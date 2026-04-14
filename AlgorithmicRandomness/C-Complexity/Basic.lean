/-
Author: William Dan
-/

import Mathlib.Computability.PartrecCode
import Mathlib.Data.ENat.Lattice

import AlgorithmicRandomness.UniversalMachines.Basic

/-
# C-Complexity

C-complexity (or plain Kolmogorov complexity) can be thought of as a measure of how compressible a
finite string is. Relative to a p.c. function (procedure) f, the C-complexity of σ is just the
shortest input (description) τ so that f(τ) = σ. We think of being able to compress σ to τ and just
applying f to get back σ, so short τ means highly compressible σ.

Of course, the specific f affects the complexity a lot. To abstract this out, we usually consider
C-complexity to be relative to a fixed universal machine. Then, the compressibility of σ is the
shortest combination of procedure ρ and input τ so that U(ρτ) = σ.

This file defines C-complexity relative to f, and then the just C-complexity (relative to fixedU).
Afterwards, it proves some basic theorems concerning C-complexity.

## Main definitions and results

- C_complexity : definition of C-complexity
- C_complexity_ubound : theorem giving the upper bound C(σ) ≤ |σ| + O(1) (Prop 3.1.1 (i))
- C_complexity_of_computable : theorem giving the identity C(f(σ)) ≤ C(σ) + O(1) for any p.c. f
    (Prop 3.1.1 (iii))

## References

Downey, R. and Hirschfeldt, D. Algorithmic Randomness and Complexity.
-/

open UniversalMachines

namespace C_Complexity

def descriptionLengths (f : List Bool → Part (List Bool)) (σ : List Bool) : Set (ℕ) :=
  {n : ℕ | ∃ τ : List Bool, f τ = σ ∧ n = τ.length}

noncomputable def C_complexity_f (f : List Bool → Part (List Bool)) (σ : List Bool) : ℕ∞ :=
  sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' (descriptionLengths f σ))

lemma descriptionLengths_fixedU_nonempty (σ : List Bool) :
    (descriptionLengths fixedU σ).Nonempty := by
  let f : List Bool → List Bool := fun _ ↦ σ
  have hf : Computable f := Computable.const σ
  obtain ⟨ρ, hρ⟩ := fixedU_universal hf
  use ρ.length
  unfold descriptionLengths
  rw [Part.coe_some, Set.mem_setOf_eq]
  use ρ
  constructor
  · have hempty := hρ []
    unfold f at hempty
    rw [List.append_nil, PFun.coe_val] at hempty
    exact hempty
  · rfl

/- Though C-complexity relative to an arbitrary p.c. f can sometimes be infinite, since f may not
  produce a certain string, the usual C-complexity cannot. -/
lemma C_complexity_fin (σ : List Bool) : C_complexity_f fixedU σ < ⊤ := by
  have hmem : ∃ n : ℕ, (n : ℕ∞) ∈ ((fun n ↦ ↑n) '' descriptionLengths fixedU σ) := by
    obtain ⟨n, hn⟩ := descriptionLengths_fixedU_nonempty σ
    use n
    apply Set.mem_image_of_mem
    exact hn
  obtain ⟨n, hn⟩ := hmem
  unfold C_complexity_f
  exact lt_of_le_of_lt (sInf_le hn) (ENat.coe_lt_top n)

noncomputable def C_complexity (σ : List Bool) : ℕ :=
  (C_complexity_f fixedU σ).lift (C_complexity_fin σ)

-- Helper lemma to simplify the Lean mechanics used to show C-complexity will never be infinite.
lemma C_complexity_eq_sInf (σ : List Bool) :
    C_complexity σ = sInf (descriptionLengths fixedU σ) := by
  unfold C_complexity C_complexity_f
  apply ENat.coe_inj.mp
  rw [ENat.coe_lift]
  apply le_antisymm
  · apply sInf_le
    apply Set.mem_image_of_mem
    exact Nat.sInf_mem (descriptionLengths_fixedU_nonempty σ)
  · apply le_sInf
    intro b hb
    obtain ⟨x, hx₁, hx₂⟩ := hb
    change ↑x = b at hx₂
    rw [← hx₂, Nat.cast_le]
    exact csInf_le' hx₁

theorem C_complexity_ubound : ∃ A : ℕ, ∀ σ : List Bool, C_complexity σ ≤ σ.length + A := by
  obtain ⟨ρ, hρ⟩ := fixedU_universal Computable.id
  use ρ.length
  intro σ
  rw [C_complexity_eq_sInf]
  apply csInf_le'
  unfold descriptionLengths
  rw [Set.mem_setOf_eq]
  use ρ ++ σ
  constructor
  · have hσ := hρ σ
    rw [PFun.coe_val, id_eq] at hσ
    exact hσ
  · rw [List.length_append, add_comm]

theorem C_complexity_of_computable {f : List Bool → List Bool} (hf : Computable f) :
    ∃ A : ℕ, ∀ σ : List Bool, C_complexity (f σ) ≤ C_complexity σ + A := by
  obtain ⟨ρ, hρ⟩ := fixedU_universal (fixedU_partcomp.map ((hf.comp Computable.snd).to₂))
  change ∀ (σ : List Bool), fixedU (ρ ++ σ) = Part.map f (fixedU σ) at hρ
  use ρ.length
  intro σ
  rw [C_complexity_eq_sInf]
  apply csInf_le'
  unfold descriptionLengths
  rw [Part.coe_some, Set.mem_setOf_eq]
  have hsInf := Nat.sInf_mem (descriptionLengths_fixedU_nonempty σ)
  nth_rw 1 [descriptionLengths] at hsInf
  rw [Set.mem_setOf_eq] at hsInf
  obtain ⟨τ, hτ₁, hτ₂⟩ := hsInf
  rw [← C_complexity_eq_sInf] at hτ₂
  use (ρ ++ τ)
  constructor
  · rw [hρ τ, hτ₁, Part.coe_some, Part.map_some]
  · rw [hτ₂, List.length_append, add_comm]

end C_Complexity
