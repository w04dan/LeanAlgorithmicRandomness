/-
Author: William Dan
-/

import Mathlib.Computability.PartrecCode
import Mathlib.Data.ENat.Lattice

/-
# Universal Machines

Certain partial computable (p.c.) functions are called universal, since they are universal in the
sense that they can simulate all other p.c. functions. The exact sense in which they do that varies,
as there exist a number of non-equivalent definitions that authors refer to as universal.

For this project, we follow our reference and say that a p.c. function U is universal if, for any
p.c. function f, there exists a string ρ_f so that ∀σ U(ρ_fσ)=f(σ) (more broadly this might be
called universal by adjunction).

There are many universal p.c. functions, so it is common to fix one. This file does that, and proves
it is in fact universal and p.c.

## Main definitions and results

- fixedU : definition of the fixed universal p.c. function we will refer to throughout this project
- fixedU_universal : theorem saying fixedU is universal
- fixedU_partcomp : theorem saying fixedU is p.c.

## References

Downey, R. and Hirschfeldt, D. Algorithmic Randomness and Complexity.
-/

namespace UniversalMachines

-- Given a binary string, returns the number of 0s before the first 1; fails if no 1 is found.
def countLeadingZeroes (σ : List Bool) : Option ℕ :=
  match σ with
  | [] => none
  | false :: σ' => (countLeadingZeroes σ').map (· + 1)
  | true :: _ => some 0

-- Proves countLeadingZeroes(0^n1σ) = n.
lemma countLeadingZeroesCorrect (n : ℕ) (σ : List Bool) :
    countLeadingZeroes (List.replicate n false ++ [true] ++ σ) = some n := by
  induction n with
  | zero =>
      rw [List.replicate_zero, ← List.append_cons, List.nil_append, countLeadingZeroes]
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, List.cons_append]
      rw [countLeadingZeroes, ih, Option.map]

-- Proves dropReplicate (0^n1σ, n+1) = σ.
lemma dropReplicate (n : ℕ) (σ : List Bool) :
    (List.replicate n false ++ [true] ++ σ).drop (n+1) = σ := by
  induction n with
  | zero =>
      rw [List.replicate_zero, ← List.append_cons, List.nil_append, List.drop, List.drop]
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, List.cons_append]
      rw [List.drop_succ_cons, ih]

/- The fixed, universal p.c. function. On $σ=0^n1σ'$, runs the n-th p.c. function on σ', so that if
  f is the n-th p.c. function, ρ_f = 0^n1. -/
def fixedU (σ : List Bool) : Part (List Bool) := do
  let n ← countLeadingZeroes σ
  let c := Nat.Partrec.Code.ofNatCode n
  let r ← c.eval (Encodable.encode (σ.drop (n+1)))
  Part.ofOption (Encodable.decode (α := List Bool) r)

theorem fixedU_universal {f : List Bool → Part (List Bool)} (hf : Partrec f) :
    ∃ ρ : List Bool, ∀ σ : List Bool, fixedU (ρ ++ σ) = f σ := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  use List.replicate (Encodable.encode c) false ++ [true]
  intro σ
  unfold fixedU
  rw [countLeadingZeroesCorrect]
  simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  rw [dropReplicate, ← Nat.Partrec.Code.ofNatCode_eq, Denumerable.ofNat_encode, hc]
  simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.bind_map, Part.bind_some_right]

theorem fixedU_partcomp : Partrec fixedU := by
  sorry

end UniversalMachines
