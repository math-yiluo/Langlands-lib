/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
import WeilConjectures.FieldTheory.PBasisExtension

/-!
# Existence of a p-basis

Source: Stacks Project, More on Algebra, Definition 07P1 and Lemma 07P2,
applied to the extension from the prime field (blueprint: lem-weil-pbc-p-basis-exists).

The p-basis is written inline in the form of `lem-weil-pbc-p-basis-differentials-basis`
(`KaehlerDifferential.exists_basis_differentials_of_pBasis`) with base field the prime
field `ZMod p`: `k^p = (ZMod p) k^p` is `IntermediateField.adjoin (ZMod p) (Set.range (· ^ p))`.
The prime-field algebra structure is Mathlib's `ZMod.algebra`, registered locally as in
`WeilConjectures.FieldTheory.IntersectionSubfieldsDifferentials`.
-/

@[expose] public section

universe u

attribute [local instance] ZMod.algebra

namespace Field

/-- Every field of prime characteristic has a p-basis over its subfield of p-th powers.
Source: Stacks Project, More on Algebra, Definition 07P1 and Lemma 07P2
(blueprint: lem-weil-pbc-p-basis-exists).

The subfield `k^p` is `IntermediateField.adjoin (ZMod p) (Set.range (· ^ p))` over the prime
field (it already contains the prime field, so the adjunction adds nothing), the p-basis
form of `lem-weil-pbc-p-basis-differentials-basis` for the extension `ZMod p → k`.

Proof:
1. Frobenius is a ring homomorphism, so its image is the subfield `k^p`, containing the
   prime field. A subset is p-independent when its restricted monomials are independent.
2. By `lem-weil-pbc-zorn-lemma`, choose a maximal p-independent subset `T`. The empty
   subset is independent (its sole monomial is 1). For a chain, every finite relation
   in the union has its supports in one member, so the union is independent.
3. The `k^p`-span `L` of the monomials of `T` is closed under multiplication: reduce
   exponents modulo p, absorbing p-th powers into coefficients. Each element belongs
   to a finite-dimensional subring spanned by monomials on a finite subset. Multiplication
   by a nonzero element is injective, hence surjective there, giving its inverse in `L`.
4. If `t` is outside `L`, then `t^p` lies in `L`. Use
   `lem-weil-pbc-simple-algebraic-extension-power-basis` and `def-weil-algebraic-element`.
   The minimal polynomial divides `X^p - t^p = (X - t)^p`, so it is `(X - t)^e` with
   `1 ≤ e ≤ p`. If `e < p`, its coefficient `-e*t` puts `t` in `L`, a contradiction.
   Thus `1, t, ..., t^(p-1)` are independent over `L`.
5. Group a relation among monomials of `T ∪ {t}` by the exponent of `t`. Step 4 kills
   the coefficients in `L`, and independence of `T` kills the original coefficients.
   This contradicts maximality, so `L = k`.
6. Index the family by `T`: its monomials are independent and span `k`, hence form a basis.
-/
theorem exists_p_basis (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] :
    ∃ (I : Type u) (t : I → k)
      (b : Module.Basis {E : I →₀ ℕ // ∀ i : I, E i < p}
        (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k => x ^ p))) k),
      ∀ E, b E = E.val.prod (fun i e => t i ^ e) := by
  let I := Empty
  let x : I → k := fun i => i.elim
  have hx : LinearIndependent
      (IntermediateField.adjoin (ZMod p) (Set.range (fun a : k => a ^ p)))
      (fun E : {E : I →₀ ℕ // ∀ i : I, E i < p} =>
        E.val.prod (fun i e => x i ^ e)) := by
    rw [linearIndependent_iff]
    intro l hl
    apply Finsupp.ext
    intro E
    have hE : E = ⟨0, by intro i; exact i.elim⟩ := by
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      exact i.elim
    subst hE
    let z : {E : I →₀ ℕ // ∀ i : I, E i < p} :=
      ⟨0, by intro i; exact i.elim⟩
    have hlz : l = Finsupp.single z (l z) := by
      apply Finsupp.ext
      intro E
      have hEz : E = z := by
        apply Subtype.ext
        apply Finsupp.ext
        intro i
        exact i.elim
      subst E
      simp
    rw [hlz] at hl
    simpa [Finsupp.linearCombination_single] using hl
  obtain ⟨J, y, b, hb⟩ := FieldTheory.exists_pBasis_extension (k := ZMod p) (K := k)
    (p := p) x hx
  refine ⟨Empty ⊕ J, Sum.elim (fun i : Empty => i.elim) y, ?_, ?_⟩
  · exact b
  · exact hb


end Field
