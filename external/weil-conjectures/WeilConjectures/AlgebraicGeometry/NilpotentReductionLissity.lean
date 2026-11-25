/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientScalarEquivalence
import WeilConjectures.AlgebraicGeometry.NilpotentReductionStep

/-! # Lissity propagates through powers of a coefficient ideal

Source: Stacks Project, sites-cohomology.tex, Tag 094I, with Tag 094H
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Lissity of all cohomology sheaves after reduction modulo an ideal implies lissity
modulo every positive power, and implies lissity of the original object for a nilpotent
ideal. Source: Stacks Project, sites-cohomology.tex, Tags 094I and 094H
(auxiliary; not a blueprint node).

Proof:
1. Locally constant finite-type module sheaves form a weak Serre subcategory
(`lem-weil-pbc-locally-constant-derived-serre`). Cohomology in that subcategory is closed
under distinguished triangles (`lem-sbc-cohomology-in-weak-serre-subcategory`).
2. Put Q_n = J^n/J^(n+1). The quotient short exact sequence gives a distinguished triangle
with terms K tensor Q_n, K tensor B/J^(n+1), and K tensor B/J^n. Exact sheafification
(`lem-weil-pbc-site-module-presheaf-sheafification-exact`) and a flat K-flat resolution
(`lem-pc-kflat-resolution`, `def-pc-flat-sheaf-modules`, `def-pc-kflat-complex`) compute
this triangle. Balancing identifies its first term with (K tensor B/J) tensor_(B/J) Q_n
using `lem-pur-derived-change-of-rings`.
3. B/J is Noetherian, and Q_n is finite over B/J because J^n is finitely generated.
Good truncation followed by `lem-pc-kflat-bounded-flat-replacement` and
`lem-pc-bounded-above-flat-kflat-site` shows that K tensor B/J is bounded above.
Tag 094H (`lem-weil-pbc-locally-constant-tensor`) makes the first triangle term lisse.
Induction and Step 1 make the middle term lisse over B. Quotient each local finite module
M by J^(n+1)M; exact sheafification preserves its constant sheaf since this ideal acts
as zero. This supplies the required quotient-linear local descriptions.
4. When J^m = 0, scalar extension identifies the reduction with K. On a K-flat model,
p tensor b maps to bp with inverse p maps to p tensor 1. Thus K has the same property. -/
theorem locallyConstantFiniteTypeModules_reduction_pow
    {C : Type u} [Category.{u} C] (T : Precoverage C)
    [T.HasIsos] [T.IsStableUnderComposition] [T.IsStableUnderBaseChange] [T.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B))]
    [∀ I : Ideal B, HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck (B ⧸ I)))]
    (K : DerivedCategory
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B)))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hmod : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck (Ideal.Quotient.mk J)).obj K))) :
    (∀ m : ℕ, 1 ≤ m →
      ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J ^ m)
        ((DerivedCategory.homologyFunctor _ i).obj
          ((constantCoefficientScalarExtension T.toGrothendieck
            (Ideal.Quotient.mk (J ^ m))).obj K))) ∧
    (∀ m : ℕ, 1 ≤ m → J ^ m = ⊥ →
      ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck B
        ((DerivedCategory.homologyFunctor _ i).obj K)) := by
  let lisseReduction (I : Ideal B) : Prop :=
    ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ I)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck (Ideal.Quotient.mk I)).obj K))
  have hpow (m : ℕ) (hm : 1 ≤ m) : lisseReduction (J ^ m) := by
    induction m, hm using Nat.le_induction with
    | base =>
        rw [pow_one]
        exact hmod
    | succ n hn ih =>
        exact locallyConstantFiniteTypeModules_reduction_succ T B J K hbounded hmod n hn ih
  refine ⟨hpow, ?_⟩
  intro m hm hzero i
  apply locallyConstantFiniteTypeModules_of_scalarExtension_bijective
    T.toGrothendieck (Ideal.Quotient.mk (J ^ m)) ?_ K i (hpow m hm i)
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    have hmem : x - y ∈ J ^ m := (Ideal.Quotient.eq_zero_iff_mem).mp (by
      simpa only [map_sub, sub_eq_zero] using hxy)
    simpa only [hzero, Ideal.mem_bot] using hmem
  · exact Ideal.Quotient.mk_surjective

end SheafOfModules
