/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram
public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
import WeilConjectures.AlgebraicGeometry.RawModuleRestrictedAbelianNonnegative
import WeilConjectures.AlgebraicGeometry.RawModuleRestrictedAbelianNegative

/-! # Raw module Hom and restricted abelian cohomology

Source: Stacks Project, Tags 03FD, 03Q8 and 09Z1.
(blueprint: lem-sbc-raw-module-restricted-abelian-natural-iso).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The scalar-forgetting comparison is natural for the fixed five-factor pullback.
There are no limit, qcqs, affineness, or indexing assumptions in this comparison.
Source: Stacks Project, Tag 03FD, lemma-cohomology-modules-abelian; Tag 03Q8,
restriction to an etale object; Tag 09Z1, canonical maps in lemma-relative-colimit.
(blueprint: lem-sbc-raw-module-restricted-abelian-natural-iso).

Proof: For each A, resolve A.hom^*G by injective module sheaves. The free module
sheaf/sections adjunction on U identifies the raw derived-Hom complex with sections
on U times_S A. Restriction to this etale object preserves injectives: its left
adjoint, extension by zero, is exact. After forgetting scalars the resolution
computes abelian sections cohomology, because injective module sheaves are acyclic
on every etale object by 03FD; the section complexes and their differentials
are unchanged. Forgetting scalars commutes with inverse image, so its coefficient
sheaf is the pullback of the underlying abelian G. The fully faithful inclusion
of the bounded-below derived category into the derived category and its single
and shift comparisons identify these complexes with restrictedOverCohomology.
All comparisons preserve addition, giving isomorphisms in AddCommGrpCat. For f,
expand the sections adjunction unit and the two pullback-composition comparisons.
Naturality of the unit moves a class through f^*, and the adjunction triangle
identity cancels the counit. The source comparison is the first factor of the
raw pullback, the single-complex comparison is its second, the map on the class
is its third, shift compatibility is its fourth, and the canonical coefficient
identification is its fifth. On the restricted scheme side these are exactly
rawAffineComplexPullback and rawAffineRestrictedCoefficient. Thus the displayed
square holds for every f. For negative q both groups vanish, and the unique
isomorphism has the same naturality. This comparison uses no continuity theorem
and makes no assertion about a cohomology colimit. -/
theorem exists_rawModule_restrictedAbelian_natural_iso
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale) :
    ∃ e : ∀ A : Over W,
      (higherDirectImageRawOverFunctor Λ k G q U).obj (op A) ≅
        restrictedOverCohomology k
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
          q A U,
      ∀ (A B : Over W) (f : A ⟶ B),
        (higherDirectImageRawOverFunctor Λ k G q U).map f.op ≫ (e A).hom =
          (e B).hom ≫ restrictedOverCohomologyMap k
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
            q f U := by
  classical
  by_cases hq : 0 ≤ q
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact exists_rawModule_restrictedAbelian_nonnegative Λ k G p U
  · exact exists_rawModule_restrictedAbelian_negative Λ k G q U (lt_of_not_ge hq)

end AlgebraicGeometry.Etale
