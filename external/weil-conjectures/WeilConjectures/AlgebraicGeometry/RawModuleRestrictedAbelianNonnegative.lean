/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram
public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomComparison
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyNaturalIso
@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
/-- The nonnegative-degree scalar-forgetting comparison is natural for the fixed
five-factor pullback, with no affineness, qcqs, or limit hypotheses.
Source: Stacks Project, Tags 03FD, 03Q8 and 09Z1.
(blueprint: lem-sbc-raw-module-restricted-abelian-nonnegative).

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
square holds for every f. This comparison uses no continuity theorem
and makes no assertion about a cohomology colimit. In degree zero the sections
adjunction is the ordinary sections comparison; on an empty test object both
section complexes are zero. -/
theorem exists_rawModule_restrictedAbelian_nonnegative
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale) :
    ∃ e : ∀ A : Over W,
      (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op A) ≅
        restrictedOverCohomology k
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
          (q : ℤ) A U,
      ∀ (A B : Over W) (f : A ⟶ B),
        (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op ≫ (e A).hom =
          (e B).hom ≫ restrictedOverCohomologyMap k
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
            (q : ℤ) f U := by
  obtain ⟨e, he⟩ := exists_rawModule_abelianHom_comparison Λ k G q U
  obtain ⟨r, hr⟩ := exists_raw_restricted_cohomology_natural_iso S q U
  let F := (sheafCompose _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
  refine ⟨fun A ↦ e A ≪≫ r (A.hom ≫ k) (restrictedOverCoefficient F A), ?_⟩
  intro A B f
  apply AddCommGrpCat.ext
  intro z
  change (r (A.hom ≫ k) (restrictedOverCoefficient F A)).hom
      ((e A).hom ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z)) =
    restrictedOverCohomologyMap k F (q : ℤ) f U
      ((r (B.hom ≫ k) (restrictedOverCoefficient F B)).hom ((e B).hom z))
  rw [he]
  exact (hr f.left (B.hom ≫ k) (A.hom ≫ k)
    (by rw [← Category.assoc, Over.w])
    (restrictedOverCoefficient F B) (restrictedOverCoefficient F A)
    ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
      (Over.w f).symm).inv.app F) ((e B).hom z)).symm
end AlgebraicGeometry.Etale
