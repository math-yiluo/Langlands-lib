/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison
import WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport
import WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionsSingle

/-! # The shifted single comparison for restricted derived section pullback

Source: Stacks Project, Tags 07A6 and 0D6F.
(blueprint: lem-sbc-restricted-derived-section-shift-comparison).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- On a shifted single sheaf, the constructed natural pullback is the explicitly
constructed restricted cohomology map.
Source: Stacks Project, Tags 07A6 and 0D6F; Tag 03Q8 for restriction of cohomology.
(blueprint: lem-sbc-restricted-derived-section-shift-comparison).

Proof: Commute restriction and derived global sections with the shift by p.
The derived adjunction unit and the Leray isomorphism commute with this shift,
since the adjunction is induced from the adjunction of complexes and the
Leray isomorphism is characterized by the composite right-derived unit.
After the homology shift comparison, the map is H^p of the derived unit for q,
followed by the Leray comparison and the mapDerivedCategoryFactors comparison
on the actual single complex. This is exactly rawAffineComplexPullback.
The derivedRestrictionIso comparison, on a single, is the image under Q of
the mapCochainComplexSingleFunctor comparison followed by the single image
of upperStarComp(q,r) inverse and upperStarComp(r',a). Naturality for φ
then makes its coefficient part the Q image of the single coefficient map
rawAffineRestrictedCoefficient. Substitute these identities into shiftIso
and cancel the single and shift comparisons and their inverses. The result
is rawAffineRestrictedCohomologyMap by definition. The same calculation holds
for p = 0, for an empty restricted scheme, and for a noninvertible φ. -/
theorem restrictedSectionPullback_shift {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F') (U : S.Etale) :
    (restrictedSectionPullback a h h' w U).app
        (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧) ≫
      (sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
          ((D+(upperStar AddCommGrpCat.{v + 1} a).commShiftIso (p : ℤ)).hom.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
            (shiftFunctor _ (p : ℤ)).map
              (((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app
                  F ≫ (DerivedCategory.Plus.singleFunctor _ 0).map φ)) ≫
        (shiftIso h' p F' U).hom =
      (shiftIso h p F U).hom ≫ rawAffineRestrictedCohomologyMap a h h' w p F F' φ U := by
  let L := D+(upperStar AddCommGrpCat.{v + 1} a)
  let T := Evaluation.functor
      (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h))
      (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1})
  let T' := Evaluation.functor
      (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h'))
      (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1})
  let τ : T ⟶ L ⋙ T' := Functor.whiskerLeft
      (DerivedCategory.Plus.ι ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)))
      (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft DerivedCategory.Plus.ι
        (derivedRestrictionIso a h h' w U).hom)
      (rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h'))
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let K' := (DerivedCategory.Plus.singleFunctor _ 0).obj F'
  let f : L.obj K ⟶ K' :=
    ((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map φ
  let e' := Evaluation.singleIso
    (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h'))
    (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}) F'
  have hs := restrictedDerivedSections_single a h h' w F F' φ U
  dsimp only at hs
  change τ.app K ≫ T'.map f ≫ e'.hom = _ at hs
  let e := Evaluation.singleIso
    (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h))
    (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1}) F
  have hr : (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} (p : ℤ)).map
      (τ.app K ≫ T'.map f ≫ e'.hom) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} (p : ℤ)).map e.hom ≫
        rawAffineRestrictedCohomologyMap a h h' w p F F' φ U := by
    rw [hs]
    simp only [e, rawAffineRestrictedCohomologyMap, rawAffineComplexPullback,
      derivedSectionPullback, cohomology, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, NatTrans.comp_app, Functor.comp_map,
      Functor.map_comp, Category.assoc]
  rw [restrictedDerivedSections_shiftTransport a h h' w p F F' f U]
  change (shiftIso h p F U).hom ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} (p : ℤ)).map
        (e.inv ≫ τ.app K ≫ T'.map f ≫ e'.hom) =
    (shiftIso h p F U).hom ≫ rawAffineRestrictedCohomologyMap a h h' w p F F' φ U
  rw [Functor.map_comp, hr]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry.Etale.RawRestrictedComparison
