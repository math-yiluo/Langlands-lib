/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedDerivedComparison
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
import WeilConjectures.AlgebraicGeometry.RestrictedComparisonGeneratorPullback
import WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionPullbackCommShift
public import WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison

/-! # Pullback naturality of raw evaluation for derived coefficients -/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The raw pullback of a morphism into an arbitrary bounded-below derived object. -/
noncomputable def rawRestrictedDerivedPullback {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (φ : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ K')
    (q : ℤ) (U : S.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} h).obj
        ((abelianComparisonFree S).obj U)) ⟶ K⟦q⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} h').obj
        ((abelianComparisonFree S).obj U)) ⟶ K'⟦q⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app
        ((abelianComparisonFree S).obj U)) ≫
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    (D+((a)^*[AddCommGrpCat.{u + 1}])).map z ≫
    ((D+((a)^*[AddCommGrpCat.{u + 1}])).commShiftIso q).hom.app K ≫
    (shiftFunctor _ q).map φ

/-- Canonical cohomology pullback, expressed through restricted derived sections. -/
@[no_expose]
noncomputable def rawRestrictedDerivedCohomologyPullback {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (φ : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ K')
    (q : ℤ) (U : S.Etale) :
    (cohomology AddCommGrpCat.{u + 1} (pullback U.hom h) q).obj
      ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom h)).mapDerivedCategory.obj K.obj) ⟶
    (cohomology AddCommGrpCat.{u + 1} (pullback U.hom h') q).obj
      ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom h')).mapDerivedCategory.obj K'.obj) :=
  (RawRestrictedComparison.derivedShiftIso h q K U).inv ≫
    (RawRestrictedComparison.restrictedSectionPullback a h h' w U).app (K⟦q⟧) ≫
    (RawRestrictedComparison.sectionsFunctor
      ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
      (((D+((a)^*[AddCommGrpCat.{u + 1}])).commShiftIso q).hom.app K ≫
        (shiftFunctor _ q).map φ) ≫
    (RawRestrictedComparison.derivedShiftIso h' q K' U).hom

/-- Characterization of the restricted cohomology pullback by its shift factors. -/
theorem rawRestrictedDerivedCohomologyPullback_eq {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (φ : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ K')
    (q : ℤ) (U : S.Etale) :
    rawRestrictedDerivedCohomologyPullback a h h' w K K' φ q U =
      (RawRestrictedComparison.derivedShiftIso h q K U).inv ≫
        (RawRestrictedComparison.restrictedSectionPullback a h h' w U).app (K⟦q⟧) ≫
        (RawRestrictedComparison.sectionsFunctor
          ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (((D+((a)^*[AddCommGrpCat.{u + 1}])).commShiftIso q).hom.app K ≫
            (shiftFunctor _ q).map φ) ≫
        (RawRestrictedComparison.derivedShiftIso h' q K' U).hom := by
  rfl

set_option maxRecDepth 2048 in
/-- Derived evaluation intertwines raw pullback and restricted cohomology pullback. -/
theorem rawRestrictedDerivedComparison_pullback {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (φ : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ K')
    (q : ℤ) (U : S.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} h).obj
        ((abelianComparisonFree S).obj U)) ⟶ K⟦q⟧) :
    rawRestrictedDerivedCohomologyPullback a h h' w K K' φ q U
        (rawRestrictedDerivedComparison h q K U z) =
      rawRestrictedDerivedComparison h' q K' U
        (rawRestrictedDerivedPullback a h h' w K K' φ q U z) := by
  classical
  let L := D+((a)^*[AddCommGrpCat.{u + 1}])
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let W' := (MorphismProperty.Over.pullback @Etale ⊤ h').obj U
  let G := (upperStar AddCommGrpCat.{u + 1} h).obj
    ((abelianComparisonFree S).obj U)
  let G' := (upperStar AddCommGrpCat.{u + 1} h').obj
    ((abelianComparisonFree S).obj U)
  let e : (upperStar AddCommGrpCat.{u + 1} a).obj G ≅ G' :=
    (upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).symm.app _
  let A := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let A' := (DerivedCategory.Plus.singleFunctor _ 0).obj G'
  let α : L.obj A ≅ A' :=
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).app G ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso e
  let T := RawRestrictedComparison.sectionsFunctor W ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
  let T' := RawRestrictedComparison.sectionsFunctor W' ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
  let τ := RawRestrictedComparison.restrictedSectionPullback a h h' w U
  let x := (RawRestrictedComparison.zeroIso W G).inv
    (RawRestrictedComparison.generator h U)
  let x' := (RawRestrictedComparison.zeroIso W' G').inv
    (RawRestrictedComparison.generator h' U)
  have hs : τ.app A ≫ T'.map α.hom =
      RawRestrictedComparison.transportZero a h h' w G G' e.hom U := by
    exact RawRestrictedComparison.restrictedSectionPullback_zero
      a h h' w G G' e.hom U
  have hx : T'.map α.hom (τ.app A x) = x' := by
    have hv := congrArg (fun m ↦ m x) hs
    change T'.map α.hom (τ.app A x) =
      RawRestrictedComparison.transportZero a h h' w G G' e.hom U x at hv
    exact hv.trans (RawRestrictedComparison.restrictedComparison_generator_pullback
      a h h' w U)
  let β := (L.commShiftIso q).hom.app K ≫ (shiftFunctor _ q).map φ
  have hn : T'.map (α.inv ≫ L.map z) x' = τ.app (K⟦q⟧) (T.map z x) := by
    rw [hx.symm, T'.map_comp]
    have hc : T'.map α.inv (T'.map α.hom (τ.app A x)) = τ.app A x := by
      have hi : T'.map α.hom ≫ T'.map α.inv = 𝟙 _ := by
        rw [← Functor.map_comp, Iso.hom_inv_id]
        exact T'.map_id _
      exact congrArg (fun m ↦ m (τ.app A x)) hi
    change T'.map (L.map z) (T'.map α.inv (T'.map α.hom (τ.app A x))) = _
    rw [hc]
    have hz := congrArg (fun m ↦ m x) (τ.naturality z)
    change τ.app (K⟦q⟧) (T.map z x) =
      T'.map (L.map z) (τ.app A x) at hz
    exact hz.symm
  have hraw : rawRestrictedDerivedPullback a h h' w K K' φ q U z =
      (α.inv ≫ L.map z) ≫ β := by
    dsimp only [rawRestrictedDerivedPullback, α, β, e, L]
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv,
      Category.assoc]
    rfl
  have heval : rawRestrictedDerivedComparison h q K U z =
      (RawRestrictedComparison.derivedShiftIso h q K U).hom (T.map z x) := by
    rfl
  have heval' : rawRestrictedDerivedComparison h' q K' U
      (rawRestrictedDerivedPullback a h h' w K K' φ q U z) =
      (RawRestrictedComparison.derivedShiftIso h' q K' U).hom
        (T'.map (rawRestrictedDerivedPullback a h h' w K K' φ q U z) x') := by
    rfl
  rw [heval, heval', hraw]
  dsimp only [rawRestrictedDerivedCohomologyPullback]
  simp only [AddCommGrpCat.comp_apply]
  have hcshift : (RawRestrictedComparison.derivedShiftIso h q K U).inv
      ((RawRestrictedComparison.derivedShiftIso h q K U).hom (T.map z x)) =
      T.map z x := by
    have hh := (RawRestrictedComparison.derivedShiftIso h q K U).hom_inv_id
    exact congrArg (fun m ↦ m (T.map z x)) hh
  rw [hcshift]
  change (RawRestrictedComparison.derivedShiftIso h' q K' U).hom
      (T'.map β (τ.app (K⟦q⟧) (T.map z x))) =
    (RawRestrictedComparison.derivedShiftIso h' q K' U).hom
      (T'.map ((α.inv ≫ L.map z) ≫ β) x')
  rw [← hn, T'.map_comp (α.inv ≫ L.map z) β]
  rfl

end AlgebraicGeometry.Etale
