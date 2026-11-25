/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalIsomorphismSourceEvaluation
public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Localization transports pro-etale coefficient-normalization squares

All coefficient and localization comparisons
are the canonical derived mates.

## References

* Stacks Tags 03DA and 098K, pasting coefficient and localization mates
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) (B B' : Type (u + 1)) [CommRing B] [CommRing B']
/-- Restrict the comparison image of a normalization arrow to a slice and use the
canonical coefficient comparison. -/
noncomputable def sliceComparisonNormalizationArrow (φ : B →+* B')
    {A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {A' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B'))}
    (d : A ⟶ (normalizationRestrict X.smallEtaleTopology φ).obj A') (U : X.ProEt) :=
  (derivedSliceRestriction (ProEt.topology X) B U).map
    ((derivedComparison X B).map d ≫ (comparisonRestrictScalarsIso X B φ).hom.app A') ≫
      (sliceRestrictScalarsIso (ProEt.topology X) B φ U).inv.app
        ((derivedComparison X B').obj A')
end AlgebraicGeometry.Scheme

section TransportHelpers

-- Cache the existence of sheafification in the private calculations. Repeatedly
-- searching for it reconstructs the same essentially-small-site instance.
private theorem etaleWeakSheafifyCache
    (X : AlgebraicGeometry.Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} B) := inferInstance

private theorem proetWeakSheafifyCache
    (X : AlgebraicGeometry.Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} B) := inferInstance

private theorem etaleOverWeakSheafifyCache
    (X : AlgebraicGeometry.Scheme.{u}) (V : X.Etale)
    (B : Type (u + 1)) [CommRing B] :
    HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} B) := inferInstance

private theorem proetOverWeakSheafifyCache
    (X : AlgebraicGeometry.Scheme.{u}) (V : X.ProEt)
    (B : Type (u + 1)) [CommRing B] :
    HasWeakSheafify ((AlgebraicGeometry.Scheme.ProEt.topology X).over V)
      (ModuleCat.{u + 1} B) := inferInstance

attribute [local instance] etaleWeakSheafifyCache proetWeakSheafifyCache
  etaleOverWeakSheafifyCache proetOverWeakSheafifyCache

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
private theorem comparison_coefficient_mate_eq (q : R →+* S)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)) :
    (normalizationPullbackIso X.smallEtaleTopology (toProEt X) (ProEt.topology X) q).hom.app M =
      comparisonRestrictScalarsMap X R q M := by
  simp only [normalizationPullbackIso, asIso_hom, normalizationPullbackMate,
    mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, comparisonRestrictScalarsMap,
    Adjunction.homEquiv_counit]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

private theorem comparison_coefficient_derived_eq (q : R →+* S) :
    localIsomorphismComparisonCoefficients (X := X) q =
      comparisonRestrictScalarsIso X R q := by
  have h : normalizationPullbackIso X.smallEtaleTopology (toProEt X)
      (ProEt.topology X) q = comparisonRestrictScalarsSheafIso X R q := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    exact comparison_coefficient_mate_eq X q M
  unfold localIsomorphismComparisonCoefficients comparisonRestrictScalarsIso
  rw [h]

variable (U : X.ProEt)
private theorem proet_coefficient_mate_eq (q : R →+* S)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q).hom.app M =
      ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) U.hom).homEquiv _ _).symm
        ((sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) U.hom).unit.app M)) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  simp only [normalizationPullbackIso, asIso_hom, normalizationPullbackMate,
    mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Adjunction.homEquiv_counit]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

private theorem proet_localization_coefficient_mate (q : R →+* S)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q).hom.app M ≫
        (sheafCompose (ProEt.topology U.left)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((ProEtale.upperStarIsoLocalizationRestriction
            (ModuleCat.{u + 1} S) U.hom U.prop).hom.app M) =
      (ProEtale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} R) U.hom U.prop).hom.app
          ((sheafCompose (ProEt.topology X)
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  let aR := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) U.hom
  let aS := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) U.hom
  let bR := ProEtale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} R) U.hom U.prop
  let bS := ProEtale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} S) U.hom U.prop
  apply (aR.homEquiv _ _).injective
  rw [aR.homEquiv_naturality_right, proet_coefficient_mate_eq,
    Equiv.apply_symm_apply]
  change _ = aR.homEquiv _ _ ((aR.leftAdjointUniq bR).hom.app _)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have hs := Adjunction.homEquiv_leftAdjointUniq_hom_app aS bS M
  rw [Adjunction.homEquiv_unit] at hs
  change
    (sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map (aS.unit.app M) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} R) U.hom).map
        ((sheafCompose (ProEt.topology U.left)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((aS.leftAdjointUniq bS).hom.app M)) = _
  change (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
      (aS.unit.app M) ≫
    (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
      ((ProEtale.lowerStar (ModuleCat.{u + 1} S) U.hom).map
        ((aS.leftAdjointUniq bS).hom.app M)) = _
  rw [← CategoryTheory.Functor.map_comp, hs]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

private noncomputable def proetSliceEquivalenceCoefficients (U : X.ProEt) (q : R →+* S) :
    Sheaf.restrictScalars ((ProEt.topology X).over U) q ⋙
        (proetSliceEquivalence X R U).functor ≅
      (proetSliceEquivalence X S U).functor ⋙
        Sheaf.restrictScalars (ProEt.topology U.left) q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private theorem proetSliceCoefficients_pasting (U : X.ProEt) (q : R →+* S)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q).hom.app M ≫
      (Sheaf.restrictScalars (ProEt.topology U.left) q).map
        ((proetSliceRestrictionIso X S U).inv.app M) =
    (proetSliceRestrictionIso X R U).inv.app
      ((Sheaf.restrictScalars (ProEt.topology X) q).obj M) ≫
      (proetSliceEquivalence X R U).functor.map
        ((sliceRestrictScalarsSheafIso (ProEt.topology X) R q U).inv.app M) ≫
      (proetSliceEquivalenceCoefficients X U q).hom.app
        (((ProEt.topology X).overPullback (ModuleCat.{u + 1} S) U).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  have h := proet_localization_coefficient_mate X U q M
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  have hh := congrArg (fun k ↦ k.hom.app V) h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun k ↦ k x) hh

private noncomputable def proetDerivedSliceEquivalenceCoefficients (U : X.ProEt) (q : R →+* S) :
    Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) q ⋙
        (proetSliceEquivalence X R U).functor.mapDerivedCategory ≅
      (proetSliceEquivalence X S U).functor.mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (ProEt.topology U.left) q :=
  Functor.mapDerivedCategorySquareIso (proetSliceEquivalenceCoefficients X U q)

private theorem proetDerivedSliceCoefficients_pasting (U : X.ProEt) (q : R →+* S)
    (M : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S))) :
    (localIsomorphismProEtaleCoefficients U.hom q).hom.app M ≫
      (normalizationRestrict (ProEt.topology U.left) q).map
        ((proetDerivedSliceRestrictionIso X S U).inv.app M) =
    (proetDerivedSliceRestrictionIso X R U).inv.app
      ((normalizationRestrict (ProEt.topology X) q).obj M) ≫
      (proetSliceEquivalence X R U).functor.mapDerivedCategory.map
        ((sliceRestrictScalarsIso (ProEt.topology X) R q U).inv.app M) ≫
      (proetDerivedSliceEquivalenceCoefficients X U q).hom.app
        ((derivedSliceRestriction (ProEt.topology X) S U).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  let : (Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback
      @AlgebraicGeometry.WeaklyEtale ⊤ U.hom) (ModuleCat.{u + 1} S)
      (ProEt.topology X) (ProEt.topology U.left)).Additive := by
    change (ProEtale.upperStar (ModuleCat.{u + 1} S) U.hom).Additive
    infer_instance
  let : (Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback
      @AlgebraicGeometry.WeaklyEtale ⊤ U.hom) (ModuleCat.{u + 1} R)
      (ProEt.topology X) (ProEt.topology U.left)).Additive := by
    change (ProEtale.upperStar (ModuleCat.{u + 1} R) U.hom).Additive
    infer_instance
  let : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} R) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteLimits (ProEtale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  let : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} R) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteColimits (ProEtale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  let : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} S) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteLimits (ProEtale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  let : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} S) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteColimits (ProEtale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (sliceRestrictScalarsSheafIso (ProEt.topology X) R q U).symm
    (proetSliceEquivalenceCoefficients X U q)
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q)
    (proetSliceRestrictionIso X R U).symm
    (proetSliceRestrictionIso X S U).symm
    (proetSliceCoefficients_pasting X U q) M
  simp only [localIsomorphismProEtaleCoefficients, proetDerivedSliceRestrictionIso,
    proetDerivedSliceEquivalenceCoefficients, sliceRestrictScalarsIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc] at h ⊢
  convert! h using 1

end AlgebraicGeometry.Scheme

namespace CategoryTheory
section TransportSquare
variable {H S P Q : Type*} [Category H] [Category S] [Category P] [Category Q]
    (ER : H ⥤ P) (ES : S ⥤ Q) (RS : S ⥤ H) (RP : Q ⥤ P)
    (c : RS ⋙ ER ≅ ES ⋙ RP)
    {A D : H} {A' D' : S} {A₀ D₀ : P} {A₁ D₁ : Q}
    (δA : ER.obj A ≅ A₀) (δD : ER.obj D ≅ D₀)
    (εA : ES.obj A' ≅ A₁) (εD : ES.obj D' ≅ D₁)
    (dA : A ⟶ RS.obj A') (dD : D ⟶ RS.obj D')
    (dA₀ : A₀ ⟶ RP.obj A₁) (dD₀ : D₀ ⟶ RP.obj D₁)
    (hA : δA.hom ≫ dA₀ = ER.map dA ≫ c.hom.app A' ≫ RP.map εA.hom)
    (hD : δD.hom ≫ dD₀ = ER.map dD ≫ c.hom.app D' ≫ RP.map εD.hom)
include hA hD in
private theorem normalized_square_transport
    (e : A ≅ D) (e' : A' ≅ D')
    (he : e.hom ≫ dD = dA ≫ RS.map e'.hom) :
    (δA.symm ≪≫ ER.mapIso e ≪≫ δD).hom ≫ dD₀ =
      dA₀ ≫ RP.map (εA.symm ≪≫ ES.mapIso e' ≪≫ εD).hom := by
  apply (cancel_epi δA.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  rw [hD, reassoc_of% hA]
  simp only [← RP.map_comp_assoc, Iso.hom_inv_id_assoc]
  rw [← ER.map_comp_assoc, he, ER.map_comp, Category.assoc]
  have hn := c.hom.naturality e'.hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

end TransportSquare
end CategoryTheory

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
private theorem source_slice_normalization (U : X.ProEt) (q : R →+* S)
    {A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))}
    {A' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))}
    (d : A ⟶ (normalizationRestrict X.smallEtaleTopology q).obj A') :
    (proetDerivedSliceRestrictionIso X R U).hom.app ((derivedComparison X R).obj A) ≫
      localProEtaleNormalization U.hom q d =
    (proetSliceEquivalence X R U).functor.mapDerivedCategory.map
      (sliceComparisonNormalizationArrow X R S q d U) ≫
      (proetDerivedSliceEquivalenceCoefficients X U q).hom.app
        ((derivedSliceRestriction (ProEt.topology X) S U).obj
          ((derivedComparison X S).obj A')) ≫
      (normalizationRestrict (ProEt.topology U.left) q).map
        ((proetDerivedSliceRestrictionIso X S U).hom.app ((derivedComparison X S).obj A')) := by
  have hp := proetDerivedSliceCoefficients_pasting X U q ((derivedComparison X S).obj A')
  have hn := (proetDerivedSliceRestrictionIso X R U).hom.naturality
    ((derivedComparison X R).map d ≫
      (comparisonRestrictScalarsIso X R q).hom.app A')
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [localProEtaleNormalization, localProEtaleComparisonCoefficients,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id, localProEtaleComparison, Functor.comp_map,
    Category.assoc, comparison_coefficient_derived_eq] at *
  rw [← CategoryTheory.Functor.map_comp_assoc]
  erw [← reassoc_of% hn]
  apply (cancel_mono ((normalizationRestrict (ProEt.topology U.left) q).map
    ((proetDerivedSliceRestrictionIso X S U).inv.app ((derivedComparison X S).obj A')))).mp
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [hp]
  simp only [sliceComparisonNormalizationArrow, CategoryTheory.Functor.map_comp,
    Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id, CategoryTheory.Functor.map_comp]
end AlgebraicGeometry.Scheme
end TransportHelpers

namespace AlgebraicGeometry.Scheme

/-- A coefficient-normalization square on the pro-etale slice transports to the
source scheme. -/
theorem sourceSliceNormalization_transport
    (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)))
    (dA : A ⟶ (normalizationRestrict X.smallEtaleTopology q).obj A')
    (dD : D ⟶ (normalizationRestrict X.smallEtaleTopology q).obj D') (U : X.ProEt)
    (e : (derivedSliceRestriction (ProEt.topology X) R U).obj
        ((derivedComparison X R).obj A) ≅
      (derivedSliceRestriction (ProEt.topology X) R U).obj ((derivedComparison X R).obj D))
    (e' : (derivedSliceRestriction (ProEt.topology X) S U).obj
        ((derivedComparison X S).obj A') ≅
      (derivedSliceRestriction (ProEt.topology X) S U).obj ((derivedComparison X S).obj D'))
    (h : e.hom ≫ sliceComparisonNormalizationArrow X R S q dD U =
      sliceComparisonNormalizationArrow X R S q dA U ≫
        (normalizationRestrict ((ProEt.topology X).over U) q).map e'.hom) :
    (((proetDerivedSliceRestrictionIso X R U).app ((derivedComparison X R).obj A)).symm ≪≫
      (proetSliceEquivalence X R U).functor.mapDerivedCategory.mapIso e ≪≫
      (proetDerivedSliceRestrictionIso X R U).app ((derivedComparison X R).obj D)).hom ≫
        localProEtaleNormalization U.hom q dD =
      localProEtaleNormalization U.hom q dA ≫
        (normalizationRestrict (ProEt.topology U.left) q).map
          (((proetDerivedSliceRestrictionIso X S U).app
              ((derivedComparison X S).obj A')).symm ≪≫
            (proetSliceEquivalence X S U).functor.mapDerivedCategory.mapIso e' ≪≫
            (proetDerivedSliceRestrictionIso X S U).app ((derivedComparison X S).obj D')).hom := by
  exact CategoryTheory.normalized_square_transport
    (proetSliceEquivalence X R U).functor.mapDerivedCategory
    (proetSliceEquivalence X S U).functor.mapDerivedCategory
    (normalizationRestrict ((ProEt.topology X).over U) q)
    (normalizationRestrict (ProEt.topology U.left) q)
    (proetDerivedSliceEquivalenceCoefficients X U q)
    ((proetDerivedSliceRestrictionIso X R U).app ((derivedComparison X R).obj A))
    ((proetDerivedSliceRestrictionIso X R U).app ((derivedComparison X R).obj D))
    ((proetDerivedSliceRestrictionIso X S U).app ((derivedComparison X S).obj A'))
    ((proetDerivedSliceRestrictionIso X S U).app ((derivedComparison X S).obj D'))
    (sliceComparisonNormalizationArrow X R S q dA U)
    (sliceComparisonNormalizationArrow X R S q dD U)
    (localProEtaleNormalization U.hom q dA) (localProEtaleNormalization U.hom q dD)
    (source_slice_normalization X U q dA) (source_slice_normalization X U q dD) e e' h

end AlgebraicGeometry.Scheme
