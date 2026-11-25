/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalIsomorphismSourceEvaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.Derived.DerivedHomRestrictionEvaluation
import WeilConjectures.AlgebraicGeometry.Derived.DerivedHomEvaluationFunctoriality
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleNormalizationSquareTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Evaluation of a specified normalized Isom presheaf map

Source: Stacks Project, Tags 09BV and 0F63; functoriality of comparison and evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Pull a coefficient-normalization arrow to an etale object, using the canonical mate.
Source: Stacks Tags 03DA and 03ED.
(blueprint: def-weil-pbc-etale-isomorphism-normalization-arrow). -/
def etaleIsomorphismNormalizationArrow (Y : Scheme.{t})
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    {C : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} R))}
    {D : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} S))}
    (d : C ⟶ (normalizationRestrict Y.smallEtaleTopology q).obj D) (U : Y.Etale) :
    (localIsomorphismRestriction Y R U).obj C ⟶
      (normalizationRestrict U.left.smallEtaleTopology q).obj
        ((localIsomorphismRestriction Y S U).obj D) := by
  letI : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      Y.smallEtaleTopology U.left.smallEtaleTopology := by
    exact AlgebraicGeometry.Etale.isContinuous_overPullback U.hom
  letI : (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology U.left.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{t + 1} R) U.hom).Additive
    infer_instance
  letI : (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology U.left.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{t + 1} S) U.hom).Additive
    infer_instance
  letI : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{t + 1} R) U.hom)
    infer_instance
  letI : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{t + 1} R) U.hom)
    infer_instance
  letI : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{t + 1} S) U.hom)
    infer_instance
  letI : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{t + 1} S) U.hom)
    infer_instance
  exact (localIsomorphismRestriction Y R U).map d ≫
    (Functor.mapDerivedCategorySquareIso
      (normalizationPullbackIso Y.smallEtaleTopology
        (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
        U.left.smallEtaleTopology q)).hom.app D

end AlgebraicGeometry.Scheme
universe u
section EvaluationHelpers

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
private theorem normalized_square_reflect [ER.Faithful]
    (e : A ≅ D) (e' : A' ≅ D')
    (he : (δA.symm ≪≫ ER.mapIso e ≪≫ δD).hom ≫ dD₀ =
      dA₀ ≫ RP.map (εA.symm ≪≫ ES.mapIso e' ≪≫ εD).hom) :
    e.hom ≫ dD = dA ≫ RS.map e'.hom := by
  apply ER.map_injective
  apply (cancel_mono (c.hom.app D' ≫ RP.map εD.hom)).mp
  have h := congrArg (fun k ↦ δA.hom ≫ k) he
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp] at h
  rw [hD, reassoc_of% hA] at h
  simp only [← RP.map_comp_assoc, Iso.hom_inv_id_assoc] at h
  have hn := c.hom.naturality e'.hom
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn] at h
  simpa only [Functor.map_comp, Category.assoc] using h

end TransportSquare
end CategoryTheory

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
private def etaleNormalizationCoefficients (X : Scheme.{u}) (U : X.Etale)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    normalizationRestrict X.smallEtaleTopology q ⋙ localIsomorphismRestriction X R U ≅
      localIsomorphismRestriction X S U ⋙ normalizationRestrict U.left.smallEtaleTopology q := by
  letI : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      X.smallEtaleTopology U.left.smallEtaleTopology := by
    exact AlgebraicGeometry.Etale.isContinuous_overPullback U.hom
  letI : (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} R) X.smallEtaleTopology U.left.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{u + 1} R) U.hom).Additive
    infer_instance
  letI : (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} S) X.smallEtaleTopology U.left.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{u + 1} S) U.hom).Additive
    infer_instance
  letI : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} R) X.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  letI : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} R) X.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  letI : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} S) X.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  letI : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} S) X.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  exact Functor.mapDerivedCategorySquareIso
    (normalizationPullbackIso X.smallEtaleTopology
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      U.left.smallEtaleTopology q)

variable (U : X.Etale)

private theorem etale_coefficient_mate_eq (q : R →+* S)
    (M : Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      (X.smallEtaleTopology) (U.left.smallEtaleTopology) := Etale.isContinuous_overPullback U.hom
    (normalizationPullbackIso (X.smallEtaleTopology)
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (U.left.smallEtaleTopology) q).hom.app M =
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) U.hom).homEquiv _ _).symm
        ((sheafCompose X.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) U.hom).unit.app M)) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      (X.smallEtaleTopology) (U.left.smallEtaleTopology) := Etale.isContinuous_overPullback U.hom
  simp only [normalizationPullbackIso, asIso_hom, normalizationPullbackMate,
    mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Adjunction.homEquiv_counit]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

private theorem etale_localization_coefficient_mate (q : R →+* S)
    (M : Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      (X.smallEtaleTopology) (U.left.smallEtaleTopology) := Etale.isContinuous_overPullback U.hom
    (normalizationPullbackIso (X.smallEtaleTopology)
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (U.left.smallEtaleTopology) q).hom.app M ≫
        (sheafCompose (U.left.smallEtaleTopology)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((Etale.upperStarIsoLocalizationRestriction
            (ModuleCat.{u + 1} S) U.hom U.prop).hom.app M) =
      (Etale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} R) U.hom U.prop).hom.app
          ((sheafCompose (X.smallEtaleTopology)
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      (X.smallEtaleTopology) (U.left.smallEtaleTopology) := Etale.isContinuous_overPullback U.hom
  let aR := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) U.hom
  let aS := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) U.hom
  let bR := Etale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} R) U.hom U.prop
  let bS := Etale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} S) U.hom U.prop
  apply (aR.homEquiv _ _).injective
  rw [aR.homEquiv_naturality_right, etale_coefficient_mate_eq,
    Equiv.apply_symm_apply]
  change _ = aR.homEquiv _ _ ((aR.leftAdjointUniq bR).hom.app _)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have hs := Adjunction.homEquiv_leftAdjointUniq_hom_app aS bS M
  rw [Adjunction.homEquiv_unit] at hs
  change
    (sheafCompose (X.smallEtaleTopology)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map (aS.unit.app M) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} R) U.hom).map
        ((sheafCompose (U.left.smallEtaleTopology)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((aS.leftAdjointUniq bS).hom.app M)) = _
  change (sheafCompose X.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
      (aS.unit.app M) ≫
    (sheafCompose (X.smallEtaleTopology) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
      ((Etale.lowerStar (ModuleCat.{u + 1} S) U.hom).map
        ((aS.leftAdjointUniq bS).hom.app M)) = _
  rw [← CategoryTheory.Functor.map_comp, hs]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  rfl

private noncomputable def etaleSliceEquivalenceCoefficients (U : X.Etale) (q : R →+* S) :
    Sheaf.restrictScalars ((X.smallEtaleTopology).over U) q ⋙
        (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor ≅
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} S)).functor ⋙
        Sheaf.restrictScalars (U.left.smallEtaleTopology) q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private theorem etaleSliceCoefficients_pasting (U : X.Etale) (q : R →+* S)
    (M : Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      (X.smallEtaleTopology) (U.left.smallEtaleTopology) := Etale.isContinuous_overPullback U.hom
    (normalizationPullbackIso (X.smallEtaleTopology)
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (U.left.smallEtaleTopology) q).hom.app M ≫
      (Sheaf.restrictScalars (U.left.smallEtaleTopology) q).map
        ((etaleSliceRestrictionIso X S U).inv.app M) =
    (etaleSliceRestrictionIso X R U).inv.app
      ((Sheaf.restrictScalars (X.smallEtaleTopology) q).obj M) ≫
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor.map
        ((sliceRestrictScalarsSheafIso (X.smallEtaleTopology) R q U).inv.app M) ≫
      (etaleSliceEquivalenceCoefficients X U q).hom.app
        (((X.smallEtaleTopology).overPullback (ModuleCat.{u + 1} S) U).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      (X.smallEtaleTopology) (U.left.smallEtaleTopology) := Etale.isContinuous_overPullback U.hom
  have h := etale_localization_coefficient_mate X U q M
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  have hh := congrArg (fun k ↦ k.hom.app V) h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun k ↦ k x) hh

private noncomputable def etaleDerivedSliceEquivalenceCoefficients (U : X.Etale) (q : R →+* S) :
    Sheaf.derivedRestrictScalars ((X.smallEtaleTopology).over U) q ⋙
        (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor.mapDerivedCategory ≅
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} S)).functor.mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (U.left.smallEtaleTopology) q :=
  Functor.mapDerivedCategorySquareIso (etaleSliceEquivalenceCoefficients X U q)

private theorem etaleDerivedSliceCoefficients_pasting (U : X.Etale) (q : R →+* S)
    (M : DerivedCategory (Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} S))) :
    (etaleNormalizationCoefficients X U q).hom.app M ≫
      (normalizationRestrict (U.left.smallEtaleTopology) q).map
        ((etaleDerivedSliceRestrictionIso X S U).inv.app M) =
    (etaleDerivedSliceRestrictionIso X R U).inv.app
      ((normalizationRestrict (X.smallEtaleTopology) q).obj M) ≫
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor.mapDerivedCategory.map
        ((sliceRestrictScalarsIso (X.smallEtaleTopology) R q U).inv.app M) ≫
      (etaleDerivedSliceEquivalenceCoefficients X U q).hom.app
        ((derivedSliceRestriction (X.smallEtaleTopology) S U).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      (X.smallEtaleTopology) (U.left.smallEtaleTopology) := Etale.isContinuous_overPullback U.hom
  let : (Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback
      @AlgebraicGeometry.Etale ⊤ U.hom) (ModuleCat.{u + 1} S)
      (X.smallEtaleTopology) (U.left.smallEtaleTopology)).Additive := by
    change (Etale.upperStar (ModuleCat.{u + 1} S) U.hom).Additive
    infer_instance
  let : (Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback
      @AlgebraicGeometry.Etale ⊤ U.hom) (ModuleCat.{u + 1} R)
      (X.smallEtaleTopology) (U.left.smallEtaleTopology)).Additive := by
    change (Etale.upperStar (ModuleCat.{u + 1} R) U.hom).Additive
    infer_instance
  let : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} R) (X.smallEtaleTopology) (U.left.smallEtaleTopology)) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  let : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} R) (X.smallEtaleTopology) (U.left.smallEtaleTopology)) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  let : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} S) (X.smallEtaleTopology) (U.left.smallEtaleTopology)) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  let : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} S) (X.smallEtaleTopology) (U.left.smallEtaleTopology)) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (sliceRestrictScalarsSheafIso (X.smallEtaleTopology) R q U).symm
    (etaleSliceEquivalenceCoefficients X U q)
    (normalizationPullbackIso (X.smallEtaleTopology)
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (U.left.smallEtaleTopology) q)
    (etaleSliceRestrictionIso X R U).symm
    (etaleSliceRestrictionIso X S U).symm
    (etaleSliceCoefficients_pasting X U q) M
  simp only [etaleNormalizationCoefficients, etaleDerivedSliceRestrictionIso,
    etaleDerivedSliceEquivalenceCoefficients, etaleDerivedSliceEquivalence_functor,
    sliceRestrictScalarsIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc] at h ⊢
  convert! h using 1

end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

private theorem etale_source_slice_normalization
    (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (V : X.Etale) (q : R →+* S)
    {A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))}
    {A' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))}
    (d : A ⟶ (normalizationRestrict X.smallEtaleTopology q).obj A') :
    (etaleDerivedSliceRestrictionIso X R V).hom.app A ≫
      etaleIsomorphismNormalizationArrow X q d V =
    (etaleDerivedSliceEquivalence X R V).functor.map
      ((derivedSliceRestriction X.smallEtaleTopology R V).map d ≫
        (sliceRestrictScalarsIso X.smallEtaleTopology R q V).inv.app A') ≫
      (etaleDerivedSliceEquivalenceCoefficients X V q).hom.app
        ((derivedSliceRestriction X.smallEtaleTopology S V).obj A') ≫
      (normalizationRestrict V.left.smallEtaleTopology q).map
        ((etaleDerivedSliceRestrictionIso X S V).hom.app A') := by
  have hp := etaleDerivedSliceCoefficients_pasting X V q A'
  have hn := (etaleDerivedSliceRestrictionIso X R V).hom.naturality d
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  change _ ≫ ((localIsomorphismRestriction X R V).map d ≫
    (etaleNormalizationCoefficients X V q).hom.app A') = _
  rw [← Category.assoc, ← hn, Category.assoc]
  apply (cancel_mono ((normalizationRestrict V.left.smallEtaleTopology q).map
    ((etaleDerivedSliceRestrictionIso X S V).inv.app A'))).mp
  simp only [Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hp]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem slice_normalized_presheaf_evaluation
    (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)))
    (dA : A ⟶ (normalizationRestrict X.smallEtaleTopology q).obj A')
    (dD : D ⟶ (normalizationRestrict X.smallEtaleTopology q).obj D')
    (r : derivedLocalIsoPresheaf X.smallEtaleTopology R A D ⟶
      derivedLocalIsoPresheaf X.smallEtaleTopology S A' D')
    (hr : ∀ (V : X.Etale)
      (e : (derivedSliceRestriction X.smallEtaleTopology R V).obj A ≅
        (derivedSliceRestriction X.smallEtaleTopology R V).obj D),
      e.hom ≫ (derivedSliceRestriction X.smallEtaleTopology R V).map dD ≫
          (sliceRestrictScalarsIso X.smallEtaleTopology R q V).inv.app D' =
        (derivedSliceRestriction X.smallEtaleTopology R V).map dA ≫
          (sliceRestrictScalarsIso X.smallEtaleTopology R q V).inv.app A' ≫
          (normalizationRestrict (X.smallEtaleTopology.over V) q).map
            (r.app (op V) e).hom)
    (U : X.ProEt) [IsAffine U.left]
    (hw : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology R A D)).obj.obj (op U)) :
    (derivedIsoEvaluation X R A D U hw s).hom ≫
        sliceComparisonNormalizationArrow X R S q dD U =
      sliceComparisonNormalizationArrow X R S q dA U ≫
        (normalizationRestrict ((ProEt.topology X).over U) q).map
          (derivedIsoEvaluation X S A' D' U hw
            (((comparisonSetUpperStar X).map
              ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map r)).hom.app
                (op U) s)).hom := by
  let iR := derivedLocalIsoToHomPresheaf
    (J := X.smallEtaleTopology) (B := R) (A := A) (D := D)
  let iS := derivedLocalIsoToHomPresheaf
    (J := X.smallEtaleTopology) (B := S) (A := A') (D := D')
  let f := derivedLocalHomPresheafMap (𝟙 A) dD
  let g := derivedRestrictionHomPresheaf X.smallEtaleTopology q A' D'
  let k := derivedLocalHomPresheafMap dA
    (𝟙 ((normalizationRestrict X.smallEtaleTopology q).obj D'))
  have he : iR ≫ f = r ≫ iS ≫ g ≫ k := by
    ext V e
    change (derivedSliceRestriction X.smallEtaleTopology R V.unop).obj A ≅
      (derivedSliceRestriction X.smallEtaleTopology R V.unop).obj D at e
    have h := congrArg (fun z ↦ z ≫
      (sliceRestrictScalarsIso X.smallEtaleTopology R q V.unop).hom.app D')
      (hr V.unop e)
    change (derivedSliceRestriction X.smallEtaleTopology R V.unop).map (𝟙 A) ≫
        e.hom ≫ (derivedSliceRestriction X.smallEtaleTopology R V.unop).map dD =
      (derivedSliceRestriction X.smallEtaleTopology R V.unop).map dA ≫
        ((sliceRestrictScalarsIso X.smallEtaleTopology R q V.unop).inv.app A' ≫
          (normalizationRestrict (X.smallEtaleTopology.over V.unop) q).map
            (r.app V e).hom ≫
          (sliceRestrictScalarsIso X.smallEtaleTopology R q V.unop).hom.app D') ≫
        (derivedSliceRestriction X.smallEtaleTopology R V.unop).map
          (𝟙 ((normalizationRestrict X.smallEtaleTopology q).obj D'))
    simp only [Category.assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp, Functor.comp_obj] at h ⊢
    exact h
  let F := presheafToSheaf X.smallEtaleTopology (Type (u + 1)) ⋙ comparisonSetUpperStar X
  let sR := (F.map iR).hom.app (op U) s
  let sS := (F.map r).hom.app (op U) s
  let tS := (F.map iS).hom.app (op U) sS
  let tR := (F.map g).hom.app (op U) tS
  have ht : (F.map f).hom.app (op U) sR = (F.map k).hom.app (op U) tR := by
    have h := congrArg (fun z ↦ (F.map z).hom.app (op U) s) he
    simpa only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, ConcreteCategory.comp_apply] using h
  have hf : derivedHomEvaluation X R A
      ((normalizationRestrict X.smallEtaleTopology q).obj D') U hw
        ((F.map f).hom.app (op U) sR) =
      derivedHomEvaluation X R A D U hw sR ≫
        (derivedSliceRestriction (ProEt.topology X) R U).map
          ((derivedComparison X R).map dD) := by
    have h := derivedHomEvaluation_natural X R A D A
      ((normalizationRestrict X.smallEtaleTopology q).obj D') (𝟙 A) dD U hw sR
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
    convert! h using 1
  have hk : derivedHomEvaluation X R A
      ((normalizationRestrict X.smallEtaleTopology q).obj D') U hw
        ((F.map k).hom.app (op U) tR) =
      (derivedSliceRestriction (ProEt.topology X) R U).map
          ((derivedComparison X R).map dA) ≫
        derivedHomEvaluation X R
          ((normalizationRestrict X.smallEtaleTopology q).obj A')
          ((normalizationRestrict X.smallEtaleTopology q).obj D') U hw tR := by
    have h := derivedHomEvaluation_natural X R
      ((normalizationRestrict X.smallEtaleTopology q).obj A')
      ((normalizationRestrict X.smallEtaleTopology q).obj D') A
      ((normalizationRestrict X.smallEtaleTopology q).obj D') dA
      (𝟙 ((normalizationRestrict X.smallEtaleTopology q).obj D')) U hw tR
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h
    convert! h using 1
  have hiR : derivedHomEvaluation X R A D U hw sR =
      (derivedIsoEvaluation X R A D U hw s).hom := by
    convert! derivedIsoEvaluation_hom X R A D U hw s using 1
  have hiS : derivedHomEvaluation X S A' D' U hw tS =
      (derivedIsoEvaluation X S A' D' U hw sS).hom := by
    convert! derivedIsoEvaluation_hom X S A' D' U hw sS using 1
  have hc : derivedHomEvaluation X R
        ((normalizationRestrict X.smallEtaleTopology q).obj A')
        ((normalizationRestrict X.smallEtaleTopology q).obj D') U hw tR ≫
      (derivedSliceRestriction (ProEt.topology X) R U).map
        ((comparisonRestrictScalarsIso X R q).hom.app D') ≫
      (sliceRestrictScalarsIso (ProEt.topology X) R q U).inv.app
        ((derivedComparison X S).obj D') =
    (derivedSliceRestriction (ProEt.topology X) R U).map
        ((comparisonRestrictScalarsIso X R q).hom.app A') ≫
      (sliceRestrictScalarsIso (ProEt.topology X) R q U).inv.app
        ((derivedComparison X S).obj A') ≫
      (normalizationRestrict ((ProEt.topology X).over U) q).map
        (derivedHomEvaluation X S A' D' U hw tS) := by
    convert! derivedHomEvaluation_restrictScalars X q A' D' U hw tS using 1
  have h := hf.symm.trans ((congrArg (derivedHomEvaluation X R A
    ((normalizationRestrict X.smallEtaleTopology q).obj D') U hw) ht).trans hk)
  have h' := congrArg (fun z ↦ z ≫
    ((derivedSliceRestriction (ProEt.topology X) R U).map
        ((comparisonRestrictScalarsIso X R q).hom.app D') ≫
      (sliceRestrictScalarsIso (ProEt.topology X) R q U).inv.app
        ((derivedComparison X S).obj D'))) h
  simp only [Category.assoc] at h'
  rw [hiR, hc, hiS] at h'
  simp only [sliceComparisonNormalizationArrow, Functor.map_comp, Category.assoc] at h' ⊢
  convert! h' using 1

private theorem etalePresheafIso_hom_apply
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (V : X.Etale)
    (e : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ≅
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    (etaleIsomorphismPresheafIso X B A D).hom.app (op V) e =
      etaleSliceToSourceIso X B A D V e := by
  rfl

end AlgebraicGeometry.Scheme
end EvaluationHelpers

namespace AlgebraicGeometry.Scheme

/-- Evaluation respects an already specified presheaf map whose generators satisfy
normalization. This is a preservation statement: it constructs neither a reduction map
nor normalization universal arrows, and assumes no finite, perfect, or lisse objects.

Source: Stacks Project, Tags 09BV and 0F63, with the canonical coefficient mate of
Tags 03DA and 098K.
(blueprint: lem-weil-pbc-source-isomorphism-normalized-presheaf-evaluation).

Proof: the equation on etale generators is an equality of maps of the Isom presheaves
into the presheaf of morphisms with restricted coefficients. Sheafify that equality and
apply comparison inverse image. On a weakly contractible affine the pro-etale
sheafification unit is invertible. Its inverse commutes with presheaf maps, by naturality
of the unit. Thus evaluation commutes with the given presheaf map and with the two
compositions in its generator equation. Slice-to-source localization carries coefficient
restriction to the canonical coefficient mate; pasting comparison and restriction mates
identifies the resulting arrows with localProEtaleNormalization. Transport the equality
through these localization isomorphisms to obtain the displayed square. No bijectivity of
comparison on arbitrary sections, local existence of isomorphisms, or cover is used. -/
theorem sourceIsomorphism_normalized_presheaf_evaluation
    (Y : Scheme.{t}) {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    (C K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} R)))
    (C' K' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} S)))
    (dC : C ⟶ (normalizationRestrict Y.smallEtaleTopology q).obj C')
    (dK : K ⟶ (normalizationRestrict Y.smallEtaleTopology q).obj K')
    (p : derivedLocalIsomorphismPresheaf C K ⟶ derivedLocalIsomorphismPresheaf C' K')
    (hp : ∀ (U : Y.Etale) (e : (localIsomorphismRestriction Y R U).obj C ≅
        (localIsomorphismRestriction Y R U).obj K),
      e.hom ≫ etaleIsomorphismNormalizationArrow Y q dK U =
        etaleIsomorphismNormalizationArrow Y q dC U ≫
          (normalizationRestrict U.left.smallEtaleTopology q).map
            (p.app (op U) e).hom)
    (U : Y.ProEt) (ha : IsAffine U.left)
    (hw : (ProEt.topology Y).IsWeaklyContractible.{t + 1} U)
    (s : ((comparisonSetUpperStar Y).obj
      (derivedLocalIsomorphismSheaf C K)).obj.obj (op U)) :
    (sourceDerivedIsoEvaluation Y R C K U ha hw s).hom ≫
        localProEtaleNormalization U.hom q dK =
      localProEtaleNormalization U.hom q dC ≫
        (normalizationRestrict (ProEt.topology U.left) q).map
          (sourceDerivedIsoEvaluation Y S C' K' U ha hw
            (((comparisonSetUpperStar Y).map
              ((presheafToSheaf Y.smallEtaleTopology (Type (t + 1))).map p)).hom.app
                (op U) s)).hom := by
  let := ha
  let δ := etaleIsomorphismPresheafIso Y R C K
  let ε := etaleIsomorphismPresheafIso Y S C' K'
  let r := δ.hom ≫ p ≫ ε.inv
  have hr (V : Y.Etale)
      (e : (derivedSliceRestriction Y.smallEtaleTopology R V).obj C ≅
        (derivedSliceRestriction Y.smallEtaleTopology R V).obj K) :
      e.hom ≫ (derivedSliceRestriction Y.smallEtaleTopology R V).map dK ≫
          (sliceRestrictScalarsIso Y.smallEtaleTopology R q V).inv.app K' =
        (derivedSliceRestriction Y.smallEtaleTopology R V).map dC ≫
          (sliceRestrictScalarsIso Y.smallEtaleTopology R q V).inv.app C' ≫
          (normalizationRestrict (Y.smallEtaleTopology.over V) q).map
            (r.app (op V) e).hom := by
    have hre : etaleSliceToSourceIso Y S C' K' V (r.app (op V) e) =
        p.app (op V) (etaleSliceToSourceIso Y R C K V e) := by
      have h := ConcreteCategory.congr_hom (congr_app ε.inv_hom_id (op V))
        (p.app (op V) (δ.hom.app (op V) e))
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, NatTrans.id_app,
        CategoryTheory.id_apply] at h
      change ε.hom.app (op V) (r.app (op V) e) =
        p.app (op V) (δ.hom.app (op V) e) at h
      simpa only [δ, ε, etalePresheafIso_hom_apply] using h
    have hs := hp V (etaleSliceToSourceIso Y R C K V e)
    rw [← hre] at hs
    simpa only [Category.assoc] using CategoryTheory.normalized_square_reflect
      (etaleDerivedSliceEquivalence Y R V).functor
      (etaleDerivedSliceEquivalence Y S V).functor
      (normalizationRestrict (Y.smallEtaleTopology.over V) q)
      (normalizationRestrict V.left.smallEtaleTopology q)
      (etaleDerivedSliceEquivalenceCoefficients Y V q)
      ((etaleDerivedSliceRestrictionIso Y R V).app C)
      ((etaleDerivedSliceRestrictionIso Y R V).app K)
      ((etaleDerivedSliceRestrictionIso Y S V).app C')
      ((etaleDerivedSliceRestrictionIso Y S V).app K')
      ((derivedSliceRestriction Y.smallEtaleTopology R V).map dC ≫
        (sliceRestrictScalarsIso Y.smallEtaleTopology R q V).inv.app C')
      ((derivedSliceRestriction Y.smallEtaleTopology R V).map dK ≫
        (sliceRestrictScalarsIso Y.smallEtaleTopology R q V).inv.app K')
      (etaleIsomorphismNormalizationArrow Y q dC V)
      (etaleIsomorphismNormalizationArrow Y q dK V)
      (etale_source_slice_normalization Y V q dC)
      (etale_source_slice_normalization Y V q dK)
      e (r.app (op V) e) hs
  let F := presheafToSheaf Y.smallEtaleTopology (Type (t + 1))
  let δs := etaleIsomorphismSheafIso Y R C K
  let εs := etaleIsomorphismSheafIso Y S C' K'
  let s₀ := ((comparisonSetUpperStar Y).map δs.inv).hom.app (op U) s
  have hs : ((comparisonSetUpperStar Y).map (F.map r)).hom.app (op U) s₀ =
      ((comparisonSetUpperStar Y).map εs.inv).hom.app (op U)
        (((comparisonSetUpperStar Y).map (F.map p)).hom.app (op U) s) := by
    have hm : δs.inv ≫ F.map r = F.map p ≫ εs.inv := by
      simp only [r, δs, εs, etaleIsomorphismSheafIso, F, Functor.map_comp,
        Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
      rw [← Functor.map_comp_assoc, δ.inv_hom_id]
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, ε]
    have h := congrArg
      (fun k ↦ ((comparisonSetUpperStar Y).map k).hom.app (op U) s) hm
    dsimp only [F, derivedLocalIsoSheaf] at h ⊢
    simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, ConcreteCategory.comp_apply, s₀] at h ⊢
    convert! h using 1
  have hh := slice_normalized_presheaf_evaluation Y q C K C' K' dC dK r hr U hw s₀
  rw [hs] at hh
  simp only [sourceDerivedIsoEvaluation]
  exact sourceSliceNormalization_transport Y q C K C' K' dC dK U
    (derivedIsoEvaluation Y R C K U hw s₀)
    (derivedIsoEvaluation Y S C' K' U hw
      (((comparisonSetUpperStar Y).map εs.inv).hom.app (op U)
        (((comparisonSetUpperStar Y).map (F.map p)).hom.app (op U) s))) hh

end AlgebraicGeometry.Scheme
