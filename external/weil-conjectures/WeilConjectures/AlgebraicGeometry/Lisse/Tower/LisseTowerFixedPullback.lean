/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerScalarRestriction
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.CategoryTheory.Constant.ConstantScalarGeometricAdjunctions

/-! # Fixed finite realization and ordinary inverse image

## References

* Stacks Project, Modules on Sites, Tags 03CY, 03D8 and 03DA
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  lisseTowerFixedRealization proEtaleRingModulePullback

private theorem coefficient_comp
    {X T Z : Scheme.{u}} (a : Z ⟶ T) (b : T ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (lisseTowerFiniteCoefficientIso (a ≫ b) d n).hom =
      (proEtaleRingInverseImageComp a b).hom.app ((pbcAdicRings X d).obj (op n)) ≫
        (adicTowerInverseImage a).map (lisseTowerFiniteCoefficientIso b d n).hom ≫
          proEtaleConstantInverseImageMap a CommRingCat.{u + 1}
            (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) := by
  change (adicTowerInverseImage (a ≫ b)).map (pbcLevelConstantComparison X d n).inv ≫
      (proEtaleConstantComparison (a ≫ b)).app _ = _
  rw [proEtaleConstantComparison_comp a b]
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    lisseTowerFiniteCoefficientIso, Functor.map_comp, Category.assoc]
  rw [(proEtaleRingInverseImageComp a b).hom.naturality_assoc]
  rfl

private theorem scalar_square
    {X T Z : Scheme.{u}} (a : Z ⟶ T) (b : T ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    lisseTowerFiniteScalarMap b d n ≫
      ((adicLisseForget T).map (proEtaleRingDirectImageMap a
        ((adicTowerInverseImage b).obj ((pbcAdicRings X d).obj (op n)))
        ((adicTowerInverseImage (a ≫ b)).obj ((pbcAdicRings X d).obj (op n)))
        ((proEtaleRingInverseImageComp a b).symm.app ((pbcAdicRings X d).obj (op n))))).hom =
      Functor.whiskerLeft (proEtaleBaseChange a).op
        (lisseTowerFiniteScalarMap (a ≫ b) d n) := by
  let R := (pbcAdicRings X d).obj (op n)
  let RT := (adicTowerInverseImage b).obj R
  let RZ := (adicTowerInverseImage (a ≫ b)).obj R
  let c := (proEtaleRingInverseImageComp a b).symm.app R
  let eT := lisseTowerFiniteCoefficientIso b d n
  let eZ := lisseTowerFiniteCoefficientIso (a ≫ b) d n
  let C := CommRingCat.of (A ⧸ d.ideal ^ (n + 1))
  let L := adicTowerInverseImage a
  let G := proEtaleSheafDirectImage a CommRingCat.{u + 1}
  let adj := proEtaleSheafAdjunction a CommRingCat.{u + 1}
  have he : c.hom ≫ eZ.hom = L.map eT.hom ≫
      proEtaleConstantInverseImageMap a CommRingCat.{u + 1} C := by
    dsimp only [eZ]
    rw [coefficient_comp a b d n]
    exact (Iso.inv_hom_id_assoc ((proEtaleRingInverseImageComp a b).app R) _)
  have hr : proEtaleRingDirectImageMap a RT RZ c ≫ G.map eZ.hom =
      eT.hom ≫ proEtaleConstantDirectImageMap a CommRingCat.{u + 1} C := by
    change adj.homEquiv _ _ c.hom ≫ G.map eZ.hom = _
    rw [← adj.homEquiv_naturality_right, he, adj.homEquiv_naturality_left]
    congr 1
    change adj.homEquiv _ _
      ((adj.homEquiv _ _).symm (proEtaleConstantDirectImageMap a CommRingCat C)) = _
    exact (adj.homEquiv _ _).apply_symm_apply _
  have hi : eT.inv ≫ proEtaleRingDirectImageMap a RT RZ c =
      proEtaleConstantDirectImageMap a CommRingCat.{u + 1} C ≫ G.map eZ.inv := by
    apply (cancel_mono (G.map eZ.hom)).1
    rw [Category.assoc, hr, Iso.inv_hom_id_assoc]
    simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id]
    exact (Category.comp_id _).symm
  have hunit := ((sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    ((Functor.const T.ProEtᵒᵖ).obj C)
    (G.obj ((constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).obj C))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange a).op
        (toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj C)))
  change toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj C) ≫
      (proEtaleConstantDirectImageMap a CommRingCat.{u + 1} C).hom = _ at hunit
  apply NatTrans.ext
  funext U
  change (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj C)).app U) ≫
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map (eT.inv.hom.app U) ≫
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((proEtaleRingDirectImageMap a RT RZ c).hom.app U) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hiU := congrArg (fun t ↦ t.hom.app U) hi
  change eT.inv.hom.app U ≫ (proEtaleRingDirectImageMap a RT RZ c).hom.app U =
    (proEtaleConstantDirectImageMap a CommRingCat.{u + 1} C).hom.app U ≫
      eZ.inv.hom.app ((proEtaleBaseChange a).op.obj U) at hiU
  erw [hiU, ← Category.assoc]
  have hU := congrArg (fun t ↦ t.app U) hunit
  change (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj C)).app U ≫
    (proEtaleConstantDirectImageMap a CommRingCat.{u + 1} C).hom.app U = _ at hU
  erw [hU, Functor.map_comp]
  rfl

private def coefficientEmbedding (T : Scheme.{u})
    (Q : Type (u + 1)) [CommRing Q] :=
  sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} Q) ⋙
    ProEtale.finiteCoefficientModulePresheaf T.ProEt Q

private def coefficientRestriction {X T : Scheme.{u}} (b : T ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  SheafOfModules.forget.{u + 1} ((adicLisseForget T).obj
      ((adicTowerInverseImage b).obj ((pbcAdicRings X d).obj (op n)))) ⋙
    PresheafOfModules.restrictScalars.{u + 1} (lisseTowerFiniteScalarMap b d n)

private def coefficientUnitIso {X T : Scheme.{u}} (b : T ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    coefficientEmbedding T (A ⧸ d.ideal ^ (n + 1)) ≅
      lisseTowerFiniteSheafRealization b d n ⋙ coefficientRestriction b d n := by
  let E := coefficientEmbedding T (A ⧸ d.ideal ^ (n + 1))
  have hunit (F : Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1)))) :
      IsIso ((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (lisseTowerFiniteScalarMap b d n)).unit.app (E.obj F)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) AddCommGrpCat.{u + 1})).obj F).property
  let η : E ⟶ lisseTowerFiniteSheafRealization b d n ⋙ coefficientRestriction b d n :=
    Functor.whiskerLeft E
      (PresheafOfModules.sheafificationAdjunction.{u + 1} (lisseTowerFiniteScalarMap b d n)).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hunit
  exact asIso η

private def restrictionDirectImageIso
    {X T Z : Scheme.{u}} (a : Z ⟶ T) (b : T ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    proEtaleRingModuleDirectImage a
        ((adicTowerInverseImage b).obj ((pbcAdicRings X d).obj (op n)))
        ((adicTowerInverseImage (a ≫ b)).obj ((pbcAdicRings X d).obj (op n)))
        ((proEtaleRingInverseImageComp a b).symm.app ((pbcAdicRings X d).obj (op n))) ⋙
      coefficientRestriction b d n ≅
    coefficientRestriction (a ≫ b) d n ⋙
      PresheafOfModules.pushforward₀ (proEtaleBaseChange a)
        ((Functor.const Z.ProEtᵒᵖ).obj (RingCat.of (A ⧸ d.ideal ^ (n + 1)))) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let L := ((proEtaleRingModuleDirectImage a
        ((adicTowerInverseImage b).obj ((pbcAdicRings X d).obj (op n)))
        ((adicTowerInverseImage (a ≫ b)).obj ((pbcAdicRings X d).obj (op n)))
        ((proEtaleRingInverseImageComp a b).symm.app ((pbcAdicRings X d).obj (op n))) ⋙
      coefficientRestriction b d n).obj M)
    let R := ((coefficientRestriction (a ≫ b) d n ⋙
      PresheafOfModules.pushforward₀ (proEtaleBaseChange a)
        ((Functor.const Z.ProEtᵒᵖ).obj (RingCat.of (A ⧸ d.ideal ^ (n + 1))))).obj M)
    change L ≅ R
    refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
    · let g : L.obj U ≃ₗ[A ⧸ d.ideal ^ (n + 1)] R.obj U :=
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r m
            have h := congrArg (fun t ↦ (t.app U).hom r) (scalar_square a b d n)
            change ((proEtaleRingDirectImageMap a
              ((adicTowerInverseImage b).obj ((pbcAdicRings X d).obj (op n)))
              ((adicTowerInverseImage (a ≫ b)).obj ((pbcAdicRings X d).obj (op n)))
              ((proEtaleRingInverseImageComp a b).symm.app
                ((pbcAdicRings X d).obj (op n)))).hom.app U)
              ((lisseTowerFiniteScalarMap b d n).app U r) •
                (show M.val.obj ((proEtaleBaseChange a).op.obj U) from m) =
              (lisseTowerFiniteScalarMap (a ≫ b) d n).app
                ((proEtaleBaseChange a).op.obj U) r •
                  (show M.val.obj ((proEtaleBaseChange a).op.obj U) from m)
            exact congrArg (fun q : ((adicTowerInverseImage (a ≫ b)).obj
              ((pbcAdicRings X d).obj (op n))).obj.obj
                ((proEtaleBaseChange a).op.obj U) ↦ q •
              (show M.val.obj ((proEtaleBaseChange a).op.obj U) from m)) h }
      exact g.toModuleIso
    · intro U V g
      ext x
      rfl
  · intro M N g
    ext U x
    rfl

private def finiteSheafPullback
    {X T Z : Scheme.{u}} (a : Z ⟶ T) (b : T ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) a ⋙
        lisseTowerFiniteSheafRealization (a ≫ b) d n ≅
      lisseTowerFiniteSheafRealization b d n ⋙
        proEtaleRingModulePullback a
          ((adicTowerInverseImage b).obj ((pbcAdicRings X d).obj (op n)))
          ((adicTowerInverseImage (a ≫ b)).obj ((pbcAdicRings X d).obj (op n)))
          ((proEtaleRingInverseImageComp a b).symm.app ((pbcAdicRings X d).obj (op n))) := by
  let Q := A ⧸ d.ideal ^ (n + 1)
  let R := (pbcAdicRings X d).obj (op n)
  let c := (proEtaleRingInverseImageComp a b).symm.app R
  let J := proEtaleRingModuleDirectImage a ((adicTowerInverseImage b).obj R)
    ((adicTowerInverseImage (a ≫ b)).obj R) c
  let P := PresheafOfModules.pushforward₀ (proEtaleBaseChange a)
    ((Functor.const Z.ProEtᵒᵖ).obj (RingCat.of Q))
  have : (coefficientRestriction b d n).Full :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (lisseTowerFiniteScalarMap b d n)).fullyFaithfulROfIsIsoCounit.full
  have : (coefficientRestriction b d n).Faithful :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (lisseTowerFiniteScalarMap b d n)).fullyFaithfulROfIsIsoCounit.faithful
  let β : (lisseTowerFiniteSheafRealization (a ≫ b) d n ⋙ J) ⋙
        coefficientRestriction b d n ≅
      (ProEtale.lowerStar (ModuleCat.{u + 1} Q) a ⋙
        lisseTowerFiniteSheafRealization b d n) ⋙ coefficientRestriction b d n :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (lisseTowerFiniteSheafRealization (a ≫ b) d n)
        (restrictionDirectImageIso a b d n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (coefficientUnitIso (a ≫ b) d n).symm P ≪≫
      (Iso.refl _ : coefficientEmbedding Z Q ⋙ P ≅
        ProEtale.lowerStar (ModuleCat.{u + 1} Q) a ⋙ coefficientEmbedding T Q) ≪≫
      Functor.isoWhiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} Q) a)
        (coefficientUnitIso b d n) ≪≫ (Functor.associator _ _ _).symm
  let β' := Functor.fullyFaithfulCancelRight (coefficientRestriction b d n) β
  exact (adjunctionSquare (lisseTowerFiniteSheafRealization b d n)
    (lisseTowerFiniteSheafRealization (a ≫ b) d n)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Q) a)
    (proEtaleRingModuleAdjunction a ((adicTowerInverseImage b).obj R)
      ((adicTowerInverseImage (a ≫ b)).obj R) c) β'.symm).choose

/-- Ordinary fixed finite realization commutes with inverse image, retaining the
canonical composite coefficient identification. No derived object, tower, etale
comparison, or chosen marking occurs here. -/
theorem lisseTower_fixed_sheaf_pullback
    {X T Z : Scheme.{u}} (a : Z ⟶ T) (b : T ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    Nonempty (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a ⋙
        lisseTowerFixedSheafRealization (a ≫ b) d n ≅
      lisseTowerFixedSheafRealization b d n ⋙
        proEtaleRingModulePullback a
          ((adicTowerInverseImage b).obj ((pbcAdicRings X d).obj (op n)))
          ((adicTowerInverseImage (a ≫ b)).obj ((pbcAdicRings X d).obj (op n)))
          ((proEtaleRingInverseImageComp a b).symm.app ((pbcAdicRings X d).obj (op n)))) := by
  let q := constantAdicQuotientMap d.ideal n
  let := ProEt.isContinuous_overPullback a
  let k : sheafCompose (ProEt.topology T)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
      ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) a ≅
    ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a ⋙
      sheafCompose (ProEt.topology Z)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) :=
    normalizationPullbackIso (ProEt.topology T)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ a) (ProEt.topology Z) q
  exact ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight k.symm (lisseTowerFiniteSheafRealization (a ≫ b) d n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (finiteSheafPullback a b d n) ≪≫
    (Functor.associator _ _ _).symm⟩

end AlgebraicGeometry.Scheme
