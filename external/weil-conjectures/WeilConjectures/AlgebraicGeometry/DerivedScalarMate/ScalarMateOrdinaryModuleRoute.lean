/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
import all WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarTensorOrdinary
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # Ordinary scalar mate and tensor pullback on module sheaves

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL.
(blueprint: lem-sfb-scalar-mate-ordinary-module-route).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.DerivedScalarMate
attribute [local irreducible] SheafOfModules.monoidalCategory
  Functor.leftAdjoint proEtaleRingModulePullback

section ProjectionUnit
attribute [local semireducible] SheafOfModules.monoidalCategory

private theorem projectionUnit_homEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    let φ : (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
        ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
      ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f R S c).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    (proEtaleRingModuleAdjunction f R S c).homEquiv _ _
      (Classical.choose (proEtaleProjectionUnit_existsUnique f R S c).exists).hom =
    SheafOfModules.unitToPushforwardObjUnit φ := by
  dsimp only
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let adj := proEtaleRingModuleAdjunction f R S c
  let φ : (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f R S c).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint := adj.isRightAdjoint
  let adj' := SheafOfModules.pullbackPushforwardAdjunction.{u + 1} φ
  let e := adj.leftAdjointUniq adj'
  let j := e.app (SheafOfModules.unit _) ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  have hj : adj.homEquiv _ _ j.hom = SheafOfModules.unitToPushforwardObjUnit φ := by
    change adj.homEquiv _ _ (e.hom.app _ ≫ _) = _
    rw [adj.homEquiv_naturality_right]
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ
  have hcompat (M : proEtaleRingModules Y R) :
      (proEtaleOrdinaryTensorPullback f R S c M (𝟙_ _)).hom ≫
        (𝟙 _ ⊗ₘ j.hom) ≫ (ρ_ _).hom =
      (proEtaleRingModulePullback f R S c).map (ρ_ M).hom := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, adj.unit_naturality]
    apply proEtaleTensorPair_hom_ext Y R
    intro U m r
    obtain ⟨U⟩ := U
    have hmu := (Classical.choose_spec
      (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists).2 M (𝟙_ _) U m r
    have hjr := congrArg (fun z ↦ z.val.app (Opposite.op U) r) hj
    rw [Adjunction.homEquiv_unit] at hjr
    change j.hom.val.app (Opposite.op ((proEtaleBaseChange f).obj U))
      ((adj.unit.app (𝟙_ _)).val.app (Opposite.op U) r) =
        (proEtaleRingDirectImageMap f R S c).hom.app (Opposite.op U) r at hjr
    change (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app _
        (((SheafOfModules.monoidalCategory S).tensorHom (𝟙 _) j.hom).val.app _
          ((proEtaleOrdinaryTensorPullback f R S c M (𝟙_ _)).hom.val.app _
            ((adj.unit.app _).val.app _ (proEtaleTensorPair Y R M (𝟙_ _) _ m r)))) =
      (adj.unit.app M).val.app _ ((ρ_ M).hom.val.app _
        (proEtaleTensorPair Y R M (𝟙_ _) _ m r))
    erw [hmu]
    let V := Opposite.op ((proEtaleBaseChange f).obj U)
    let m' : ((proEtaleRingModulePullback f R S c).obj M).val.obj V :=
      (adj.unit.app M).val.app (Opposite.op U) m
    let r' : ((proEtaleRingModulePullback f R S c).obj (𝟙_ _)).val.obj V :=
      (adj.unit.app (𝟙_ _)).val.app (Opposite.op U) r
    change j.hom.val.app V r' =
      (proEtaleRingDirectImageMap f R S c).hom.app (Opposite.op U) r at hjr
    change (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app V
        (((SheafOfModules.monoidalCategory S).tensorHom (𝟙 _) j.hom).val.app V
          (proEtaleTensorPair X S _ _ V m' r')) = _
    have htens := proEtaleTensorPair_tensorHom X S
      (𝟙 ((proEtaleRingModulePullback f R S c).obj M)) j.hom V m' r'
    change ((SheafOfModules.monoidalCategory S).tensorHom (𝟙 _) j.hom).val.app V
        (proEtaleTensorPair X S _ _ V m' r') =
      proEtaleTensorPair X S _ _ V m' (j.hom.val.app V r') at htens
    calc
      _ = (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app V
          (proEtaleTensorPair X S _ _ V m' (j.hom.val.app V r')) :=
        congrArg (fun z ↦
          (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app V z) htens
      _ = (show S.obj.obj V from j.hom.val.app V r') • m' :=
        proEtaleTensorPair_rightUnitor X S _ V m' (j.hom.val.app V r')
      _ = ((proEtaleRingDirectImageMap f R S c).hom.app (Opposite.op U) r) • m' :=
        congrArg (fun z ↦ z • m') hjr
      _ = (adj.unit.app M).val.app (Opposite.op U)
          ((show R.obj.obj (Opposite.op U) from r) • m) :=
        ((adj.unit.app M).val.app (Opposite.op U)).hom.map_smul r m |>.symm
      _ = _ := congrArg (fun z ↦ (adj.unit.app M).val.app (Opposite.op U) z)
        (proEtaleTensorPair_rightUnitor Y R M (Opposite.op U) m r).symm
  have he : j = Classical.choose (proEtaleProjectionUnit_existsUnique f R S c).exists :=
    (proEtaleProjectionUnit_existsUnique f R S c).unique hcompat
      (Classical.choose_spec (proEtaleProjectionUnit_existsUnique f R S c).exists)
  rw [← he]
  exact hj

end ProjectionUnit

private theorem restrictionPullback_unit
    {U V : Scheme.{u}} (f : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)
    (N : proEtaleRingModules V SV) (W : V.ProEtᵒᵖ) (z : N.val.obj W) :
    ((proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm).app N).val.app
        ((proEtaleBaseChange f).op.obj W)
        (((proEtaleRingModuleAdjunction f RV RU cR).unit.app
          ((proEtaleRingRestrictScalars aV).obj N)).val.app W z) =
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z := by
  let δ := proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm
  let σ := proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm
  have h := unit_mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
    (proEtaleRingModuleAdjunction f RV RU cR) (TwoSquare.mk _ _ _ _ σ) N
  have hm := restrictionPullback_mate f RV SV RU SU aV aU cR cS comm
  change (proEtaleRingRestrictScalars aV).map
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app N) ≫
        (mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
          (proEtaleRingModuleAdjunction f RV RU cR)
          (TwoSquare.mk _ _ _ _ σ)).app _ = _ at h
  rw [hm] at h
  have hz := congrArg (fun k ↦ k.val.app W z) h
  change (δ.hom.app ((proEtaleRingModulePullback f SV SU cS).obj N)).val.app W
      (((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z) = _ at hz
  have he := (Classical.choose_spec
    (proEtaleRingRestrictionDirectImage_existsUnique f RV SV RU SU aV aU cR cS comm)).1
      ((proEtaleRingModulePullback f SV SU cS).obj N) W
      (((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z)
  exact (he.symm.trans hz).symm

private theorem coefficientPullback_unit {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (W : T.ProEtᵒᵖ) (s : B.obj.obj W) :
    (coefficientPullback f a).hom.val.app ((proEtaleBaseChange f).op.obj W)
      (((proEtaleRingModuleAdjunction f A (inverseRing f A) (Iso.refl _)).unit.app
        (coefficient a)).val.app W s) =
    (proEtaleRingDirectImageMap f B (inverseRing f B) (Iso.refl _)).hom.app W s := by
  have h := congrArg (fun k ↦ k.val.app W s)
    (projectionUnit_homEquiv f B (inverseRing f B) (Iso.refl _))
  rw [Adjunction.homEquiv_unit] at h
  change _ = _ at h
  unfold coefficientPullback
  change (Classical.choose
    (proEtaleProjectionUnit_existsUnique f B (inverseRing f B) (Iso.refl _)).exists).hom.val.app _
      (((proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).app
        (SheafOfModules.unit _)).val.app _ _) = _
  rw [restrictionPullback_unit]
  exact h

private theorem ordinaryTensorIso_section {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : A ⟶ B)
    (M : proEtaleRingModules W A) (U : W.ProEtᵒᵖ)
    (b : B.obj.obj U) (m : M.val.obj U) :
    ((ordinaryTensorIso a).hom.app M).val.app U (reductionTensorSection W a M U b m) =
      proEtaleTensorPair W A M (coefficient a) U m b := by
  have h := (Classical.choose_spec (ordinaryTensorIso_existsUnique a).exists) M U b m
  dsimp only [IsOrdinaryTensor] at h
  rw [pureSection_toSheafify] at h
  exact h

private theorem ordinaryScalar_pure {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (χ : proEtaleRingExtension a ⋙
      proEtaleRingModulePullback f B (inverseRing f B) (Iso.refl _) ≅
      proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _) ⋙
        proEtaleRingExtension (inverseMap f a))
    (hχ : ∀ M, (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).map
        ((proEtaleRingExtensionAdjunction a).unit.app M) ≫
      (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).app
          ((proEtaleRingExtension a).obj M) ≫
      (restriction (inverseMap f a)).map (χ.hom.app M) =
      (proEtaleRingExtensionAdjunction (inverseMap f a)).unit.app
        ((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).obj M))
    (M : proEtaleRingModules T A) (W : T.ProEtᵒᵖ) (s : B.obj.obj W)
    (x : M.val.obj W) :
    (χ.hom.app M).val.app ((proEtaleBaseChange f).op.obj W)
      (((proEtaleRingModuleAdjunction f B (inverseRing f B) (Iso.refl _)).unit.app
        ((proEtaleRingExtension a).obj M)).val.app W (reductionTensorSection T a M W s x)) =
      reductionTensorSection Z (inverseMap f a)
        ((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).obj M)
        ((proEtaleBaseChange f).op.obj W)
        ((proEtaleRingDirectImageMap f B (inverseRing f B) (Iso.refl _)).hom.app W s)
        (((proEtaleRingModuleAdjunction f A (inverseRing f A) (Iso.refl _)).unit.app M
          ).val.app W x) := by
  let FA := proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
  let adjA := proEtaleRingModuleAdjunction f A (inverseRing f A) (Iso.refl _)
  let adjB := proEtaleRingModuleAdjunction f B (inverseRing f B) (Iso.refl _)
  let b := proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)
  let N := (proEtaleRingExtension a).obj M
  let V := (proEtaleBaseChange f).op.obj W
  let q := b.app N ≫ (restriction (inverseMap f a)).map (χ.hom.app M)
  let uY := (proEtaleRingExtensionAdjunction a).unit.app M
  let uX := (proEtaleRingExtensionAdjunction (inverseMap f a)).unit.app (FA.obj M)
  have h : uY ≫ adjA.unit.app ((restriction a).obj N) ≫
      (proEtaleRingModuleDirectImage f A (inverseRing f A) (Iso.refl _)).map q =
      adjA.unit.app M ≫
        (proEtaleRingModuleDirectImage f A (inverseRing f A) (Iso.refl _)).map uX := by
    erw [← adjA.unit_naturality_assoc]
    rw [← Functor.map_comp]
    exact congrArg (adjA.unit.app M ≫ ·)
      (congrArg (proEtaleRingModuleDirectImage f A (inverseRing f A) (Iso.refl _)).map
        (hχ M))
  have hx := congrArg (fun k ↦ k.val.app W x) h
  change q.val.app V ((adjA.unit.app ((restriction a).obj N)).val.app W
      (uY.val.app W x)) = uX.val.app V ((adjA.unit.app M).val.app W x) at hx
  have huY : uY.val.app W x = reductionTensorSection T a M W 1 x :=
    (pbcScalarAdjunction_exists a).exists.choose_spec M W x
  have huX : uX.val.app V ((adjA.unit.app M).val.app W x) =
      reductionTensorSection Z (inverseMap f a) (FA.obj M) V 1
        ((adjA.unit.app M).val.app W x) :=
    (pbcScalarAdjunction_exists (inverseMap f a)).exists.choose_spec
      (FA.obj M) V ((adjA.unit.app M).val.app W x)
  rw [huY, huX] at hx
  change (χ.hom.app M).val.app V ((b.app N).val.app V
    ((adjA.unit.app ((restriction a).obj N)).val.app W
      (reductionTensorSection T a M W 1 x))) = _ at hx
  rw [restrictionPullback_unit] at hx
  have hs := tensorSection_smul T a M W s 1 x
  rw [mul_one] at hs
  rw [← hs]
  have hsm := ((adjB.unit.app N).val.app W).hom.map_smul s
    (reductionTensorSection T a M W 1 x)
  change (adjB.unit.app N).val.app W (s • reductionTensorSection T a M W 1 x) =
    @SMul.smul ((inverseRing f B).obj.obj V)
      (((proEtaleRingModulePullback f B (inverseRing f B) (Iso.refl _)).obj N).val.obj V)
      inferInstance
      ((proEtaleRingDirectImageMap f B (inverseRing f B) (Iso.refl _)).hom.app W s)
      ((adjB.unit.app N).val.app W (reductionTensorSection T a M W 1 x)) at hsm
  rw [hsm]
  erw [((χ.hom.app M).val.app V).hom.map_smul]
  rw [hx]
  simpa only [mul_one] using tensorSection_smul Z (inverseMap f a) (FA.obj M) V
    ((proEtaleRingDirectImageMap f B (inverseRing f B) (Iso.refl _)).hom.app W s) 1
    ((adjA.unit.app M).val.app W x)

/-- The ordinary inverse scalar mate agrees with tensor pullback and the fixed coefficient map.
Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL
(blueprint: lem-sfb-scalar-mate-ordinary-module-route).

Proof: transpose the two maps through the inverse-image adjunction. The source is the
restricted sheafified extension of scalars, so it suffices to evaluate at every local
pure tensor b tensor m. The scalar-unit equation gives the mate's value at 1 tensor m;
linearity over the pulled-back B extends this to every local b. The normalized ordinary
extension/tensor isomorphism sends that value to pullback(m) tensor pullback(b).
The tensor pullback's defining pure-section equation and the coefficient comparison's
unit normalization give exactly the same value for the other route. Sheafification
universality and the adjunction identify the two maps. No flatness is required. -/
theorem scalarMate_ordinary_module_route {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (χ : proEtaleRingExtension a ⋙
      proEtaleRingModulePullback f B (inverseRing f B) (Iso.refl _) ≅
      proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _) ⋙
        proEtaleRingExtension (inverseMap f a))
    (hχ : ∀ M, (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).map
        ((proEtaleRingExtensionAdjunction a).unit.app M) ≫
      (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).app
          ((proEtaleRingExtension a).obj M) ≫
      (restriction (inverseMap f a)).map (χ.hom.app M) =
      (proEtaleRingExtensionAdjunction (inverseMap f a)).unit.app
        ((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).obj M))
    (M : proEtaleRingModules T A) :
    (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
      a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).app
        ((proEtaleRingExtension a).obj M) ≫
      (restriction (inverseMap f a)).map (χ.hom.app M) ≫
      (ordinaryTensorIso (inverseMap f a)).hom.app
        ((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).obj M) =
    (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).map
        ((ordinaryTensorIso a).hom.app M) ≫
      (proEtaleOrdinaryTensorPullback f A (inverseRing f A) (Iso.refl _)
        M (coefficient a)).hom ≫
      ((proEtaleOrdinaryTensor Z (inverseRing f A)).obj
        ((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).obj M)).map
          (coefficientPullback f a).hom := by
  let FA := proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
  let adj := proEtaleRingModuleAdjunction f A (inverseRing f A) (Iso.refl _)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  rw [adj.unit_naturality_assoc]
  apply level_hom_ext T a M
  intro W s x
  let V := (proEtaleBaseChange f).op.obj W
  change ((ordinaryTensorIso (inverseMap f a)).hom.app (FA.obj M)).val.app V
      ((χ.hom.app M).val.app V
        (((proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
          a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).app
          ((proEtaleRingExtension a).obj M)).val.app V
          ((adj.unit.app ((restriction a).obj ((proEtaleRingExtension a).obj M))).val.app W
            (reductionTensorSection T a M W s x)))) = _
  rw [restrictionPullback_unit, ordinaryScalar_pure f a χ hχ,
    ordinaryTensorIso_section]
  change _ =
    (((proEtaleOrdinaryTensor Z (inverseRing f A)).obj (FA.obj M)).map
      (coefficientPullback f a).hom).val.app V
      ((proEtaleOrdinaryTensorPullback f A (inverseRing f A) (Iso.refl _)
        M (coefficient a)).hom.val.app V
        ((adj.unit.app ((ordinaryTensor a).obj M)).val.app W
          (((ordinaryTensorIso a).hom.app M).val.app W
            (reductionTensorSection T a M W s x))))
  rw [ordinaryTensorIso_section]
  have hmu := (Classical.choose_spec
    (proEtaleOrdinaryTensorPullback_existsUnique f A (inverseRing f A)
      (Iso.refl _)).exists).2 M (coefficient a) W.unop x s
  erw [hmu]
  have ht := proEtaleTensorPair_tensorHom Z (inverseRing f A) (𝟙 (FA.obj M))
    (coefficientPullback f a).hom V ((adj.unit.app M).val.app W x)
    ((adj.unit.app (coefficient a)).val.app W s)
  simp only [MonoidalCategory.id_tensorHom, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] at ht
  erw [ht, coefficientPullback_unit]

end AlgebraicGeometry.Scheme.DerivedScalarMate
