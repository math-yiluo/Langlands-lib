/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarOperationComp
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Constructible restriction and rationalization of scalar comparisons

Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.

## References

* Milne, Section 19
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme

-- `SignedDoubleHomCone.moduleBinaryBiproducts` leaves its universe free
attribute [-instance] CategoryTheory.SignedDoubleHomCone.moduleBinaryBiproducts
section ConditionalRestriction
variable {X Y : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A) (H : PbcCompletedDerived X d ⥤ PbcCompletedDerived Y d)
variable (h : ∀ K : PbcBoundedConstructibleComplete X d,
  PbcIsBoundedConstructibleComplete Y d (H.obj K.obj))

/-- Conditional restriction keeps exactly the actual ambient object and arrow maps. -/
def pbcConditionalIntegral : PbcBoundedConstructibleComplete X d ⥤
    PbcBoundedConstructibleComplete Y d :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete Y d)
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X d) ⋙ H) h

/-- The actual restriction inherits addition and its constant-section linearity. -/
theorem pbcConditionalIntegral_linear [H.Additive] [H.Linear A] :
    (pbcConditionalIntegral d H h).Additive ∧ (pbcConditionalIntegral d H h).Linear A := by
  constructor
  · dsimp only [pbcConditionalIntegral]
    infer_instance
  · constructor
    intros K L f r
    apply ObjectProperty.hom_ext
    exact H.map_smul r f.hom

/-- Addition on the actual conditional restriction. -/
instance pbcConditionalIntegral_additive [H.Additive] [H.Linear A] :
    (pbcConditionalIntegral d H h).Additive := (pbcConditionalIntegral_linear d H h).1

/-- Linearity on the actual conditional restriction. -/
instance pbcConditionalIntegral_linearInstance [H.Additive] [H.Linear A] :
    (pbcConditionalIntegral d H h).Linear A := (pbcConditionalIntegral_linear d H h).2

/-- Rationalizing a preserving actual operation uses the tensor base-change Hom map. -/
def pbcConditionalRational (p : A) [H.Additive] [H.Linear A] :
    PbcRationalCategory X d p ⥤ PbcRationalCategory Y d p :=
  ScalarLocalization.transport A p (pbcConditionalIntegral d H h)
end ConditionalRestriction

section ConditionalOperations
variable (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
variable [Algebra (Padic l) E] [Algebra (Padic l) F]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable (i : E →ₐ[Padic l] F) {X Y : Scheme.{u}} (g : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcCompletedScalar_directImage
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    pbcCompletedScalar Y d ≫ completedCoefficientDirectImageMap g d =
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A) ≫
        (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
          (pbcCompletedScalar X d) := by
  have hp (W : Scheme.{u}) (n : ℕ) :
      pbcCompletedScalar W d ≫ pbcAdicProjection W d n =
        (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
            (pbcLevelConstantComparison W d n).hom := by
    dsimp only [pbcCompletedScalar, pbcAdicProjection, pbcCompletedComparison]
    rw [Category.assoc]
    erw [HasLimit.isoOfNatIso_hom_π]
    rw [← Category.assoc]
    erw [(adicDatumScalar_exists W
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }).exists.choose_spec n]
    rfl
  have hp' := hp
  simp only [pbcAdicProjection] at hp'
  have hs : proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of A) ≫ pbcCompletedScalar X d =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (pbcCompletedScalar Y d) ≫ completedCoefficientMap g d := by
    apply limit.hom_ext
    rintro ⟨n⟩
    change _ ≫ pbcAdicProjection X d n = _ ≫ pbcAdicProjection X d n
    rw [Category.assoc, hp]
    simp only [pbcAdicProjection, completedCoefficientMap, limit.lift_π,
      completedCoefficientComponent, completedFiniteCoefficientMap, Category.assoc]
    rw [← Functor.map_comp_assoc, hp']
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc _ (pbcLevelConstantComparison Y d n).hom
      (pbcLevelConstantComparison Y d n).inv, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (proEtaleConstantInverseImageMap_naturality g
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).symm =≫ _
  have hd : pbcCompletedScalar Y d ≫ completedCoefficientDirectImageMap g d =
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A) ≫
        (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
          (pbcCompletedScalar X d) := by
    let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
    have h := congrArg (adj.homEquiv _ _) hs
    dsimp only [adj] at h
    simpa only [Adjunction.homEquiv_unit, proEtaleConstantInverseImageMap,
      completedCoefficientDirectImageMap,
      Functor.map_comp, Category.assoc, Adjunction.unit_naturality_assoc,
      Adjunction.right_triangle_components_assoc] using h.symm
  exact hd

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcCompletedSection_directImage
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEtᵒᵖ) (b : A) :
    (completedCoefficientDirectImageMap g d).hom.app U (pbcCompletedSection Y d U b) =
      pbcCompletedSection X d ((proEtaleBaseChange g).op.obj U) b := by
  have h := congrArg (fun f ↦ f.hom.app U
    ((toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))).app U b))
    (pbcCompletedScalar_directImage g d)
  have hc := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))
    ((proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of A)))).apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange g).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  have hcU := congrArg (fun f ↦ f.app U b) hc
  change (proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
    (CommRingCat.of A)).hom.app U _ = _ at hcU
  change _ = (pbcCompletedScalar X d).hom.app
    ((proEtaleBaseChange g).op.obj U) _ at h
  exact h.trans (congrArg
    ((pbcCompletedScalar X d).hom.app ((proEtaleBaseChange g).op.obj U)) hcU)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcActualOperations_linear_aux
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (pbcActualDerivedPush g d).Additive ∧ (pbcActualDerivedPush g d).Linear A ∧
    (pbcActualCompletedPull g d).Additive ∧ (pbcActualCompletedPull g d).Linear A := by
  have hG : (completedModuleDirectImage g d).Linear A := by
    constructor
    intro M N f b
    ext U x
    change (pbcCompletedSection X d ((proEtaleBaseChange g).op.obj U) b) •
        f.val.app ((proEtaleBaseChange g).op.obj U) x =
      ((completedCoefficientDirectImageMap g d).hom.app U
        (pbcCompletedSection Y d U b)) •
        f.val.app ((proEtaleBaseChange g).op.obj U) x
    rw [pbcCompletedSection_directImage]
  let RF := (completedModuleDirectImage g d).rightDerivedFunctor
  let η := (completedModuleDirectImage g d).rightDerivedFunctorUnit
  have hRF : RF.Linear A := by
    rw [Functor.linear_iff]
    intro K r
    let γ₁ : RF ⟶ RF :=
      { app := fun L ↦ RF.map (r • 𝟙 L)
        naturality := fun L M f ↦ by
          simp only [← RF.map_comp, Linear.comp_smul, Linear.smul_comp,
            Category.comp_id, Category.id_comp] }
    let γ₂ : RF ⟶ RF :=
      { app := fun L ↦ r • 𝟙 (RF.obj L)
        naturality := fun L M f ↦ by simp }
    have heq : γ₁ = γ₂ := by
      apply Functor.rightDerived_ext RF η
        (HomotopyCategory.quasiIso _ (.up ℤ)) RF
      ext L
      have hn := η.naturality (r • 𝟙 L)
      change η.app L ≫ RF.map (r • 𝟙 (DerivedCategory.Qh.obj L)) =
        η.app L ≫ (r • 𝟙 (RF.obj (DerivedCategory.Qh.obj L)))
      have hQ : DerivedCategory.Qh.map (r • 𝟙 L) =
          r • 𝟙 (DerivedCategory.Qh.obj L) := by
        rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
      have hT : ((completedModuleDirectImage g d).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh).map (r • 𝟙 L) = r • 𝟙 _ := by
        rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
      change ((completedModuleDirectImage g d).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh).map (r • 𝟙 L) ≫ η.app L =
        η.app L ≫ RF.map (DerivedCategory.Qh.map (r • 𝟙 L)) at hn
      rw [hQ, hT, Linear.smul_comp, Category.id_comp] at hn
      rw [Linear.comp_smul]
      exact hn.symm.trans (congrArg (fun z ↦ r • z) (Category.comp_id (η.app L))).symm
    exact congrArg (fun γ : RF ⟶ RF ↦ γ.app K) heq
  have hRFAdd : RF.Additive :=
    Functor.additive_of_iso
      (completedModuleDirectImage g d).rightDerivedFunctorIsoKInjectives.symm
  have hPullAdd : (pbcActualDerivedPull g d).Additive :=
    (pbcActualDerivedAdjunction g d).left_adjoint_additive
  have hPull : (pbcActualDerivedPull g d).Linear A :=
    (pbcActualDerivedAdjunction g d).left_adjoint_linear
  let I := ObjectProperty.ι (PbcIsIntrinsicallyComplete X d)
  have hReflect : I.leftAdjoint.Linear A :=
    (Adjunction.ofIsRightAdjoint I).left_adjoint_linear
  have hReflectAdd : I.leftAdjoint.Additive :=
    (Adjunction.ofIsRightAdjoint I).left_adjoint_additive
  refine ⟨inferInstance, hRF, ?_, ?_⟩
  · change (pbcActualDerivedPull g d ⋙ I.leftAdjoint ⋙ I).Additive
    infer_instance
  · change (pbcActualDerivedPull g d ⋙ I.leftAdjoint ⋙ I).Linear A
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual direct image and completed pullback retain constant coefficient scalars. -/
theorem pbcActualOperations_linear :
    (pbcActualDerivedPush g (pbcIntegralDatum l E)).Additive ∧
    (pbcActualDerivedPush g (pbcIntegralDatum l E)).Linear (PbcIntegralRing l E) ∧
    (pbcActualCompletedPull g (pbcIntegralDatum l E)).Additive ∧
    (pbcActualCompletedPull g (pbcIntegralDatum l E)).Linear (PbcIntegralRing l E) := by
  exact pbcActualOperations_linear_aux g (pbcIntegralDatum l E)

/-- Additivity of actual derived direct image. -/
instance pbcActualPush_additive : (pbcActualDerivedPush g (pbcIntegralDatum l E)).Additive :=
  (pbcActualOperations_linear l E g).1

/-- Constant scalar linearity of actual derived direct image. -/
instance pbcActualPush_linear :
    (pbcActualDerivedPush g (pbcIntegralDatum l E)).Linear (PbcIntegralRing l E) :=
  (pbcActualOperations_linear l E g).2.1

/-- Additivity of actual completed pullback. -/
instance pbcActualCompletedPull_additive :
    (pbcActualCompletedPull g (pbcIntegralDatum l E)).Additive :=
  (pbcActualOperations_linear l E g).2.2.1

/-- Constant scalar linearity of actual completed pullback. -/
instance pbcActualCompletedPull_linear :
    (pbcActualCompletedPull g (pbcIntegralDatum l E)).Linear (PbcIntegralRing l E) :=
  (pbcActualOperations_linear l E g).2.2.2

variable [IsNoetherian X] [IsNoetherian Y]
variable (dX : ∃ n : ℕ, topologicalKrullDim X ≤ n)
variable (dY : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
variable (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
variable (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))

attribute [-instance] ULift.module
attribute [local irreducible] pbcRationalScalarHom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- If the actual direct images preserve constructibility, their rational comparisons
are precisely the localized ambient mate components. No preservation is assumed
without being supplied. -/
theorem pbcScalarDirectImage_rational
    (hE : ∀ K : PbcIntegralCategory l E X dX hX,
      PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
        ((pbcActualDerivedPush g (pbcIntegralDatum l E)).obj K.obj))
    (hF : ∀ K : PbcIntegralCategory l F X dX hX,
      PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l F)
        ((pbcActualDerivedPush g (pbcIntegralDatum l F)).obj K.obj)) :
    ∃! e :
      pbcConditionalRational (pbcIntegralDatum l E)
          (pbcActualDerivedPush g (pbcIntegralDatum l E)) hE (pbcUniformizer l E) ⋙
        pbcRationalScalarExtension l E F i Y dY hY ≅
      pbcRationalScalarExtension l E F i X dX hX ⋙
        pbcConditionalRational (pbcIntegralDatum l F)
          (pbcActualDerivedPush g (pbcIntegralDatum l F)) hF (pbcUniformizer l F),
      ∀ K : PbcRationalDerivedCategory l E X dX hX,
        HEq (e.hom.app K)
          ((pbcRationalization Y (pbcIntegralDatum l F) (pbcUniformizer l F)).map
            (ObjectProperty.homMk
              (X := (pbcEmbeddingIntegralTensor l E F i Y dY hY).obj
                ((pbcConditionalIntegral (pbcIntegralDatum l E)
                  (pbcActualDerivedPush g (pbcIntegralDatum l E)) hE).obj K.obj))
              (Y := (pbcConditionalIntegral (pbcIntegralDatum l F)
                (pbcActualDerivedPush g (pbcIntegralDatum l F)) hF).obj
                  ((pbcEmbeddingIntegralTensor l E F i X dX hX).obj K.obj))
              ((pbcScalarDirectImageIso l E F i g).hom.app K.obj.obj))) := by
  let HE := pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualDerivedPush g (pbcIntegralDatum l E)) hE
  let HF := pbcConditionalIntegral (pbcIntegralDatum l F)
    (pbcActualDerivedPush g (pbcIntegralDatum l F)) hF
  let IX := pbcEmbeddingIntegralTensor l E F i X dX hX
  let IY := pbcEmbeddingIntegralTensor l E F i Y dY hY
  let Q := pbcRationalization Y (pbcIntegralDatum l F) (pbcUniformizer l F)
  let α : HE ⋙ IY ≅ IX ⋙ HF :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk
      (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l F))
        ((pbcScalarDirectImageIso l E F i g).app K.obj)) (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact (pbcScalarDirectImageIso l E F i g).hom.naturality f.hom)
  let e := NatIso.ofComponents
    (fun K : PbcRationalDerivedCategory l E X dX hX ↦ Q.mapIso (α.app K.obj))
    (F := pbcConditionalRational (pbcIntegralDatum l E)
      (pbcActualDerivedPush g (pbcIntegralDatum l E)) hE (pbcUniformizer l E) ⋙
        pbcRationalScalarExtension l E F i Y dY hY)
    (G := pbcRationalScalarExtension l E F i X dX hX ⋙
      pbcConditionalRational (pbcIntegralDatum l F)
        (pbcActualDerivedPush g (pbcIntegralDatum l F)) hF (pbcUniformizer l F))
    (fun {K L} f ↦ by
      change pbcRationalScalarHom l E F i Y dY hY (HE.obj K.obj) (HE.obj L.obj)
          (ScalarLocalization.transportHom _ _ HE K.obj L.obj f) ≫
          Q.map (α.hom.app L.obj) =
        Q.map (α.hom.app K.obj) ≫
          ScalarLocalization.transportHom _ _ HF (IX.obj K.obj) (IX.obj L.obj)
            (pbcRationalScalarHom l E F i X dX hX K.obj L.obj f)
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        simp only [ScalarLocalization.transportHom, LinearMap.baseChange_tmul,
          CategoryTheory.Functor.mapLinearMap_apply]
        rw [pbcRationalScalarHom_tmul, pbcRationalScalarHom_tmul]
        simp only [LinearMap.baseChange_tmul,
          CategoryTheory.Functor.mapLinearMap_apply]
        change ScalarLocalization.composition _ _ _ _ _ _
            ((1 : Localization.Away (pbcUniformizer l F)) ⊗ₜ[PbcIntegralRing l F]
              α.hom.app L.obj) (_ ⊗ₜ[PbcIntegralRing l F] IY.map (HE.map f)) =
          ScalarLocalization.composition _ _ _ _ _ _
            (_ ⊗ₜ[PbcIntegralRing l F] HF.map (IX.map f))
            ((1 : Localization.Away (pbcUniformizer l F)) ⊗ₜ[PbcIntegralRing l F]
              α.hom.app K.obj)
        rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul]
        simp only [one_mul, mul_one]
        exact congrArg (fun z ↦
          (pbcRationalCoefficientEquiv l F).symm (i (pbcRationalCoefficientEquiv l E a))
            ⊗ₜ[PbcIntegralRing l F] z) (α.hom.naturality f)
      | add f g hf hg =>
        simp only [_root_.map_add, Preadditive.add_comp, hf, hg]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm)
  refine ⟨e, fun K ↦ HEq.rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  ext K
  exact eq_of_heq (he' K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Under the two actual preservation hypotheses, the completed-pullback comparison
also descends with its specified localized components. -/
theorem pbcScalarCompletedPull_rational
    (hE : ∀ K : PbcIntegralCategory l E Y dY hY,
      PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj))
    (hF : ∀ K : PbcIntegralCategory l F Y dY hY,
      PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l F)
        ((pbcActualCompletedPull g (pbcIntegralDatum l F)).obj K.obj)) :
    ∃! e :
      pbcRationalScalarExtension l E F i Y dY hY ⋙
        pbcConditionalRational (pbcIntegralDatum l F)
          (pbcActualCompletedPull g (pbcIntegralDatum l F)) hF (pbcUniformizer l F) ≅
      pbcConditionalRational (pbcIntegralDatum l E)
          (pbcActualCompletedPull g (pbcIntegralDatum l E)) hE (pbcUniformizer l E) ⋙
        pbcRationalScalarExtension l E F i X dX hX,
      ∀ K : PbcRationalDerivedCategory l E Y dY hY,
        HEq (e.hom.app K)
          ((pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)).map
            (ObjectProperty.homMk
              (X := (pbcConditionalIntegral (pbcIntegralDatum l F)
                (pbcActualCompletedPull g (pbcIntegralDatum l F)) hF).obj
                  ((pbcEmbeddingIntegralTensor l E F i Y dY hY).obj K.obj))
              (Y := (pbcEmbeddingIntegralTensor l E F i X dX hX).obj
                ((pbcConditionalIntegral (pbcIntegralDatum l E)
                  (pbcActualCompletedPull g (pbcIntegralDatum l E)) hE).obj K.obj))
              ((pbcScalarCompletedPullIso l E F i g).hom.app K.obj.obj))) := by
  let HE := pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualCompletedPull g (pbcIntegralDatum l E)) hE
  let HF := pbcConditionalIntegral (pbcIntegralDatum l F)
    (pbcActualCompletedPull g (pbcIntegralDatum l F)) hF
  let IX := pbcEmbeddingIntegralTensor l E F i Y dY hY
  let IY := pbcEmbeddingIntegralTensor l E F i X dX hX
  let Q := pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)
  let α : HE ⋙ IY ≅ IX ⋙ HF :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk
      (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l F))
        ((pbcScalarCompletedPullIso l E F i g).symm.app K.obj)) (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact (pbcScalarCompletedPullIso l E F i g).inv.naturality f.hom)
  let e := NatIso.ofComponents
    (fun K : PbcRationalDerivedCategory l E Y dY hY ↦ Q.mapIso (α.app K.obj))
    (F := pbcConditionalRational (pbcIntegralDatum l E)
      (pbcActualCompletedPull g (pbcIntegralDatum l E)) hE (pbcUniformizer l E) ⋙
        pbcRationalScalarExtension l E F i X dX hX)
    (G := pbcRationalScalarExtension l E F i Y dY hY ⋙
      pbcConditionalRational (pbcIntegralDatum l F)
        (pbcActualCompletedPull g (pbcIntegralDatum l F)) hF (pbcUniformizer l F))
    (fun {K L} f ↦ by
      change pbcRationalScalarHom l E F i X dX hX (HE.obj K.obj) (HE.obj L.obj)
          (ScalarLocalization.transportHom _ _ HE K.obj L.obj f) ≫
          Q.map (α.hom.app L.obj) =
        Q.map (α.hom.app K.obj) ≫
          ScalarLocalization.transportHom _ _ HF (IX.obj K.obj) (IX.obj L.obj)
            (pbcRationalScalarHom l E F i Y dY hY K.obj L.obj f)
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        simp only [ScalarLocalization.transportHom, LinearMap.baseChange_tmul,
          CategoryTheory.Functor.mapLinearMap_apply]
        rw [pbcRationalScalarHom_tmul, pbcRationalScalarHom_tmul]
        simp only [LinearMap.baseChange_tmul,
          CategoryTheory.Functor.mapLinearMap_apply]
        change ScalarLocalization.composition _ _ _ _ _ _
            ((1 : Localization.Away (pbcUniformizer l F)) ⊗ₜ[PbcIntegralRing l F]
              α.hom.app L.obj) (_ ⊗ₜ[PbcIntegralRing l F] IY.map (HE.map f)) =
          ScalarLocalization.composition _ _ _ _ _ _
            (_ ⊗ₜ[PbcIntegralRing l F] HF.map (IX.map f))
            ((1 : Localization.Away (pbcUniformizer l F)) ⊗ₜ[PbcIntegralRing l F]
              α.hom.app K.obj)
        rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul]
        simp only [one_mul, mul_one]
        exact congrArg (fun z ↦
          (pbcRationalCoefficientEquiv l F).symm (i (pbcRationalCoefficientEquiv l E a))
            ⊗ₜ[PbcIntegralRing l F] z) (α.hom.naturality f)
      | add f g hf hg =>
        simp only [_root_.map_add, Preadditive.add_comp, hf, hg]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm)
  refine ⟨e.symm, fun K ↦ HEq.rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  ext K
  exact eq_of_heq (he' K)
end ConditionalOperations
end AlgebraicGeometry.Scheme
