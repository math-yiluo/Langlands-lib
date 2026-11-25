/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteComparisonUnit
import all WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison

/-! # Extension from the unit finite comparison formula

The normalized unit calculation of the finite comparison formula extends by scalar linearity
to all middle finite coefficients.

## References

* Stacks Project, Tags 03EK and 03EL, Step 4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

section TensorLinearity
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

private theorem rawTensor_mul (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (a b : S.obj.obj U) (x : M.val.obj U) :
    (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
        ((a * b) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
      a • (show (SheafOfModules.changeOfRings φ M).val.obj U from
        (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
          (b ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf φ M)
  have ht := (ModuleCat.ExtendScalars.smul_tmul (φ.hom.app U).hom
    (M := M.val.obj U) a b x).symm
  have hη := (η.app U).hom.map_smul a (b ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  with_unfolding_all
    exact (congrArg (fun z ↦ (η.app U) z) ht).trans hη

private theorem rawTensor_smul (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (b : S.obj.obj U) (a : R.obj.obj U) (x : M.val.obj U) :
    (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
        (b ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] (a • x)) =
      (φ.hom.app U a) • (show (SheafOfModules.changeOfRings φ M).val.obj U from
        (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
          (b ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) := by
  rw [← TensorProduct.smul_tmul]
  exact rawTensor_mul φ M U (φ.hom.app U a) b x

end TensorLinearity

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

private theorem reductionTensor_smul (n : ℕ) (M : integralTowerModules l E Y)
    (U : Y.ProEtᵒᵖ) (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj U)
    (x : M.val.obj U) :
    unrestrictedIntegralTensorSection l E Y n M U a x =
      a • unrestrictedIntegralTensorSection l E Y n M U 1 x := by
  have h := rawTensor_mul (completedIntegralCommRingProjectionUnrestricted l E Y n)
    M U a 1 x
  rw [mul_one] at h
  unfold unrestrictedIntegralTensorSection
  rw [h]
  exact ((eqToHom ((scalarReductionExistence l E Y n).choose_spec.choose M).symm).val.app
    U).hom.map_smul _ _

private theorem finitePure_smul (W : Scheme.{t}) (n : ℕ)
    (M : integralOperationsFiniteModules l E W n) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U)
    (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : M.val.obj U) :
    finitePure l E L ι W n M U s (a • x) =
      ((integralScalarQuotientSheafMap l E L ι W n).hom.app U a) •
        finitePure l E L ι W n M U s x := by
  unfold finitePure
  erw [rawTensor_smul (integralScalarQuotientSheafMap l E L ι W n) M U s a x]
  exact ((eqToHom ((finiteChangeData l E L ι W n).obj_eq M).symm).val.app U).hom.map_smul
    _ _

private theorem scalarTensor_mul (n : ℕ) (M : integralTowerModules l E Y)
    (U : Y.ProEtᵒᵖ) (a b : (integralCoefficientCommRingSheaf l L Y n).obj.obj U)
    (x : M.val.obj U) :
    integralScalarTensorSection l E L ι Y n M U (a * b) x =
      a • integralScalarTensorSection l E L ι Y n M U b x := by
  unfold integralScalarTensorSection
  erw [rawTensor_mul (integralScalarRho l E L ι Y n) M U a b x]
  exact (((integralScalarReductionIso l E L ι Y n).inv.app M).val.app U).hom.map_smul _ _

private theorem finiteScalar_transport (n : ℕ) (U : X.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U))) :
    (inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U)
        ((integralScalarQuotientSheafMap l E L ι X n).hom.app (op U)
          ((inverseImageFiniteCoefficientMap l E g n).hom.app (op U) a)) =
      (integralScalarQuotientSheafMap l E L ι Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)) a := by
  have h := constantMap_naturality g (CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
      ((integralScalarQuotientMap l E L ι n).comp
        (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))
  have hx := congrArg (fun f ↦ f.hom.app (op U) a) h
  change (inverseImageFiniteCoefficientMap l L g n).hom.app (op U)
      ((integralScalarQuotientSheafMap l E L ι Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)) a) =
    (integralScalarQuotientSheafMap l E L ι X n).hom.app (op U)
      ((inverseImageFiniteCoefficientMap l E g n).hom.app (op U) a) at hx
  rw [← hx]
  exact congrArg (fun f ↦ f.hom.app (op U)
    ((integralScalarQuotientSheafMap l E L ι Y n).hom.app
      (op ((proEtaleIsoPostcompose g).obj U)) a))
    (IsIso.hom_inv_id (inverseImageFiniteCoefficientMap l L g n))

/-- Scalar linearity extends the unit calculation to every pure middle tensor. -/
theorem finite_formula_of_unit
    (bfin : ∀ n : ℕ,
      (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (hunit : FiniteFormulaUnit l E L ι g bfin) :
    FiniteFormula l E L ι g bfin := by
  intro n P i U s a x
  let V := op ((proEtaleIsoPostcompose g).obj U)
  let M := (inverseImageFiniteModules l E g n).obj
    ((unrestrictedIntegralReductionFunctor l E Y n).obj (P.obj.X i))
  let aX := (inverseImageFiniteCoefficientMap l E g n).hom.app (op U) a
  let y : M.val.obj (op U) :=
    unrestrictedIntegralTensorSection l E Y n (P.obj.X i) V 1 x
  have ha : (show M.val.obj (op U) from
      unrestrictedIntegralTensorSection l E Y n (P.obj.X i) V a x) = aX • y := by
    change unrestrictedIntegralTensorSection l E Y n (P.obj.X i) V a x =
      (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U) aX •
        unrestrictedIntegralTensorSection l E Y n (P.obj.X i) V 1 x
    have hi := congrArg (fun f ↦ f.hom.app (op U) a)
      (IsIso.hom_inv_id (inverseImageFiniteCoefficientMap l E g n))
    change (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U) aX = a at hi
    rw [hi]
    exact reductionTensor_smul l E n (P.obj.X i) V a x
  let f := ((bfin n).hom.app P).f i
  have hu := hunit n P i U s x
  simp only [map_one, mul_one] at hu
  change f.val.app (op U) (finitePure l E L ι X n M (op U) s y) =
    integralScalarTensorSection l E L ι Y n (P.obj.X i) V
      ((inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) s) x at hu
  change f.val.app (op U) (finitePure l E L ι X n M (op U) s
      (unrestrictedIntegralTensorSection l E Y n (P.obj.X i) V a x)) = _
  have hp := (congrArg (finitePure l E L ι X n M (op U) s) ha).trans
    (finitePure_smul l E L ι X n M (op U) s aX y)
  refine (congrArg (fun z ↦ f.val.app (op U) z) hp).trans ?_
  refine ((f.val.app (op U)).hom.map_smul _ _).trans ?_
  erw [hu]
  change (inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U)
      ((integralScalarQuotientSheafMap l E L ι X n).hom.app (op U) aX) •
        integralScalarTensorSection l E L ι Y n (P.obj.X i) V
          ((inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) s) x = _
  rw [finiteScalar_transport l E L ι g n U a]
  rw [← scalarTensor_mul]
  exact congrArg (fun z ↦ integralScalarTensorSection l E L ι Y n (P.obj.X i) V z x)
    (mul_comm _ _)

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
