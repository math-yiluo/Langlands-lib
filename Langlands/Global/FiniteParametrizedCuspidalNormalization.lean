import Langlands.Global.FiniteParametrizedBlockInduction
import Langlands.Automorphic.HeckeTwist.OperatorTwistFiniteComparison
import Langlands.Automorphic.OperatorSubquotient
import Mathlib.Algebra.BigOperators.Pi

/-! Inverse half-modulus twists for the actual cuspidal blocks of finite induction. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.Representation
open scoped BigOperators NNReal

universe u uV uW

namespace Langlands.Global.FiniteParametrizedBlockInduction

open GeneralLinear Automorphic

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

private def classCoordinate (i : Fin B.length) :
    (Fin B.length → IdeleClasses F) →ₜ* IdeleClasses F where
  toFun a := a i
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_apply i

private def classCoordinateNorm (i : Fin B.length) :
    (Fin B.length → IdeleClasses F) →ₜ* ℝ≥0ˣ :=
  (IdeleAbsoluteValue.ideleClass F).comp (classCoordinate F B i)

private theorem classCoordinateNorm_apply (i : Fin B.length) (a : Fin B.length → IdeleClasses F) :
    classCoordinateNorm F B i a = IdeleAbsoluteValue.ideleClass F (a i) := rfl

private def classModulusHom : (Fin B.length → IdeleClasses F) →* ℝ≥0ˣ :=
  ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (classCoordinateNorm F B i).toMonoidHom ^ B.size j /
      (classCoordinateNorm F B j).toMonoidHom ^ B.size i

private theorem classModulusHom_apply (a : Fin B.length → IdeleClasses F) :
    classModulusHom F B a = ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
      IdeleAbsoluteValue.ideleClass F (a i) ^ B.size j /
        IdeleAbsoluteValue.ideleClass F (a j) ^ B.size i := by
  simp [classModulusHom, classCoordinateNorm_apply]

private def classModulus : (Fin B.length → IdeleClasses F) →ₜ* ℝ≥0ˣ where
  toMonoidHom := classModulusHom F B
  continuous_toFun := by
    change Continuous (fun a => classModulusHom F B a)
    simp_rw [classModulusHom_apply, div_eq_mul_inv]
    exact continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ =>
      ((classCoordinateNorm F B i).continuous.pow _).mul
        ((classCoordinateNorm F B j).continuous.pow _).inv

private def classPositiveHalf : (Fin B.length → IdeleClasses F) →ₜ* ℝ≥0ˣ where
  toMonoidHom := Jacquet.positiveHalfCharacter (H := Fin B.length → IdeleClasses F)
    (classModulus F B).toMonoidHom
  continuous_toFun :=
    (NNReal.continuous_sqrt.units_map NNReal.sqrtHom.toMonoidHom).comp (classModulus F B).continuous

private def classHalf : (Fin B.length → IdeleClasses F) →ₜ* ℂˣ where
  toMonoidHom := Jacquet.complexCharacter (H := Fin B.length → IdeleClasses F)
    (classPositiveHalf F B).toMonoidHom
  continuous_toFun :=
    ((Complex.continuous_ofReal.comp NNReal.continuous_coe).units_map
      (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom).comp (classPositiveHalf F B).continuous

private def inverseHalfClass : (Fin B.length → IdeleClasses F) →ₜ* ℂˣ where
  toMonoidHom := (classHalf F B).toMonoidHom⁻¹
  continuous_toFun := (classHalf F B).continuous.inv

private def classSingle (i : Fin B.length) :
    IdeleClasses F →ₜ* (Fin B.length → IdeleClasses F) where
  toMonoidHom := MonoidHom.mulSingle (fun _ => IdeleClasses F) i
  continuous_toFun := by
    change Continuous (fun x => Pi.mulSingle (M := fun _ : Fin B.length => IdeleClasses F) i x)
    exact continuous_mulSingle (A := fun _ : Fin B.length => IdeleClasses F) i

/-- The inverse positive half-modulus restricted to one determinant idele class. -/
def inverseHalfBlockHeckeCharacter (i : Fin B.length) : HeckeCharacter F :=
  (inverseHalfClass F B).comp (classSingle F B i)

private theorem prod_coordinateValues {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid A]
    (e : (ι → A) →* ℂˣ) (a : ι → A) : (∏ i, e (Pi.mulSingle i (a i))) = e a := by
  calc
    _ = e (∏ i, Pi.mulSingle i (a i)) := (map_prod e _ _).symm
    _ = e a := congrArg e (Finset.univ_prod_mulSingle a)

/-- The block characters multiply to the inverse half of the full adelic Levi modulus. -/
theorem prod_inverseHalfBlockHeckeCharacter (m : AdelicBlockParabolic.FullLevi F B) :
    (∏ i, (inverseHalfBlockHeckeCharacter F B i).adelicDeterminant (B.size i) (m i)) =
      (AdelicBlockDeterminantCharacter.leviHalfCharacter F B m)⁻¹ := by
  let a := fun i => ideleClassMap F (AdelicGL.determinant F (B.size i) (m i))
  have hmod : classModulusHom F B a = AdelicBlockDeterminantCharacter.leviCharacter F B m := by
    rw [classModulusHom_apply, AdelicBlockDeterminantCharacter.leviCharacter_apply]
    simp only [a, IdeleAbsoluteValue.ideleClass_class]
    rfl
  calc
    _ = inverseHalfClass F B a := prod_coordinateValues (inverseHalfClass F B).toMonoidHom a
    _ = _ := by
      apply Units.ext
      change (↑((classHalf F B a)⁻¹) : ℂ) =
        ↑((AdelicBlockDeterminantCharacter.leviHalfCharacter F B m)⁻¹)
      have hhalf : (classHalf F B a : ℂ) =
          ((NNReal.sqrt (classModulusHom F B a : ℝ≥0) : ℝ) : ℂ) := rfl
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val,
        AdelicBlockDeterminantCharacter.coe_leviHalfCharacter, hhalf, hmod]

/-- The inverse half block twists cancel the finite parabolic half character. -/
theorem finiteHalfCharacter_mul_prod_inverseHalfBlock (p : AdelicBlockParabolic.Finite F B) :
    finiteHalfCharacter F B p *
      (∏ i, (inverseHalfBlockHeckeCharacter F B i).finiteAdelicDeterminant (B.size i)
        (B.leviProjection (FiniteAdeles F) p i)) = 1 := by
  let m := B.leviProjection (Adeles F) (AdelicBlockParabolic.ofFinite F B p)
  have hm : m = fun i => AdelicGL.ofFinite F (B.size i)
      (B.leviProjection (FiniteAdeles F) p i) := by
    change B.leviProjection (Adeles F) (AdelicBlockParabolic.pair F B 1 p) = _
    rw [AdelicBlockParabolic.leviProjection_pair, map_one]
    rfl
  have h := prod_inverseHalfBlockHeckeCharacter F B m
  have hf : (∏ i, (inverseHalfBlockHeckeCharacter F B i).finiteAdelicDeterminant (B.size i)
      (B.leviProjection (FiniteAdeles F) p i)) = (finiteHalfCharacter F B p)⁻¹ := by
    calc
      _ = ∏ i, (inverseHalfBlockHeckeCharacter F B i).adelicDeterminant (B.size i) (m i) := by
        rw [hm]
        rfl
      _ = _ := h
  rw [hf, mul_inv_cancel]

private def coefficientEquivOfBlockTwists
    {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ (FiniteAdelicGL F (B.size i)) (V i))
    (τ : ∀ i, Representation ℂ (FiniteAdelicGL F (B.size i)) (W i))
    (e : ∀ i, V i ≃ₗ[ℂ] W i)
    (he : ∀ i d x, τ i d (e i x) =
      ((inverseHalfBlockHeckeCharacter F B i).finiteAdelicDeterminant (B.size i) d : ℂ) •
        e i (ρ i d x)) :
    Representation.Equiv
      ((B.blockTensor ρ).comp (B.leviProjection (FiniteAdeles F))) (finiteCoefficient F B τ) := by
  let E := PiTensorProduct.congr e
  have hE (x : ∀ i, V i) : E (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (fun i => e i (x i)) := PiTensorProduct.congr_tprod _ _
  refine Representation.Equiv.mk E (fun p => ?_)
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  let a := B.leviProjection (FiniteAdeles F) p
  change E (B.blockTensor ρ a (PiTensorProduct.tprod ℂ x)) =
    (finiteHalfCharacter F B p : ℂ) • B.blockTensor τ a (E (PiTensorProduct.tprod ℂ x))
  rw [B.blockTensor_tprod, hE, hE, B.blockTensor_tprod]
  simp_rw [he, (PiTensorProduct.tprod ℂ).map_smul_univ, smul_smul]
  have hc : (finiteHalfCharacter F B p : ℂ) *
      (∏ i, ((inverseHalfBlockHeckeCharacter F B i).finiteAdelicDeterminant (B.size i) (a i) : ℂ)) =
        1 := by
    simpa only [Units.val_mul, Units.coe_prod, Units.val_one] using
      congrArg (fun z : ℂˣ => (z : ℂ)) (finiteHalfCharacter_mul_prod_inverseHalfBlock F B p)
  rw [hc, one_smul]

section Cuspidal

variable {F} [CompactSpace (AdeleQuotient F)] {r k : ℕ} {m : Fin k → ℕ}
  (hm : ∑ i, (m i + 1) = r + 1) (T : ∀ i, CuspidalOperatorRealization F (m i))

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup

/-- Apply the inverse half-modulus twist to each actual cuspidal realization. -/
def normalizedCuspidalBlocks : ∀ i, CuspidalOperatorRealization F (m i) :=
  fun i => (T i).heckeDeterminantTwist
    (inverseHalfBlockHeckeCharacter F ⟨k, fun j => m j + 1, fun _ => Nat.succ_pos _, hm⟩ i)

/-- The unnormalized finite parabolic action is equivalent to normalized
covariance for the actual twisted cuspidal blocks. -/
def normalizedCuspidalCoefficientEquiv :
    let B : BlockShape (r + 1) := ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
    Representation.Equiv
      ((B.blockTensor (fun i => (T i).realization.finiteRepresentation)).comp
        (B.leviProjection (FiniteAdeles F)))
      (finiteCoefficient F B (fun i => ((normalizedCuspidalBlocks hm T) i).realization.finiteRepresentation)) := by
  let B : BlockShape (r + 1) := ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
  let χ := inverseHalfBlockHeckeCharacter F B
  exact coefficientEquivOfBlockTwists F B
    (fun i => (T i).realization.finiteRepresentation)
    (fun i => ((normalizedCuspidalBlocks hm T) i).realization.finiteRepresentation)
    (fun i => ((T i).realization.heckeDeterminantTwistEquiv (χ i)).toLinearEquiv)
    (fun i d x => (T i).realization.heckeDeterminantTwistEquiv_finite (χ i) d x)

end Cuspidal
end Langlands.Global.FiniteParametrizedBlockInduction
