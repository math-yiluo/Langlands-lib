import Langlands.Automorphic.CuspidalL2.Representation
import Langlands.Global.AdelicBlockCoefficientTensor
import Langlands.Global.AdelicBlockArchimedeanNormalization

/-!
# Smooth mixed matrix evaluation of the realized Levi coefficients

An actual scalar block coefficient, with its finite Levi argument fixed,
can be evaluated smoothly on ambient archimedean matrices near any parabolic unit.
-/

noncomputable section

open scoped BigOperators Classical ContDiff Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
set_option synthInstance.maxHeartbeats 100000

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear AdelicBlockParabolic
open AdelicBlockDeterminantCharacter

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local instance (t : ℕ) : AddCommGroup (RationalInvariantFunctions F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (ContinuousRationalFunctions F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (AutomorphicForms F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (StableAutomorphicFunctions F t) := Submodule.addCommGroup _
local instance {t : ℕ} (U : OperatorRealization F t) : AddCommGroup U.Space :=
  Submodule.addCommGroup _

local notation "A" => ArchimedeanMatrix F n
local notation "μ∞" => (B.leviProjection (InfiniteAdeles F))

private def factorExtension (d : FiniteLevi F B) (i : Fin B.length) :
    (S i).Space →ₗ[ℂ] (ArchimedeanMatrix F (B.size i) → ℂ) where
  toFun v := ArchimedeanGL.coordinateExtension F (B.size i)
    (finiteSmoothSlice F (B.size i) (d i) ((S i).ambient v))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def tensorExtension (d : FiniteLevi F B) : (⨂[ℂ] i, (S i).Space) →ₗ[ℂ] (A → ℂ) :=
  (LinearMap.pi fun x : A => LinearMap.proj (fun i => archimedeanDiagonalBlock F B i x)).comp
    (indexedEvaluation (factorExtension F B S d))

/-- Fix the finite Levi argument and extend evaluation to ambient mixed block matrices. -/
def coefficientExtension (d : FiniteLevi F B) : coefficientValues F B S →ₗ[ℂ] (A → ℂ) :=
  (tensorExtension F B S d).comp (coefficientEquiv F B S).symm.toLinearMap

private theorem tensorExtension_tprod (d : FiniteLevi F B) (v : ∀ i, (S i).Space) (x : A) :
    tensorExtension F B S d (PiTensorProduct.tprod ℂ v) x =
      ∏ i, factorExtension F B S d i (v i) (archimedeanDiagonalBlock F B i x) :=
  indexedEvaluation_tprod (factorExtension F B S d) v _

private theorem tensorExtension_apply_parabolic (d : FiniteLevi F B) (a : Infinite F B)
    (t : ⨂[ℂ] i, (S i).Space) :
    tensorExtension F B S d t (archimedeanGLCoordinates F n a.val).val =
      (coefficientEquiv F B S t).val (leviPair F B (μ∞ a) d) := by
  let x := (archimedeanGLCoordinates F n a.val).val
  let m := leviPair F B (μ∞ a) d
  have hx (i : Fin B.length) : archimedeanDiagonalBlock F B i x =
      (archimedeanGLCoordinates F (B.size i) (μ∞ a i)).val := rfl
  have h : (LinearMap.proj x : (A → ℂ) →ₗ[ℂ] ℂ).comp (tensorExtension F B S d) =
      (LinearMap.proj m).comp
        ((coefficientValues F B S).subtype.comp (coefficientEquiv F B S).toLinearMap) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply, LinearEquiv.coe_coe, tensorExtension_tprod,
      coefficientEquiv_tprod_apply, hx, factorExtension, LinearMap.coe_mk, AddHom.coe_mk,
      ArchimedeanGL.coordinateExtension_apply, ContinuousMulEquiv.symm_apply_apply,
      finiteSmoothSlice_apply, blockCoefficient, OperatorRealization.evaluate_toContinuous,
      m, leviPair]
  exact LinearMap.congr_fun h t

@[simp]
theorem coefficientExtension_apply_parabolic (d : FiniteLevi F B) (a : Infinite F B)
    (v : coefficientValues F B S) :
    coefficientExtension F B S d v (archimedeanGLCoordinates F n a.val).val =
      v.val (leviPair F B (μ∞ a) d) := by
  change tensorExtension F B S d ((coefficientEquiv F B S).symm v) _ = _
  rw [tensorExtension_apply_parabolic, LinearEquiv.apply_symm_apply]

private theorem tensorExtension_contDiffAt (d : FiniteLevi F B) (a : Infinite F B)
    (t : ⨂[ℂ] i, (S i).Space) :
    ContDiffAt ℝ ∞ (tensorExtension F B S d t) (archimedeanGLCoordinates F n a.val).val := by
  let x := (archimedeanGLCoordinates F n a.val).val
  change ContDiffAt ℝ ∞ _ x
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul]
    suffices ContDiffAt ℝ ∞
        (tensorExtension F B S d (PiTensorProduct.tprod ℂ v)) x from this.const_smul c
    rw [show tensorExtension F B S d (PiTensorProduct.tprod ℂ v) =
      (fun y : A => ∏ i, factorExtension F B S d i (v i) (archimedeanDiagonalBlock F B i y))
      from funext (tensorExtension_tprod F B S d v)]
    apply contDiffAt_prod
    intro i _
    exact (ArchimedeanGL.coordinateExtension_contDiffAt F (B.size i)
      (finiteSmoothSlice F (B.size i) (d i) ((S i).ambient (v i)))
      (archimedeanGLCoordinates F (B.size i) (μ∞ a i))).comp x
        (archimedeanDiagonalBlock F B i).contDiff.contDiffAt
  | add t s ht hs =>
    rw [map_add]
    exact ht.add hs

/-- The extended coefficient evaluation is smooth at every infinite parabolic unit. -/
theorem coefficientExtension_contDiffAt (d : FiniteLevi F B) (a : Infinite F B)
    (v : coefficientValues F B S) :
    ContDiffAt ℝ ∞ (coefficientExtension F B S d v) (archimedeanGLCoordinates F n a.val).val :=
  tensorExtension_contDiffAt F B S d a ((coefficientEquiv F B S).symm v)

end Langlands.Global.AdelicBlockScalarSections
