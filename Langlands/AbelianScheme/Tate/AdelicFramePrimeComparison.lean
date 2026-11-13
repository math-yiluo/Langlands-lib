import Langlands.AbelianScheme.Tate.AdelicFrameTransport
import Langlands.Shimura.PEL.ScalarExtension
import Langlands.AbelianScheme.Tate.AdelicPrimeScalars
import Langlands.Shimura.Unitary.Adelic

/-! # Actual prime extraction in local adelic-frame coordinates -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

namespace Langlands.AbelianScheme.Tate

open Langlands.Shimura Langlands.Shimura.PEL

universe u v w
variable {S : Scheme.{u}} (B : AbelianScheme S)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D]
  (i : D →ₐ[ℚ] Rationalization.End B)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Frame" => AdelicFrame B h i (Af ⊗[ℚ] V) s
local notation "TateSpace" => RationalFull B (Over.mk s)

/-- An actual tensor-algebra-linear frame also preserves the existing rational actions. -/
def adelicFrameRatLinear :
    letI := scalarExtensionAlgebraModule D V Af
    Frame → ((Af ⊗[ℚ] V) →ₗ[ℚ] TateSpace) := by
  letI := scalarExtensionAlgebraModule D V Af
  letI := finiteAdeleAlgebraModule B (Over.mk s) (fun _ => True) h i
  letI : IsScalarTower ℚ (D ⊗[ℚ] Af) (Af ⊗[ℚ] V) :=
    IsScalarTower.of_algebraMap_smul (fun q x => by
      change scalarExtensionAlgebraAction D V Af (algebraMap ℚ (D ⊗[ℚ] Af) q) x = q • x
      rw [AlgHom.commutes]
      rfl)
  letI : IsScalarTower ℚ (D ⊗[ℚ] Af) TateSpace :=
    IsScalarTower.of_algebraMap_smul (fun q x => by
      change finiteAdeleAlgebraAction B (Over.mk s) (fun _ => True) h i
        (algebraMap ℚ (D ⊗[ℚ] Af) q) x = q • x
      rw [AlgHom.commutes]
      rfl)
  intro eta
  exact eta.toLinearMap.restrictScalars ℚ

@[simp] theorem adelicFrameRatLinear_apply :
    letI := scalarExtensionAlgebraModule D V Af
    ∀ (eta : Frame) (x : Af ⊗[ℚ] V),
      adelicFrameRatLinear B h i V s eta x = eta x := by
  let := scalarExtensionAlgebraModule D V Af
  intros
  rfl

/-- The finite-adelic scalar in a pure tensor acts through the actual frame. -/
theorem adelicFrame_tmul :
    letI := scalarExtensionAlgebraModule D V Af
    ∀ (eta : Frame) (a : Af) (x : V),
      eta (a ⊗ₜ[ℚ] x) =
        finiteAdeleAction B (Over.mk s) (fun _ => True) h a (eta (1 ⊗ₜ[ℚ] x)) := by
  let := scalarExtensionAlgebraModule D V Af
  let := finiteAdeleAlgebraModule B (Over.mk s) (fun _ => True) h i
  intro eta a x
  have heq := eta.map_smul ((1 : D) ⊗ₜ[ℚ] a) ((1 : Af) ⊗ₜ[ℚ] x)
  change eta (scalarExtensionAlgebraAction D V Af
      ((1 : D) ⊗ₜ[ℚ] a) ((1 : Af) ⊗ₜ[ℚ] x)) =
    finiteAdeleAlgebraAction B (Over.mk s) (fun _ => True) h i
      ((1 : D) ⊗ₜ[ℚ] a) (eta ((1 : Af) ⊗ₜ[ℚ] x)) at heq
  simpa only [scalarExtensionAlgebraAction_tmul, mul_one, one_smul,
    finiteAdeleAlgebraAction_tmul, map_one, Module.End.one_apply] using heq

/-- Extend prime extraction of the rational vectors in a frame to local coefficients. -/
def localFrameToPrime (v : Global.FinitePlace ℚ) :
    letI := scalarExtensionAlgebraModule D V Af
    Frame → ((Global.FiniteCompletion ℚ v) ⊗[ℚ] V →ₗ[ℚ]
      PrimeAdic.Rational B (Over.mk s) (Rat.HeightOneSpectrum.primesEquiv v).val) := by
  let := scalarExtensionAlgebraModule D V Af
  intro eta
  let L : V →ₗ[ℚ]
      PrimeAdic.Rational B (Over.mk s) (Rat.HeightOneSpectrum.primesEquiv v).val :=
    (PrimeComparison.rationalFullToPrime B (Over.mk s)
      (Rat.HeightOneSpectrum.primesEquiv v).val).comp
      ((adelicFrameRatLinear B h i V s eta).comp (TensorProduct.mk ℚ Af V 1))
  exact TensorProduct.lift {
    toFun c := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v c • L
    map_add' c d := by rw [_root_.map_add, add_smul]
    map_smul' q c := by
      ext x
      simp [map_smul, smul_assoc] }

@[simp] theorem localFrameToPrime_tmul (v : Global.FinitePlace ℚ) :
    letI := scalarExtensionAlgebraModule D V Af
    ∀ (eta : Frame) (c : Global.FiniteCompletion ℚ v) (x : V),
      localFrameToPrime B h i V s v eta (c ⊗ₜ[ℚ] x) =
        Rat.HeightOneSpectrum.adicCompletion.padicEquiv v c •
          PrimeComparison.rationalFullToPrime B (Over.mk s)
            (Rat.HeightOneSpectrum.primesEquiv v).val (eta (1 ⊗ₜ[ℚ] x)) := by
  let := scalarExtensionAlgebraModule D V Af
  intros
  rfl

/-- Actual prime extraction factors through evaluation of the frame coefficients. -/
theorem localFrameToPrime_evaluation (v : Global.FinitePlace ℚ) :
    letI := scalarExtensionAlgebraModule D V Af
    ∀ (eta : Frame) (x : Af ⊗[ℚ] V),
      localFrameToPrime B h i V s v eta
          (TensorProduct.map (AlgebraInvolution.finiteEvaluation v).toLinearMap
            (LinearMap.id : V →ₗ[ℚ] V) x) =
        PrimeComparison.rationalFullToPrime B (Over.mk s)
          (Rat.HeightOneSpectrum.primesEquiv v).val (eta x) := by
  let := scalarExtensionAlgebraModule D V Af
  intro eta x
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [TensorProduct.map_tmul, localFrameToPrime_tmul, LinearMap.id_apply,
      adelicFrame_tmul B h i V s eta a x,
      PrimeComparison.rationalFullToPrime_finiteAdeleAction]
    rfl
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, _root_.map_add, _root_.map_add, hx, hy]

/-- Evaluating inverse-frame coordinates recovers the actual selected prime coordinate. -/
theorem localFrameToPrime_inverseFrame (v : Global.FinitePlace ℚ) :
    letI := scalarExtensionAlgebraModule D V Af
    ∀ (eta : Frame) (y : TateSpace),
      localFrameToPrime B h i V s v eta
          (TensorProduct.map (AlgebraInvolution.finiteEvaluation v).toLinearMap
            (LinearMap.id : V →ₗ[ℚ] V) (eta.symm y)) =
        PrimeComparison.rationalFullToPrime B (Over.mk s)
          (Rat.HeightOneSpectrum.primesEquiv v).val y := by
  let := scalarExtensionAlgebraModule D V Af
  intro eta y
  rw [localFrameToPrime_evaluation, LinearEquiv.apply_symm_apply]

end Langlands.AbelianScheme.Tate
