import Langlands.Global.RankinSelberg.ComplexGodementContinuedSmooth
import Langlands.Global.RankinSelberg.ComplexGodementKFinite

/-! # Compact support and finite unitary orbits under Godement test derivatives -/

noncomputable section
open Set
open scoped Classical Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean (unitaryCompact)
open Langlands.Analysis.SchwartzMatrixNorm (OperatorSchwartz EntrySchwartz operatorToEntry)
open ComplexGodementAddedCharacter (rightTest rightTest_apply)
open ComplexGodementContinuedSmooth (testDerivative)

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "KUnit" => unitaryCompact ℂ (r + 1 + 1)
local notation "Square" => Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Test" => EntrySchwartz (r + 1) (r + 1 + 1)
local notation "OpTest" => OperatorSchwartz (r + 1) (r + 1 + 1)

/-- The right matrix derivative in entrywise Schwartz coordinates. -/
theorem testDerivative_apply (Φ : Test) (X : Square) (Y : Rect) :
    testDerivative Φ X Y = fderiv ℝ (Φ : Rect → ℂ) Y (Y * X) := rfl

/-- The reverse norm change for rectangular Schwartz functions. -/
def entryToOperator {m n : ℕ} (Φ : EntrySchwartz m n) : OperatorSchwartz m n :=
  @SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Matrix (Fin m) (Fin n) ℂ) (Matrix (Fin m) (Fin n) ℂ) ℂ
    Matrix.normedAddCommGroup Matrix.normedSpace _ _ _
    Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace _
    (ContinuousLinearEquiv.refl ℝ (Matrix (Fin m) (Fin n) ℂ)) Φ

@[simp] theorem entryToOperator_apply {m n : ℕ} (Φ : EntrySchwartz m n) (Y : Matrix (Fin m) (Fin n) ℂ) :
    entryToOperator Φ Y = Φ Y := rfl

/-- The same translated-test derivative in the norm of the standard-section test. -/
def operatorTestDerivative (Φ : OpTest) (X : Square) : OpTest :=
  entryToOperator (testDerivative (operatorToEntry Φ) X)

@[simp] theorem operatorToEntry_operatorTestDerivative (Φ : OpTest) (X : Square) :
    operatorToEntry (operatorTestDerivative Φ X) = testDerivative (operatorToEntry Φ) X :=
  SchwartzMap.ext fun _ => rfl

private theorem tsupport_testDerivative_subset (Φ : Test) (X : Square) :
    tsupport (testDerivative Φ X) ⊆ tsupport Φ := by
  apply closure_minimal _ (isClosed_tsupport Φ)
  intro Y hY
  by_contra h
  have hz : fderiv ℝ (Φ : Rect → ℂ) Y = 0 := fderiv_of_notMem_tsupport ℝ h
  exact hY (by rw [testDerivative_apply, hz]; rfl)

/-- Differentiating the test preserves its compact support and full-rank support condition. -/
theorem operatorTestDerivative_support (Φ : OpTest) (X : Square)
    (hΦ : HasCompactSupport Φ) (hfull : ∀ Y ∈ tsupport Φ, HasFullRowRank Y) :
    HasCompactSupport (operatorTestDerivative Φ X) ∧
      ∀ Y ∈ tsupport (operatorTestDerivative Φ X), HasFullRowRank Y := by
  have hsub : tsupport (operatorTestDerivative Φ X) ⊆ tsupport Φ :=
    tsupport_testDerivative_subset (operatorToEntry Φ) X
  exact ⟨hΦ.of_isClosed_subset (isClosed_tsupport _) hsub, fun Y hY => hfull Y (hsub hY)⟩

/-- Translating a derivative conjugates its direction by the translating matrix. -/
theorem rightTest_testDerivative (k : G) (Φ : Test) (X : Square) :
    rightTest k (testDerivative Φ X) = testDerivative (rightTest k Φ) (k.val * X * k⁻¹.val) := by
  apply SchwartzMap.ext
  intro Y
  let R : Rect →L[ℝ] Rect := (mulRightLinearMap (Fin (r + 1)) ℝ k.val).toContinuousLinearMap
  have h := (Φ.hasFDerivAt (Y * k.val)).comp Y R.hasFDerivAt
  have hd : HasFDerivAt (rightTest k Φ : Rect → ℂ)
      ((fderiv ℝ (Φ : Rect → ℂ) (Y * k.val)).comp R) Y := h
  rw [rightTest_apply, testDerivative_apply, testDerivative_apply, hd.fderiv]
  change fderiv ℝ (Φ : Rect → ℂ) (Y * k.val) (Y * k.val * X) =
    fderiv ℝ (Φ : Rect → ℂ) (Y * k.val) ((Y * (k.val * X * k⁻¹.val)) * k.val)
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

private def derivativeTestLinear (X : Square) : Test →ₗ[ℂ] Test where
  toFun Φ := testDerivative Φ X
  map_add' Φ Ψ := by
    apply SchwartzMap.ext
    intro Y
    change fderiv ℝ ((Φ : Rect → ℂ) + (Ψ : Rect → ℂ)) Y (Y * X) =
      fderiv ℝ (Φ : Rect → ℂ) Y (Y * X) + fderiv ℝ (Ψ : Rect → ℂ) Y (Y * X)
    rw [fderiv_add (Φ.hasFDerivAt Y).differentiableAt (Ψ.hasFDerivAt Y).differentiableAt]
    rfl
  map_smul' c Φ := by
    apply SchwartzMap.ext
    intro Y
    change fderiv ℝ (c • (Φ : Rect → ℂ)) Y (Y * X) = c • fderiv ℝ (Φ : Rect → ℂ) Y (Y * X)
    rw [fderiv_const_smul (Φ.hasFDerivAt Y).differentiableAt c]
    rfl

private def testToFun : Test →ₗ[ℂ] (Rect → ℂ) where
  toFun Φ := Φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem testToFun_inj : Function.Injective (testToFun (r := r)) :=
  fun _ _ h => SchwartzMap.ext (congrFun h)

set_option maxHeartbeats 700000 in
/-- Applying a right matrix derivative to a compact-finite Schwartz test preserves compact finiteness. -/
theorem finiteSpan_testDerivative (Φ : Test) (X : Square)
    (hΦ : FiniteDimensional ℂ (Submodule.span ℂ (range fun k : KUnit => translateTest k.val Φ))) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : KUnit => translateTest k.val (testDerivative Φ X))) := by
  let S := Submodule.span ℂ (range fun k : KUnit => rightTest k.val Φ)
  have hS : S.map testToFun = Submodule.span ℂ (range fun k : KUnit => translateTest k.val Φ) := by
    rw [Submodule.map_span, ← range_comp]
    rfl
  have : FiniteDimensional ℂ (S.map testToFun) := hS.symm ▸ hΦ
  let e := Submodule.equivMapOfInjective testToFun testToFun_inj S
  have : FiniteDimensional ℂ S := FiniteDimensional.of_injective e.toLinearMap e.injective
  let b := Module.finBasis ℝ Square
  let H := ⨆ i : Fin (Module.finrank ℝ Square), S.map (derivativeTestLinear (b i))
  have : FiniteDimensional ℂ H := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := H.map testToFun)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨rightTest k.val (testDerivative Φ X), ?_, rfl⟩
  let Y := k.val.val * X * k.val⁻¹.val
  let v := rightTest k.val Φ
  have hv : v ∈ S := Submodule.subset_span ⟨k, rfl⟩
  rw [rightTest_testDerivative]
  change testDerivative v Y ∈ H
  have hb := congrArg (testDerivative v) (b.sum_repr Y)
  simp only [map_sum, map_smul] at hb
  rw [← hb]
  refine Submodule.sum_mem H fun i _ => ?_
  have hi : testDerivative v (b i) ∈ H :=
    (le_iSup (fun i : Fin (Module.finrank ℝ Square) => S.map (derivativeTestLinear (b i))) i)
      ⟨v, hv, rfl⟩
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact H.smul_mem _ hi

variable (r) in
/-- Right matrix differentiation preserves the compact full-rank finite test class used by
compact Godement spanning. -/
def ComplexGodementTestDerivativeStatement : Prop :=
  ∀ (Φ : OpTest) (X : Square), HasCompactSupport Φ → (∀ Y ∈ tsupport Φ, HasFullRowRank Y) →
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : KUnit => translateTest k.val Φ)) →
    HasCompactSupport (operatorTestDerivative Φ X) ∧
      (∀ Y ∈ tsupport (operatorTestDerivative Φ X), HasFullRowRank Y) ∧
      FiniteDimensional ℂ
        (Submodule.span ℂ (range fun k : KUnit => translateTest k.val (operatorTestDerivative Φ X)))

theorem complexGodementTestDerivative : ComplexGodementTestDerivativeStatement r := by
  intro Φ X hΦ hfull hfinite
  obtain ⟨hc, hf⟩ := operatorTestDerivative_support Φ X hΦ hfull
  exact ⟨hc, hf, finiteSpan_testDerivative (operatorToEntry Φ) X hfinite⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
