import Langlands.Global.Factors.CuspidalBlockArchimedeanEvaluationLie
import Langlands.Global.Factors.CuspidalBlockInfiniteLieAction

/-! # Upper triangular differentiation of the full infinite compact evaluation -/

noncomputable section

open scoped Classical Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 210000

universe u

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic _root_.Langlands.Archimedean LocalFactor.Archimedean
open ArchimedeanCompactBlocks ArchimedeanGL AdelicBlockParabolic InfinitePlaceFamily NumberField

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem map_slot_with_scalar {I : Type*} [DecidableEq I]
    {A C : I → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module ℂ (C i)]
    (e : ∀ i, A i →ₗ[ℂ] C i) (p : I) (D : Module.End ℂ (A p)) (H : Module.End ℂ (C p))
    (a : ℂ) (h : (e p).comp D = a • e p + H.comp (e p)) (x : ⨂[ℂ] i, A i) :
    PiTensorProduct.map e (FiniteTensor.slotAlgebraHom p D x) =
      a • PiTensorProduct.map e x + FiniteTensor.slotAlgebraHom p H (PiTensorProduct.map e x) := by
  let L := (PiTensorProduct.mapMultilinear ℂ A C).toLinearMap e p
  have hd : (PiTensorProduct.map e).comp (FiniteTensor.slotAlgebraHom p D) = L ((e p).comp D) := by
    change (PiTensorProduct.map e).comp (PiTensorProduct.map (FiniteTensor.slot p D)) =
      PiTensorProduct.map (Function.update e p ((e p).comp D))
    rw [← PiTensorProduct.map_comp]
    apply congrArg (PiTensorProduct.map (R := ℂ))
    funext j
    by_cases hj : j = p
    · subst j
      simp only [FiniteTensor.slot, Function.update_self]
    · simp only [FiniteTensor.slot, Function.update_of_ne hj, LinearMap.comp_id]
  have he : (FiniteTensor.slotAlgebraHom p H).comp (PiTensorProduct.map e) = L (H.comp (e p)) := by
    change (PiTensorProduct.map (FiniteTensor.slot p H)).comp (PiTensorProduct.map e) =
      PiTensorProduct.map (Function.update e p (H.comp (e p)))
    rw [← PiTensorProduct.map_comp]
    apply congrArg (PiTensorProduct.map (R := ℂ))
    funext j
    by_cases hj : j = p
    · subst j
      simp only [FiniteTensor.slot, Function.update_self]
    · simp only [FiniteTensor.slot, Function.update_of_ne hj, LinearMap.id_comp]
  have hr : L (e p) = PiTensorProduct.map e := by
    change PiTensorProduct.map (Function.update e p (e p)) = _
    rw [Function.update_eq_self]
  have htotal : (PiTensorProduct.map e).comp (FiniteTensor.slotAlgebraHom p D) =
      a • PiTensorProduct.map e + (FiniteTensor.slotAlgebraHom p H).comp (PiTensorProduct.map e) := by
    rw [hd, h, map_add, map_smul, hr, he]
  exact LinearMap.congr_fun htotal x

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ}
variable (real : {v : InfinitePlace F // v.IsReal} → Fin k → List RealBlock)
variable (complex : {v : InfinitePlace F // v.IsComplex} → Fin k → List ComplexCharacterData)
variable (hm : ∑ i, (m i + 1) = r + 1)
variable (T : ∀ i, CuspidalOperatorRealization F (m i))
variable (hr : ∀ v i, (T i).realization.HasRealPlaceParameter v (real v i))
variable (hc : ∀ v i, (T i).realization.HasComplexPlaceParameter v (complex v i))

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (A : OperatorRealization F n) : AddCommGroup A.Space := Submodule.addCommGroup _
private local instance (i : Fin k) (p : Index F) : AddCommGroup ((T i).placeDensityModels.subspace p) :=
  Submodule.addCommGroup _

local notation "A" => infiniteStandardSpace r real complex
local notation "B" => GeneralLinear.BlockShape.mk k (fun i => m i + 1) (fun i => Nat.succ_pos (m i)) hm
local notation "C" => (fun p : Index F => ⨂[ℂ] i, OperatorRealization.PlaceDensityModels.subspace
  (CuspidalOperatorRealization.placeDensityModels (T i)) p)
local notation "E" => infiniteEvaluation real complex hm T hr hc

/-- The sum of block Lie operators at one place, on the full infinite coefficient tensor. -/
def infiniteCoefficientLieAt (v : Index F) (Y : ∀ i, Lie (m i + 1) v) :
    Module.End ℂ (⨂[ℂ] p, C p) :=
  FiniteTensor.slotAlgebraHom v (placeCoefficientLieSum T v Y)

/-- The real upper triangular derivative at infinite compact identity acts in
one place and includes that place's half-character term. -/
theorem infiniteEvaluation_lie_real_upper (v : {v : InfinitePlace F // v.IsReal})
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (hX : X.IsUpperTriangular) (a : ⨂[ℂ] v, A v) :
    E 1 (infiniteStandardLieAt r real complex (.inl v) (1 ⊗ₜ[ℝ] X) a) =
      archimedeanHalfDerivative F B (realPlaceLieInclusion F (r + 1) v X) • E 1 a +
      infiniteCoefficientLieAt T (.inl v) (fun i => 1 ⊗ₜ[ℝ] localDiagonalBlock ℝ B i X) (E 1 a) := by
  let e (p : Index F) := infiniteLocalEvaluation real complex hm T hr hc p
    (infiniteCompactCoordinates F (r + 1) 1 p)
  let u : Index F := .inl v
  let D := infiniteStandardLocalLie r real complex u (1 ⊗ₜ[ℝ] X)
  let H := placeCoefficientLieSum T u (fun i => 1 ⊗ₜ[ℝ] localDiagonalBlock ℝ B i X)
  let c := archimedeanHalfDerivative F B (realPlaceLieInclusion F (r + 1) v X)
  have h₀ : e u = realPlaceEvaluation hm T v (real v) (hr v) 1 := by
    simp only [e, u, map_one, Pi.one_apply, infiniteLocalEvaluation]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  have h (x : A u) : e u (D x) = c • e u x + H (e u x) := by
    let E₀ := realPlaceEvaluation hm T v (real v) (hr v) 1
    have hx : E₀ (D x) = c • E₀ x + H (E₀ x) :=
      realPlaceEvaluation_lie_upper hm T v (real v) (hr v) X hX x
    exact (LinearMap.congr_fun h₀ (D x)).trans (hx.trans
      (congrArg (fun y : C u => c • y + H y) (LinearMap.congr_fun h₀ x).symm))
  exact map_slot_with_scalar e u D H c (LinearMap.ext h) a

/-- The complex upper triangular derivative at infinite compact identity acts in
one place and includes that place's half-character term. -/
theorem infiniteEvaluation_lie_complex_upper (v : {v : InfinitePlace F // v.IsComplex})
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hX : X.IsUpperTriangular) (a : ⨂[ℂ] v, A v) :
    E 1 (infiniteStandardLieAt r real complex (.inr v) (1 ⊗ₜ[ℝ] X) a) =
      archimedeanHalfDerivative F B (complexPlaceLieInclusion F (r + 1) v X) • E 1 a +
      infiniteCoefficientLieAt T (.inr v) (fun i => 1 ⊗ₜ[ℝ] localDiagonalBlock ℂ B i X) (E 1 a) := by
  let e (p : Index F) := infiniteLocalEvaluation real complex hm T hr hc p
    (infiniteCompactCoordinates F (r + 1) 1 p)
  let u : Index F := .inr v
  let D := infiniteStandardLocalLie r real complex u (1 ⊗ₜ[ℝ] X)
  let H := placeCoefficientLieSum T u (fun i => 1 ⊗ₜ[ℝ] localDiagonalBlock ℂ B i X)
  let c := archimedeanHalfDerivative F B (complexPlaceLieInclusion F (r + 1) v X)
  have h₀ : e u = complexPlaceEvaluation hm T v (complex v) (hc v) 1 := by
    simp only [e, u, map_one, Pi.one_apply, infiniteLocalEvaluation]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  have h (x : A u) : e u (D x) = c • e u x + H (e u x) := by
    let E₀ := complexPlaceEvaluation hm T v (complex v) (hc v) 1
    have hx : E₀ (D x) = c • E₀ x + H (E₀ x) :=
      complexPlaceEvaluation_lie_upper hm T v (complex v) (hc v) X hX x
    exact (LinearMap.congr_fun h₀ (D x)).trans (hx.trans
      (congrArg (fun y : C u => c • y + H y) (LinearMap.congr_fun h₀ x).symm))
  exact map_slot_with_scalar e u D H c (LinearMap.ext h) a

end Langlands.Global.CuspidalBlockInduction
