import Langlands.Global.Factors.CuspidalBlockInfiniteLieAction
import Langlands.Global.ArchimedeanPlaceAdjoint

/-! # Compact adjoints on the original-order standard tensor -/

noncomputable section

open scoped Classical Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 180000

universe u v

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic _root_.Langlands.Archimedean LocalFactor.Archimedean InfinitePlaceFamily
open ArchimedeanGL NumberField

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem tensor_map_slot_adjoint {I : Type*} [DecidableEq I] {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (S : ∀ i, Module.End ℂ (V i)) (p : I) (D E : Module.End ℂ (V p))
    (h : (S p).comp D = E.comp (S p)) :
    (PiTensorProduct.map S).comp (FiniteTensor.slotAlgebraHom p D) =
      (FiniteTensor.slotAlgebraHom p E).comp (PiTensorProduct.map S) := by
  change (PiTensorProduct.map S).comp (PiTensorProduct.map (FiniteTensor.slot p D)) =
    (PiTensorProduct.map (FiniteTensor.slot p E)).comp (PiTensorProduct.map S)
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  apply congrArg (PiTensorProduct.map (R := ℂ))
  funext j
  by_cases hj : j = p
  · subst j
    simpa only [FiniteTensor.slot, Function.update_self] using h
  · simp only [FiniteTensor.slot, Function.update_of_ne hj, LinearMap.comp_id, LinearMap.id_comp]

variable {F : Type u} [Field F] [NumberField F] {k : ℕ}
variable (r : ℕ)
variable (real : {v : InfinitePlace F // v.IsReal} → Fin k → List RealBlock)
variable (complex : {v : InfinitePlace F // v.IsComplex} → Fin k → List ComplexCharacterData)

local notation "A" => infiniteStandardSpace r real complex
local notation "W∞" => (⨂[ℂ] v, A v)
local notation "K" => standardInfiniteCompact F (r + 1)
local notation "κ" => infiniteStandardAction r real complex

variable (U : Type v) [AddCommGroup U] [Module ℂ U]

local notation "κU" => Representation.tprod (Representation.trivial ℂ K U) κ

/-- The one-place standard Lie operator on a tensor with an additional fixed factor. -/
def infiniteStandardTensorLie (p : Index F) : Lie (r + 1) p →ₗ[ℂ] Module.End ℂ (U ⊗[ℂ] W∞) :=
  (LinearMap.lTensorHom U).comp (infiniteStandardLieAt r real complex p)

private theorem infiniteStandardTensorLie_adjoint (q : K) (p : Index F)
    (X Y : Lie (r + 1) p)
    (h : ∀ x : A p, infiniteStandardLocalAction r real complex p
        (infiniteCompactCoordinates F (r + 1) q p) (infiniteStandardLocalLie r real complex p X x) =
      infiniteStandardLocalLie r real complex p Y
        (infiniteStandardLocalAction r real complex p (infiniteCompactCoordinates F (r + 1) q p) x))
    (x : U ⊗[ℂ] W∞) :
    κU q (infiniteStandardTensorLie r real complex U p X x) =
      infiniteStandardTensorLie r real complex U p Y (κU q x) := by
  let S (j : Index F) := infiniteStandardLocalAction r real complex j
    (infiniteCompactCoordinates F (r + 1) q j)
  let D := infiniteStandardLocalLie r real complex p X
  let E := infiniteStandardLocalLie r real complex p Y
  have he := tensor_map_slot_adjoint S p D E (LinearMap.ext h)
  have hU := congrArg (LinearMap.lTensor U) he
  simp only [LinearMap.lTensor_comp] at hU
  exact LinearMap.congr_fun hU x

/-- Compact covariance of the tensor Lie action in a real-place matrix direction. -/
theorem infiniteStandardTensorLie_real_adjoint (q : K) (v : {v : InfinitePlace F // v.IsReal})
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (x : U ⊗[ℂ] W∞) :
    κU q (infiniteStandardTensorLie r real complex U (.inl v) (1 ⊗ₜ[ℝ] X) x) =
      infiniteStandardTensorLie r real complex U (.inl v)
        (1 ⊗ₜ[ℝ] unitaryMatrixRealLieConjugation ℝ (r + 1)
          (infiniteCompactCoordinates F (r + 1) q (.inl v)) X) (κU q x) := by
  apply infiniteStandardTensorLie_adjoint
  intro z
  let d := infiniteCompactCoordinates F (r + 1) q (.inl v)
  exact (isRealGKModule_realStandardModule (r + 1) (List.flatten (List.ofFn (real v)))).2.2.2 d X z

/-- Compact covariance of the tensor Lie action in a complex-place matrix direction. -/
theorem infiniteStandardTensorLie_complex_adjoint (q : K) (v : {v : InfinitePlace F // v.IsComplex})
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : U ⊗[ℂ] W∞) :
    κU q (infiniteStandardTensorLie r real complex U (.inr v) (1 ⊗ₜ[ℝ] X) x) =
      infiniteStandardTensorLie r real complex U (.inr v)
        (1 ⊗ₜ[ℝ] unitaryMatrixRealLieConjugation ℂ (r + 1)
          (infiniteCompactCoordinates F (r + 1) q (.inr v)) X) (κU q x) := by
  apply infiniteStandardTensorLie_adjoint
  intro z
  let d := infiniteCompactCoordinates F (r + 1) q (.inr v)
  exact (isComplexGKModule_complexStandardModule (r + 1) (List.flatten (List.ofFn (complex v)))).2.2.2 d X z

variable (F)

/-- The actual compact adjoint preserves the inserted one-place real Lie algebra. -/
theorem realLieConjugation_infiniteCompact_real (n : ℕ) (q : standardInfiniteCompact F n)
    (v : {v : InfinitePlace F // v.IsReal}) (X : Matrix (Fin n) (Fin n) ℝ) :
    realLieConjugation F n q.val (realPlaceLieInclusion F n v X) =
      realPlaceLieInclusion F n v (unitaryMatrixRealLieConjugation ℝ n
        (infiniteCompactCoordinates F n q (.inl v)) X) := by
  obtain ⟨p, rfl⟩ := ArchimedeanCompactFactors.toStandardCompact_surjective F n q
  have hd : infiniteCompactCoordinates F n (ArchimedeanCompactFactors.toStandardCompact F n p)
      (.inl v) = p.1 v := by
    apply Subtype.ext
    rw [infiniteCompactCoordinates_apply_real, ArchimedeanCompactFactors.toStandardCompact_val,
      ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
    rfl
  rw [hd]
  exact realLieConjugation_realInclusion F n p v X

/-- The actual compact adjoint preserves the inserted one-place complex matrix Lie algebra. -/
theorem realLieConjugation_infiniteCompact_complex (n : ℕ) (q : standardInfiniteCompact F n)
    (v : {v : InfinitePlace F // v.IsComplex}) (X : Matrix (Fin n) (Fin n) ℂ) :
    realLieConjugation F n q.val (complexPlaceLieInclusion F n v X) =
      complexPlaceLieInclusion F n v (unitaryMatrixRealLieConjugation ℂ n
        (infiniteCompactCoordinates F n q (.inr v)) X) := by
  obtain ⟨p, rfl⟩ := ArchimedeanCompactFactors.toStandardCompact_surjective F n q
  have hd : infiniteCompactCoordinates F n (ArchimedeanCompactFactors.toStandardCompact F n p)
      (.inr v) = p.2 v := by
    apply Subtype.ext
    rw [infiniteCompactCoordinates_apply_complex, ArchimedeanCompactFactors.toStandardCompact_val,
      ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
    rfl
  rw [hd]
  exact realLieConjugation_complexInclusion F n p v X

end Langlands.Global.CuspidalBlockInduction
