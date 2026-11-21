import Langlands.Global.Factors.CuspidalBlockInfiniteCompactCoordinates
import Langlands.Global.AdelicBlockCompactCurveIntertwining
import Langlands.Representation.Tensor.FiniteSlotDifferential
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Differentiation of the compact actions of the infinite standard tensor -/

noncomputable section

open scoped Classical Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 220000

universe u v

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic _root_.Langlands.Archimedean LocalFactor.Archimedean InfinitePlaceFamily
open ArchimedeanGL NumberField AdelicBlockScalarSections GeneralLinear

attribute [local instance 100] LieRing.ofAssociativeRing

section CompactCurve

variable (𝕜 : Type) [RCLike 𝕜] {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) 𝕜

/-- The exponential compact curve in a skew-adjoint matrix direction. -/
def unitaryExpCurve (X : M) (hX : star X = -X) (t : ℝ) : Matrix.unitaryGroup (Fin n) 𝕜 :=
  ⟨NormedSpace.exp (t • X), by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff, star_smul, hX, star_trivial, smul_neg]⟩

private theorem unitaryExpCurve_zero (X : M) (hX : star X = -X) :
    unitaryExpCurve 𝕜 X hX 0 = 1 := by
  apply Subtype.ext
  change NormedSpace.exp ((0 : ℝ) • X) = 1
  rw [zero_smul, NormedSpace.exp_zero]

private theorem unitaryExpCurve_hasDerivAt_entry (X : M) (hX : star X = -X) (i j : Fin n) :
    HasDerivAt (fun t => (unitaryExpCurve 𝕜 X hX t).val i j) (X i j) 0 := by
  have h : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  exact (Matrix.entryLinearMap ℝ 𝕜 i j).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 h

end CompactCurve

variable {F : Type u} [Field F] [NumberField F] {k : ℕ}
variable (r : ℕ)
variable (real : {v : InfinitePlace F // v.IsReal} → Fin k → List RealBlock)
variable (complex : {v : InfinitePlace F // v.IsComplex} → Fin k → List ComplexCharacterData)

local notation "A" => infiniteStandardSpace r real complex
local notation "W∞" => (⨂[ℂ] v, A v)
local notation "K" => standardInfiniteCompact F (r + 1)

/-- The original-order local standard Lie action at each tagged infinite place. -/
def infiniteStandardLocalLie (v : Index F) : Lie (r + 1) v →ₗ⁅ℂ⁆ Module.End ℂ (A v) := by
  cases v with
  | inl v => exact realStandardLie (r + 1) (List.flatten (List.ofFn (real v)))
  | inr v => exact complexStandardLie (r + 1) (List.flatten (List.ofFn (complex v)))

/-- The local Lie action transported to its slot of the infinite standard tensor. -/
def infiniteStandardLieAt (v : Index F) : Lie (r + 1) v →ₗ[ℂ] Module.End ℂ W∞ :=
  (FiniteTensor.slotAlgebraHom (V := A) v).toLinearMap.comp
    (infiniteStandardLocalLie r real complex v).toLinearMap

theorem infiniteStandardAction_inclusion (v : Index F) (d : Compact (r + 1) v) :
    infiniteStandardAction r real complex (compactInclusion (r + 1) v d) =
      FiniteTensor.externalSlot (infiniteStandardLocalAction r real complex) v d := by
  change FiniteTensor.external (infiniteStandardLocalAction r real complex)
    (infiniteCompactCoordinates F (r + 1) (compactInclusion (r + 1) v d)) = _
  rw [infiniteCompactCoordinates_inclusion, FiniteTensor.external_mulSingle_eq_externalSlot]

variable {U : Type v} [AddCommGroup U] [Module ℂ U]

local notation "κ" => infiniteStandardAction r real complex
local notation "κ₀" => Representation.trivial ℂ K U

private theorem hasDerivAt_standardTensor_compactInclusion (v : Index F)
    (γ : ℝ → Compact (r + 1) v) (Y : Lie (r + 1) v)
    (hγ : ∀ (b : A v) (L : A v →ₗ[ℂ] ℂ),
      HasDerivAt (fun t => L (infiniteStandardLocalAction r real complex v (γ t) b))
        (L (infiniteStandardLocalLie r real complex v Y b)) 0)
    (x : U ⊗[ℂ] W∞) (ℓ : U ⊗[ℂ] W∞ →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => ℓ (Representation.tprod κ₀ κ (compactInclusion (r + 1) v (γ t)) x))
      (ℓ ((infiniteStandardLieAt r real complex v Y).lTensor U x)) 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    let L := ℓ.comp (TensorProduct.mk ℂ U W∞ a)
    have hd := FiniteTensor.hasDerivAt_externalSlot (infiniteStandardLocalAction r real complex) v γ
      (infiniteStandardLocalLie r real complex v Y) hγ b L
    simpa only [Representation.tprod_apply, TensorProduct.map_tmul, Representation.trivial_apply,
      Module.End.one_apply, infiniteStandardAction_inclusion, LinearMap.lTensor_tmul,
      LinearMap.comp_apply, TensorProduct.mk_apply, infiniteStandardLieAt, AlgHom.toLinearMap_apply,
      LieHom.coe_toLinearMap, L] using! hd
  | add a b ha hb => simpa only [map_add] using! (HasDerivAt.fun_add ha hb)

variable (B : BlockShape (r + 1)) (S : ∀ i, OperatorRealization F (B.size i))
variable (J : (Representation.tprod
  (Representation.trivial ℂ (standardInfiniteCompact F (r + 1)) U)
  (infiniteStandardAction r real complex)).IntertwiningMap (smoothCompactAction F B S))

/-- A right compact intertwiner differentiates to the local Lie intertwiner
in every skew-adjoint real matrix direction. -/
theorem intertwines_infiniteStandardLie_real_skew
    (v : {v : InfinitePlace F // v.IsReal}) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (hX : star X = -X) (x : U ⊗[ℂ] W∞) :
    J ((infiniteStandardLieAt r real complex (.inl v) (1 ⊗ₜ[ℝ] X)).lTensor U x) =
      sectionDifferential F B S (realPlaceLieInclusion F (r + 1) v X) (J x) := by
  let γ := unitaryExpCurve ℝ X hX
  have γ₀ : γ 0 = 1 := unitaryExpCurve_zero ℝ X hX
  let hγ := unitaryExpCurve_hasDerivAt_entry ℝ X hX
  apply intertwines_sectionDifferential_of_compactCurve F B S _ J _
    (fun t => compactInclusion (r + 1) (.inl v) (γ t))
    (by rw [γ₀, map_one])
    (hasDerivAt_coordinates_realPlaceCompactInclusion v γ X hγ)
  exact hasDerivAt_standardTensor_compactInclusion r real complex (.inl v) γ (1 ⊗ₜ[ℝ] X)
    ((isRealGKModule_realStandardModule (r + 1) (List.flatten (List.ofFn (real v)))).2.2.1 γ X γ₀ hγ)

/-- A right compact intertwiner differentiates to the local Lie intertwiner
in every skew-adjoint complex matrix direction, regarded as a real direction. -/
theorem intertwines_infiniteStandardLie_complex_skew
    (v : {v : InfinitePlace F // v.IsComplex}) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hX : star X = -X) (x : U ⊗[ℂ] W∞) :
    J ((infiniteStandardLieAt r real complex (.inr v) (1 ⊗ₜ[ℝ] X)).lTensor U x) =
      sectionDifferential F B S (complexPlaceLieInclusion F (r + 1) v X) (J x) := by
  let γ := unitaryExpCurve ℂ X hX
  have γ₀ : γ 0 = 1 := unitaryExpCurve_zero ℂ X hX
  let hγ := unitaryExpCurve_hasDerivAt_entry ℂ X hX
  apply intertwines_sectionDifferential_of_compactCurve F B S _ J _
    (fun t => compactInclusion (r + 1) (.inr v) (γ t))
    (by rw [γ₀, map_one])
    (hasDerivAt_coordinates_complexPlaceCompactInclusion v γ X hγ)
  exact hasDerivAt_standardTensor_compactInclusion r real complex (.inr v) γ (1 ⊗ₜ[ℝ] X)
    ((isComplexGKModule_complexStandardModule (r + 1) (List.flatten (List.ofFn (complex v)))).2.2.1 γ X γ₀ hγ)

end Langlands.Global.CuspidalBlockInduction
