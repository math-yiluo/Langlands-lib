import Langlands.Global.Factors.CuspidalBlockInfiniteLieAdjoint
import Langlands.Global.AdelicBlockNormalizedCoefficientMap
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Langlands.Representation.Archimedean.ComplexJacquetChart

/-! # Extending the identity comparison to the whole place Lie operator -/

noncomputable section

open scoped Classical Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 210000

universe u v w

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic _root_.Langlands.Archimedean LocalFactor.Archimedean InfinitePlaceFamily
open ArchimedeanGL NumberField AdelicBlockScalarSections GeneralLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {k : ℕ}
variable (r : ℕ)
variable (real : {v : InfinitePlace F // v.IsReal} → Fin k → List RealBlock)
variable (complex : {v : InfinitePlace F // v.IsComplex} → Fin k → List ComplexCharacterData)
variable {U : Type v} [AddCommGroup U] [Module ℂ U]

local notation "Ai" => (⨂[ℂ] v, infiniteStandardSpace r real complex v)
local notation "Kf" => FiniteAdelicGL.standardIntegral F (r + 1)
local notation "K" => standardInfiniteCompact F (r + 1)
local notation "κ" => Representation.tprod (Representation.trivial ℂ K U) (infiniteStandardAction r real complex)
local notation "δ" => infiniteStandardTensorLie r real complex U

variable (B : BlockShape (r + 1)) (S : ∀ i, OperatorRealization F (B.size i))

local notation "W" => smoothCompactFiniteSections F B S
local notation "C" => coefficientValues F B S
local notation "N" => normalizedCoefficientMap F B S
local notation "JType" => (Representation.IntertwiningMap κ (smoothCompactAction F B S))

private theorem atIdentity_add {L : Type w} [AddCommGroup L] [Module ℝ L]
    (J : U ⊗[ℂ] Ai →ₗ[ℂ] W) (l : Kf) (ι : L →ₗ[ℝ] RealLieAlgebra F (r + 1))
    (D : (ℂ ⊗[ℝ] L) →ₗ[ℂ] Module.End ℂ (U ⊗[ℂ] Ai))
    (x : U ⊗[ℂ] Ai) (X Y : L)
    (hX : N (compactPair F 1 l) (J (D (1 ⊗ₜ[ℝ] X) x)) =
      N (compactPair F 1 l) (sectionDifferential F B S (ι X) (J x)))
    (hY : N (compactPair F 1 l) (J (D (1 ⊗ₜ[ℝ] Y) x)) =
      N (compactPair F 1 l) (sectionDifferential F B S (ι Y) (J x))) :
    N (compactPair F 1 l) (J (D (1 ⊗ₜ[ℝ] (X + Y)) x)) =
      N (compactPair F 1 l) (sectionDifferential F B S (ι (X + Y)) (J x)) := by
  simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, sectionDifferential_add, hX, hY]

/-- An upper triangular identity comparison and compact intertwining give the
real-place Lie intertwining law in every real matrix direction. -/
theorem sectionLie_real_of_upper (J : JType) (v : {v : InfinitePlace F // v.IsReal})
    (hupper : ∀ (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ), X.IsUpperTriangular →
      ∀ (x : U ⊗[ℂ] Ai) (l : Kf),
        N (compactPair F 1 l) (J (δ (.inl v) (1 ⊗ₜ[ℝ] X) x)) =
          N (compactPair F 1 l) (sectionDifferential F B S (realPlaceLieInclusion F (r + 1) v X) (J x)))
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (x : U ⊗[ℂ] Ai) :
    J (δ (.inl v) (1 ⊗ₜ[ℝ] X) x) = sectionDifferential F B S (realPlaceLieInclusion F (r + 1) v X) (J x) := by
  let α (q : K) := unitaryMatrixRealLieConjugation ℝ (r + 1) (infiniteCompactCoordinates F (r + 1) q (.inl v))
  refine intertwines_sectionDifferential_of_identity F B S κ J (realPlaceLieInclusion F (r + 1) v)
    (fun X => δ (.inl v) (1 ⊗ₜ[ℝ] X)) (fun q X => α q X)
    (fun q X => realLieConjugation_infiniteCompact_real F (r + 1) q v X)
    (fun q X x => infiniteStandardTensorLie_real_adjoint r real complex U q v X x) ?_ X x
  intro Y y l
  let A := RealJacquetFrobenius.upperPart Y
  let D := RealJacquetFrobenius.skewPart Y
  have hY : A + D = Y := RealJacquetFrobenius.upperPart_add_skewPart Y
  have hA := hupper A (RealJacquetFrobenius.upperPart_isUpperTriangular Y) y l
  have hD := intertwines_infiniteStandardLie_real_skew r real complex B S J v D
    (skewAdjoint.mem_iff.mp (RealJacquetFrobenius.skewPart_mem Y)) y
  have hadd := atIdentity_add r real complex B S J.toLinearMap l (realPlaceLieInclusion F (r + 1) v).toLinearMap
    (δ (.inl v)) y A D hA (congrArg (N (compactPair F 1 l)) hD)
  rwa [hY] at hadd

/-- An upper triangular identity comparison and compact intertwining give the
complex-place Lie intertwining law in every underlying real matrix direction. -/
theorem sectionLie_complex_of_upper (J : JType) (v : {v : InfinitePlace F // v.IsComplex})
    (hupper : ∀ (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ), X.IsUpperTriangular →
      ∀ (x : U ⊗[ℂ] Ai) (l : Kf),
        N (compactPair F 1 l) (J (δ (.inr v) (1 ⊗ₜ[ℝ] X) x)) =
          N (compactPair F 1 l) (sectionDifferential F B S (complexPlaceLieInclusion F (r + 1) v X) (J x)))
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : U ⊗[ℂ] Ai) :
    J (δ (.inr v) (1 ⊗ₜ[ℝ] X) x) = sectionDifferential F B S (complexPlaceLieInclusion F (r + 1) v X) (J x) := by
  let α (q : K) := unitaryMatrixRealLieConjugation ℂ (r + 1) (infiniteCompactCoordinates F (r + 1) q (.inr v))
  refine intertwines_sectionDifferential_of_identity F B S κ J (complexPlaceLieInclusion F (r + 1) v)
    (fun X => δ (.inr v) (1 ⊗ₜ[ℝ] X)) (fun q X => α q X)
    (fun q X => realLieConjugation_infiniteCompact_complex F (r + 1) q v X)
    (fun q X x => infiniteStandardTensorLie_complex_adjoint r real complex U q v X x) ?_ X x
  intro Y y l
  let A := Archimedean.upperPart Y
  let D := Archimedean.skewPart Y
  have hY : A + D = Y := Archimedean.upperPart_add_skewPart Y
  have hA := hupper A (Archimedean.upperPart_isUpperTriangular Y) y l
  have hD := intertwines_infiniteStandardLie_complex_skew r real complex B S J v D (Archimedean.star_skewPart Y) y
  have hadd := atIdentity_add r real complex B S J.toLinearMap l (complexPlaceLieInclusion F (r + 1) v).toLinearMap
    (δ (.inr v)) y A D hA (congrArg (N (compactPair F 1 l)) hD)
  rwa [hY] at hadd

/-- The actual section enveloping action on the Lie generator at a single place. -/
def sectionPlaceLieAction (p : Index F) : Lie (r + 1) p →ₗ[ℂ] Module.End ℂ W :=
  (sectionEnvelopingAction F B S).toLinearMap.comp
    ((envelopingGenerator F (r + 1)).toLinearMap.comp (lieInclusion (r + 1) p).toLinearMap)

theorem sectionPlaceLieAction_real_one (v : {v : InfinitePlace F // v.IsReal})
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :
    sectionPlaceLieAction r B S (.inl v) (1 ⊗ₜ[ℝ] X) =
      sectionDifferential F B S (realPlaceLieInclusion F (r + 1) v X) := by
  change sectionEnvelopingAction F B S (envelopingGenerator F (r + 1)
    (realPlaceComplexLieInclusion F (r + 1) v (1 ⊗ₜ[ℝ] X))) = _
  rw [realPlaceComplexLieInclusion_tmul, ← complexify_apply, sectionEnvelopingAction_real_generator]

theorem sectionPlaceLieAction_complex_one (v : {v : InfinitePlace F // v.IsComplex})
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    sectionPlaceLieAction r B S (.inr v) (1 ⊗ₜ[ℝ] X) =
      sectionDifferential F B S (complexPlaceLieInclusion F (r + 1) v X) := by
  change sectionEnvelopingAction F B S (envelopingGenerator F (r + 1)
    (complexPlaceComplexLieInclusion F (r + 1) v (1 ⊗ₜ[ℝ] X))) = _
  rw [complexPlaceComplexLieInclusion_tmul, ← complexify_apply, sectionEnvelopingAction_real_generator]

/-- It suffices to compare the complexified Lie operators on tensors with scalar one. -/
theorem intertwines_complexification_of_real {L V Z : Type*} [AddCommGroup L] [Module ℝ L]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
    (J : V →ₗ[ℂ] Z) (D : ℂ ⊗[ℝ] L →ₗ[ℂ] Module.End ℂ V)
    (E : ℂ ⊗[ℝ] L →ₗ[ℂ] Module.End ℂ Z)
    (h : ∀ X x, J (D (1 ⊗ₜ[ℝ] X) x) = E (1 ⊗ₜ[ℝ] X) (J x)) (X : ℂ ⊗[ℝ] L) (x : V) :
    J (D X x) = E X (J x) := by
  induction X using TensorProduct.inductionOn with
  | tmul c X =>
    have hc : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [hc, map_smul, LinearMap.smul_apply, h]
  | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]

end Langlands.Global.CuspidalBlockInduction
