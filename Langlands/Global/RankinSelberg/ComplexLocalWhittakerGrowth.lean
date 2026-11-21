import Langlands.Global.ArchimedeanAnalyticJetProof
import Langlands.Global.ArchimedeanCompactAverageTranslation
import Langlands.Global.ArchimedeanCompactComponentCoverageProof
import Langlands.Global.ArchimedeanEnvelopingJetProof
import Langlands.Global.ArchimedeanFiniteUniformGrowthProof
import Langlands.Global.ArchimedeanJointFiniteAnalyticityProof
import Langlands.Global.ArchimedeanPlaceEnveloping
import Langlands.Global.ArchimedeanPlaceRestriction
import Langlands.Global.RankinSelberg.ComplexLocalCompactProjection
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerRegularity
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction
import Mathlib.Analysis.Complex.IsIntegral

/-! # Uniform derivative growth for complex local Whittaker functions -/

noncomputable section
universe u
open scoped Classical ContDiff IntermediateField Manifold Matrix.Norms.Operator NNReal TensorProduct
open NumberField Langlands.Archimedean Langlands.LocalFactor.Archimedean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal
namespace ComplexLocalWhittakerGrowth

open ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

section Transport

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "A" => InfiniteAdelicGL F n
local notation "AMat" => ArchimedeanMatrix F n

private def projectionMatrix (w : CP) : AMat →L[ℝ] Mat :=
  ((complexPlaceScalarProjection F w).mapMatrix.toLinearMap).toContinuousLinearMap

private def mixedProjection (w : CP) : ArchimedeanGL F n →* G :=
  Matrix.GeneralLinearGroup.map (complexPlaceScalarProjection F w).toRingHom

private def projection (w : CP) : A →* G :=
  (mixedProjection w).comp (archimedeanGLCoordinates F n).toMonoidHom

private def inclusion (w : CP) : G →* A :=
  (archimedeanGLCoordinates F n).symm.toMonoidHom.comp (complexPlaceGL F n w)

private theorem projection_val (w : CP) (g : A) :
    (projection w g).val = projectionMatrix w (archimedeanGLCoordinates F n g).val := rfl

omit [NumberField F] in
private theorem projection_inclusion (w : CP) (g : G) : projection w (inclusion w g) = g := by
  apply Units.ext
  change (mixedProjection w (archimedeanGLCoordinates F n
    ((archimedeanGLCoordinates F n).symm (complexPlaceGL F n w g)))).val = g.val
  rw [ContinuousMulEquiv.apply_symm_apply]
  refine Matrix.ext fun i j => ?_
  change ((complexPlaceGL F n w g).val i j).2 w = g.val i j
  rw [complexPlaceGL_entry, Pi.mulSingle_eq_same]

private def liftSmooth (w : CP) (W : G → ℂ)
    (hW : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ W) : SmoothFunctions F n := by
  refine ⟨W ∘ projection w, ?_⟩
  have h : ContDiffOn ℝ ∞ (unitsExtension W ∘ projectionMatrix w)
      {M : AMat | IsUnit M} := by
    apply (contDiffOn_unitsExtension hW).comp (projectionMatrix w).contDiff.contDiffOn
    intro M hM
    change IsUnit ((complexPlaceScalarProjection F w).mapMatrix M)
    exact hM.map (complexPlaceScalarProjection F w).mapMatrix
  have hs := (contMDiffOn_iff_contDiffOn.mpr h).comp_contMDiff
    (Units.contMDiff_val (𝕜 := ℝ) (n := ∞)) (fun g : ArchimedeanGL F n => g.isUnit)
  apply hs.congr
  intro g
  change W (projection w ((archimedeanGLCoordinates F n).symm g)) =
    unitsExtension W (projectionMatrix w g.val)
  rw [show projection w ((archimedeanGLCoordinates F n).symm g) = mixedProjection w g by
    change mixedProjection w (archimedeanGLCoordinates F n
      ((archimedeanGLCoordinates F n).symm g)) = mixedProjection w g
    rw [ContinuousMulEquiv.apply_symm_apply]]
  exact (unitsExtension_val W (mixedProjection w g)).symm

private theorem liftSmooth_apply (w : CP) (W : G → ℂ)
    (hW : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ W) (g : A) :
    (liftSmooth w W hW).val g = W (projection w g) := rfl

private def liftSmoothLinearMap (w : CP) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ W ∈ V, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ W) :
    V →ₗ[ℂ] SmoothFunctions F n where
  toFun W := liftSmooth w W.val (hV W W.2)
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private theorem smoothDifferential_lift (w : CP) (W : G → ℂ)
    (hW : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ W) (X : RealLieAlgebra F n) (g : A) :
    (smoothDifferential F n X (liftSmooth w W hW)).val g =
      rightDerivative (matrixModel ℂ n) (complexPlaceLieProjection F n w X) W
        (projection w g) := by
  have hext (x : ArchimedeanGL F n) : (unitsExtension W ∘ projectionMatrix w) x.val =
      (liftSmooth w W hW).val ((archimedeanGLCoordinates F n).symm x) := by
    rw [liftSmooth_apply]
    change unitsExtension W (mixedProjection w x).val =
      W (mixedProjection w (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm x)))
    rw [ContinuousMulEquiv.apply_symm_apply, unitsExtension_val]
  rw [smoothDifferential_eq_of_extension F n X _ _ hext, rightDerivative_eq_fderiv hW]
  have hdiff : DifferentiableAt ℝ (unitsExtension W)
      (projectionMatrix w (archimedeanGLCoordinates F n g).val) :=
    differentiableAt_unitsExtension hW (projection w g).isUnit
  rw [fderiv_comp (archimedeanGLCoordinates F n g).val hdiff
    (projectionMatrix w).differentiableAt, (projectionMatrix w).fderiv,
    ContinuousLinearMap.comp_apply, projection_val]
  congr 1
  exact (complexPlaceScalarProjection F w).mapMatrix.map_mul _ _

private theorem norm_projection_entry (w : CP) (g : A) (i j : Fin n) :
    ‖(projection w g).val i j‖ ≤ matrixHeight F n g := by
  let z := (archimedeanGLCoordinates F n g).val i j
  change ‖z.2 w‖ ≤ _
  exact (norm_le_pi_norm z.2 w).trans ((norm_snd_le z).trans
    ((ArchimedeanGL.norm_entry_le (archimedeanGLCoordinates F n g).val i j).trans
      (norm_val_le_matrixHeight F n g)))

private theorem height_projection (w : CP) (g : A) :
    max 1 (complexMatrixHeight (projection w g)) ≤
      (1 + 2 * (n : ℝ) * n) * matrixHeight F n g ^ 2 := by
  have hH := one_le_matrixHeight F n g
  have h₂ := one_le_pow₀ hH (n := 2)
  apply max_le
  · nlinarith [mul_nonneg (show 0 ≤ 2 * (n : ℝ) * n by positivity)
        (show 0 ≤ matrixHeight F n g ^ 2 by positivity)]
  · unfold complexMatrixHeight
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (matrixHeight F n g ^ 2 + matrixHeight F n g ^ 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => add_le_add
          (pow_le_pow_left₀ (norm_nonneg _) (norm_projection_entry w g i j) _) ?_
        rw [← map_inv]
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((norm_projection_entry w g⁻¹ i j).trans_eq (matrixHeight_inv F n g)) _
      _ = (2 * (n : ℝ) * n) * matrixHeight F n g ^ 2 := by simp; ring
      _ ≤ _ := by nlinarith [sq_nonneg (matrixHeight F n g)]

private theorem rowNorm_le_card_mul (M : AMat) (b : ℝ) (hb : 0 ≤ b)
    (hM : ∀ i j, ‖M i j‖ ≤ b) : ‖M‖ ≤ (n : ℝ) * b := by
  let B : ℝ≥0 := ⟨b, hb⟩
  have h : ‖M‖₊ ≤ (n : ℝ≥0) * B := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    have hs : (∑ j, ‖M i j‖₊) ≤ ∑ _j : Fin n, B := by
      apply Finset.sum_le_sum
      intro j _
      exact_mod_cast hM i j
    simpa [nsmul_eq_mul] using hs
  exact_mod_cast h

private theorem inclusion_entry (w : CP) (g : G) (i j : Fin n) :
    ‖(complexPlaceGL F n w g).val i j‖ ≤ max 1 (complexMatrixHeight g) := by
  have hb : 0 ≤ max 1 (complexMatrixHeight g) := (zero_le_one.trans (le_max_left _ _))
  have hone : ‖(1 : Mat) i j‖ ≤ (1 : ℝ) := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg hb).mpr
    intro v
    rw [complexPlaceGL_entry_fst]
    rw [Matrix.one_apply]
    split_ifs <;> simp [hb]
  · apply (pi_norm_le_iff_of_nonneg hb).mpr
    intro v
    rw [complexPlaceGL_entry]
    by_cases hv : v = w
    · subst v
      rw [Pi.mulSingle_eq_same]
      exact (ComplexPlaceAnalytic.norm_entry_le_complexMatrixHeight
        (Nat.pos_of_ne_zero fun h => Fin.elim0 (h ▸ i)) g i j).trans (le_max_right _ _)
    · rw [Pi.mulSingle_eq_of_ne hv, Units.val_one]
      exact hone.trans (le_max_left _ _)

private theorem height_inclusion (w : CP) (g : G) :
    matrixHeight F n (inclusion w g) ≤ (1 + (n : ℝ)) * max 1 (complexMatrixHeight g) := by
  have hH : 1 ≤ max 1 (complexMatrixHeight g) := le_max_left _ _
  have hpos : 0 ≤ max 1 (complexMatrixHeight g) := zero_le_one.trans hH
  have hval (x : G) : ‖(archimedeanGLCoordinates F n (inclusion w x)).val‖ ≤
      (n : ℝ) * max 1 (complexMatrixHeight x) := by
    change ‖(archimedeanGLCoordinates F n
      ((archimedeanGLCoordinates F n).symm (complexPlaceGL F n w x))).val‖ ≤ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact rowNorm_le_card_mul _ _ (zero_le_one.trans (le_max_left _ _)) (inclusion_entry w x)
  have hinv := hval g⁻¹
  rw [map_inv, map_inv, ComplexPlaceAnalytic.complexMatrixHeight_inv] at hinv
  unfold matrixHeight
  have hle : (n : ℝ) * max 1 (complexMatrixHeight g) ≤
      (1 + (n : ℝ)) * max 1 (complexMatrixHeight g) := by linarith
  exact max_le (hH.trans (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hpos]))
    (max_le ((hval g).trans hle) (hinv.trans hle))

end Transport

section Finiteness

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}
variable {ds : List ComplexCharacterData} {a : ℂˣ}

local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "n" => (r + 1)
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "A" => InfiniteAdelicGL F n
local notation "K" => standardInfiniteCompact F n
local notation "V" => complexWhittakerModel r ds a
local notation "S" => Automorphic.complexStandardKFinite n ds

private def compactProjection (w : CP) : K →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun k := ⟨(projection w k.val).val,
    ((mem_standardInfiniteCompact_iff F n k.val).mp k.2).2 w⟩
  map_one' := Subtype.ext (congrArg Units.val ((projection w).map_one))
  map_mul' k h := Subtype.ext (congrArg Units.val ((projection w).map_mul k.val h.val))

private def liftModel (w : CP) : V →ₗ[ℂ] SmoothFunctions F n :=
  liftSmoothLinearMap w V (fun _ hW => contMDiff_of_mem_complexWhittakerModel hW)

private theorem intertwiner_mem_model (B : S →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : S) : B f ∈ V :=
  Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)

private def liftIntertwiner (w : CP) (B : S →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) : S →ₗ[ℂ] SmoothFunctions F n :=
  (liftModel w).comp (B.codRestrict V (intertwiner_mem_model B hB))

private def liftCompactIntertwiner (w : CP) (B : S →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) :
    Representation.IntertwiningMap
      ((complexStandardRep n ds).comp (compactProjection (r := r) w))
      ((smoothRightAction F n).comp (K).subtype) :=
  (liftIntertwiner w B hB).intertwiningMap_of_isIntertwiningMap
    ((complexStandardRep n ds).comp (compactProjection (r := r) w))
    ((smoothRightAction F n).comp (K).subtype) (by
    intro k f
    let κ := compactProjection w k
    let k' : unitaryCompact ℂ n := ⟨projection w k.val, κ.2⟩
    have hκ : Unitary.toUnits κ = (k' : G) := Units.ext rfl
    have h := hB.2.2.2.1 k' f (complexStandardRep n ds κ f) (by
      rw [principalSeriesRep_apply_coe, hκ])
    apply Subtype.ext
    funext g
    change B (complexStandardRep n ds κ f) (projection w g) =
      B f (projection w (g * k.val))
    rw [h, map_mul]
    rfl)

private theorem liftIntertwiner_compactFinite (w : CP) (B : S →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : S) :
    FiniteVectors.IsFiniteVector ((smoothRightAction F n).comp (K).subtype)
      (liftIntertwiner w B hB f) := by
  have : Module.Finite ℂ (FiniteVectors.orbitSpan (complexStandardRep n ds) f) :=
    (isComplexGKModule_complexStandardModule n ds).1 f
  have hf : FiniteVectors.IsFiniteVector
      ((complexStandardRep n ds).comp (compactProjection (r := r) w)) f :=
    Submodule.finiteDimensional_of_le
      (S₂ := FiniteVectors.orbitSpan (complexStandardRep n ds) f) (Submodule.span_le.mpr (by
      rintro _ ⟨k, rfl⟩
      exact FiniteVectors.action_mem_orbitSpan (complexStandardRep n ds) (compactProjection w k) f))
  exact hf.map (liftCompactIntertwiner w B hB)

set_option synthInstance.maxHeartbeats 100000 in
private def projectedLieAction (w : CP) :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ S :=
  (complexStandardLie n ds).comp (complexPlaceComplexLieProjection F n w)

private theorem liftIntertwiner_lie (w : CP) (B : S →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B)
    (X : ComplexLieAlgebra F n) (f : S) :
    liftIntertwiner w B hB (projectedLieAction w X f) =
      complexSmoothLieAction F n X (liftIntertwiner w B hB f) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    apply congrArg (z • ·)
    let Y := complexPlaceLieProjection F n w X
    have h := hB.2.2.2.2 Y f (complexStandardLie n ds (1 ⊗ₜ[ℝ] Y) f)
      (principalSeriesLie_one_tmul_apply_coe ℂ n _ Y f)
    apply Subtype.ext
    funext g
    change B (complexStandardLie n ds (1 ⊗ₜ[ℝ] Y) f) (projection w g) =
      (complexSmoothLieAction F n (1 ⊗ₜ[ℝ] X) (liftSmooth w (B f) (hB.2.1 f))).val g
    rw [h, complexSmoothLieAction_tmul, one_smul, smoothDifferential_lift]
  | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]

omit [NumberField F] in
private theorem projectedEnvelopingAction (w : CP) :
    Langlands.Archimedean.envelopingAction (projectedLieAction (ds := ds) w) =
      (Langlands.Archimedean.envelopingAction (complexStandardLie n ds)).comp
        (complexPlaceEnvelopingProjection F n w) := by
  symm
  refine (UniversalEnvelopingAlgebra.lift_unique ℂ (projectedLieAction (ds := ds) w)
    ((Langlands.Archimedean.envelopingAction (complexStandardLie n ds)).comp
      (complexPlaceEnvelopingProjection F n w))).mp ?_
  funext X
  change Langlands.Archimedean.envelopingAction (complexStandardLie n ds)
      (complexPlaceEnvelopingProjection F n w (envelopingGenerator F n X)) =
    projectedLieAction (ds := ds) w X
  rw [complexPlaceEnvelopingProjection_generator]
  exact UniversalEnvelopingAlgebra.lift_ι_apply ℂ (complexStandardLie n ds)
    (complexPlaceComplexLieProjection F n w X)

private theorem liftIntertwiner_centerFinite (w : CP) (B : S →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : S) :
    IsCenterFinite F n (liftIntertwiner w B hB f) := by
  let T := liftIntertwiner w B hB
  unfold IsCenterFinite
  apply Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ T f)
  rw [centerOrbitSpan_eq_range]
  rintro _ ⟨z, rfl⟩
  have hz : complexPlaceEnvelopingProjection F n w z.val ∈
      Subalgebra.center ℂ (ComplexPlaceEnvelopingAlgebra n) :=
    Subalgebra.map_center_le_center (complexPlaceEnvelopingProjection_surjective F n w)
      ⟨z.val, z.2, rfl⟩
  obtain ⟨c, hc⟩ := complexStandardLie_hasInfinitesimalCharacter n ds _ hz
  have h := envelopingAction_intertwine (projectedLieAction w) (complexSmoothLieAction F n)
    T (liftIntertwiner_lie w B hB) z.val f
  rw [projectedEnvelopingAction, AlgHom.comp_apply, hc, Module.algebraMap_end_apply, map_smul] at h
  change Langlands.Archimedean.envelopingAction (complexSmoothLieAction F n) z.val (T f) ∈
    ℂ ∙ T f
  rw [← h]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private theorem liftModel_finite (w : CP) (W : V) :
    FiniteVectors.IsFiniteVector ((smoothRightAction F n).comp (K).subtype) (liftModel w W) ∧
    IsCenterFinite F n (liftModel w W) := by
  let P := (FiniteVectors.subrepresentation
    ((smoothRightAction F n).comp (K).subtype)).toSubmodule ⊓ centerFiniteFunctions F n
  have h : V ≤ (P.comap (liftModel w)).map (V).subtype := by
    refine iSup_le fun B => iSup_le fun hB => ?_
    rintro _ ⟨f, rfl⟩
    exact ⟨⟨B f, intertwiner_mem_model B hB f⟩,
      ⟨liftIntertwiner_compactFinite w B hB f, liftIntertwiner_centerFinite w B hB f⟩, rfl⟩
  obtain ⟨W', hW', hEq⟩ := h W.2
  have he : W' = W := Subtype.ext hEq
  subst W'
  exact hW'

private theorem liftIntertwiner_enveloping (w : CP) (B : S →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) (u : EnvelopingAlgebra F n) (f : S) :
    ArchimedeanGL.envelopingAction F n u (liftIntertwiner w B hB f) =
      liftIntertwiner w B hB
        (Langlands.Archimedean.envelopingAction (complexStandardLie n ds)
          (complexPlaceEnvelopingProjection F n w u) f) := by
  rw [← AlgHom.comp_apply, ← projectedEnvelopingAction]
  exact (envelopingAction_intertwine (projectedLieAction w) (complexSmoothLieAction F n)
    (liftIntertwiner w B hB) (liftIntertwiner_lie w B hB) u f).symm

private theorem liftIntertwiner_jointFinite (w : CP) (B : S →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : S) :
    IsJointFinite F n (liftIntertwiner w B hB f) :=
  separateJointFinite F n _ (liftIntertwiner_centerFinite w B hB f)
    (compactGroupFiniteDifferential F n _ (liftIntertwiner_compactFinite w B hB f))

private theorem liftIntertwiner_eval_at_compact (w : CP) (B : S →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : S) (k : K) :
    (liftIntertwiner w B hB f).val k.val = B (complexStandardRep n ds (compactProjection w k) f) 1 := by
  let κ := compactProjection w k
  let k' : unitaryCompact ℂ n := ⟨projection w k.val, κ.2⟩
  have hκ : Unitary.toUnits κ = (k' : G) := Units.ext rfl
  have h := hB.2.2.2.1 k' f (complexStandardRep n ds κ f) (by
    rw [principalSeriesRep_apply_coe, hκ])
  have he := congrFun h (1 : G)
  change B (complexStandardRep n ds κ f) 1 = B f (1 * k'.val) at he
  change B f k'.val = B (complexStandardRep n ds κ f) 1
  exact (he.trans (congrArg (B f) (one_mul k'.val))).symm

set_option maxHeartbeats 1000000 in
private theorem eq_of_eval_atPlace (w : CP) {B C : S →ₗ[ℂ] (G → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B) (hC : IsComplexWhittakerIntertwiner r ds a C)
    (h : ∀ f, B f 1 = C f 1) : B = C := by
  apply LinearMap.ext
  intro f
  funext g
  let W := liftIntertwiner w B hB f - liftIntertwiner w C hC f
  have hW : IsJointFinite F n W := (jointFiniteFunctions F n).sub_mem
    (liftIntertwiner_jointFinite w B hB f) (liftIntertwiner_jointFinite w C hC f)
  obtain ⟨k, hk⟩ := compactComponentCoverage F n (inclusion w g)
  have hz (u : EnvelopingAlgebra F n) : (ArchimedeanGL.envelopingAction F n u W).val k.val = 0 := by
    simp only [W, map_sub, Submodule.coe_sub, Pi.sub_apply, liftIntertwiner_enveloping,
      liftIntertwiner_eval_at_compact, h, sub_self]
  have he := analyticMatrixJetUniqueness F n W k.val (jointFiniteAnalyticity F n W hW)
    (envelopingZeroJet F n W k.val hz) (inclusion w g) hk
  change B f (projection w (inclusion w g)) - C f (projection w (inclusion w g)) = 0 at he
  rw [projection_inclusion] at he
  exact sub_eq_zero.mp he

end Finiteness

section CompactAverage

open MeasureTheory Set
open ArchimedeanGL.DerivativeSmoothFunctions
open ArchimedeanGL.SmoothFamily (averageLM averagedTranslate_mem compactRepresentation rightRepresentation)
open ComplexJacquet (hasFiniteCompactConvolutionKernel_of_finite_translates)

local instance whittakerProjectionMeasurable (j : ℕ) :
    MeasurableSpace (unitaryCompact ℂ j) := borel _
local instance whittakerProjectionBorel (j : ℕ) : BorelSpace (unitaryCompact ℂ j) := ⟨rfl⟩

variable {F : Type} [Field F] [NumberField F] {r : ℕ}
variable {ds : List ComplexCharacterData} {a : ℂˣ}

local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "n" => (r + 1)
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "A" => InfiniteAdelicGL F n
local notation "K" => standardInfiniteCompact F n
local notation "U" => unitaryCompact ℂ n
local notation "Std" => Automorphic.complexStandardKFinite n ds
local notation "Fam" => ArchimedeanGL.SmoothFamily F n Bool

private def liftStandard (w : CP) : Std →ₗ[ℂ] SmoothFunctions F n :=
  liftSmoothLinearMap w (Automorphic.complexStandardKFinite n ds) (fun _ hf => hf.1.1)

private theorem liftStandard_compact (w : CP) (k : K) (f : Std) :
    smoothRightAction F n k.val (liftStandard w f) =
      liftStandard w (complexStandardRep n ds (compactProjection w k) f) := by
  apply Subtype.ext
  funext g
  change f.val (projection w (g * k.val)) =
    (complexStandardRep n ds (compactProjection w k) f).val (projection w g)
  rw [map_mul, principalSeriesRep_apply_coe]
  rw [show Unitary.toUnits (compactProjection w k) = projection w k.val from Units.ext rfl]
  rfl

private theorem liftStandard_lie (w : CP) (Z : ComplexLieAlgebra F n) (f : Std) :
    liftStandard w (projectedLieAction w Z f) = complexSmoothLieAction F n Z (liftStandard w f) := by
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
    have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    apply congrArg (z • ·)
    apply Subtype.ext
    funext g
    let Y := complexPlaceLieProjection F n w X
    change (complexStandardLie n ds (1 ⊗ₜ[ℝ] Y) f).val (projection w g) =
      (complexSmoothLieAction F n (1 ⊗ₜ[ℝ] X) (liftStandard w f)).val g
    rw [principalSeriesLie_one_tmul_apply_coe, complexSmoothLieAction_tmul, one_smul,
      show liftStandard w f = liftSmooth w f.val f.2.1.1 from rfl, smoothDifferential_lift]
  | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]

private theorem liftStandard_enveloping (w : CP) (q : EnvelopingAlgebra F n) (f : Std) :
    ArchimedeanGL.envelopingAction F n q (liftStandard w f) =
      liftStandard w (Langlands.Archimedean.envelopingAction (complexStandardLie n ds)
        (complexPlaceEnvelopingProjection F n w q) f) := by
  rw [← AlgHom.comp_apply, ← projectedEnvelopingAction]
  exact (envelopingAction_intertwine (projectedLieAction w) (complexSmoothLieAction F n)
    (liftStandard w) (liftStandard_lie w) q f).symm

private theorem liftStandard_jointFinite (w : CP) (f : Std) : IsJointFinite F n (liftStandard w f) := by
  apply separateJointFinite F n
  · apply Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ liftStandard w f)
    rw [centerOrbitSpan_eq_range]
    rintro _ ⟨z, rfl⟩
    have hz : complexPlaceEnvelopingProjection F n w z.val ∈
        Subalgebra.center ℂ (ComplexPlaceEnvelopingAlgebra n) :=
      Subalgebra.map_center_le_center (complexPlaceEnvelopingProjection_surjective F n w)
        ⟨z.val, z.2, rfl⟩
    obtain ⟨c, hc⟩ := complexStandardLie_hasInfinitesimalCharacter n ds _ hz
    change ArchimedeanGL.envelopingAction F n z.val (liftStandard w f) ∈ _
    rw [liftStandard_enveloping, hc, Module.algebraMap_end_apply, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · apply compactGroupFiniteDifferential F n
    let Q := FiniteVectors.orbitSpan (complexStandardRep n ds) f
    have : Module.Finite ℂ Q := (isComplexGKModule_complexStandardModule n ds).1 f
    apply Submodule.finiteDimensional_of_le (S₂ := Q.map (liftStandard w))
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change smoothRightAction F n k.val (liftStandard w f) ∈ _
    rw [liftStandard_compact]
    exact Submodule.mem_map_of_mem (FiniteVectors.action_mem_orbitSpan _ _ _)

private def liftPair (w : CP) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) : Std →ₗ[ℂ] Fam :=
  LinearMap.pi fun b => (toSmooth F n).symm.toLinearMap.comp
    (Bool.rec (liftStandard w) (liftIntertwiner w B hB) b)

private theorem liftPair_compact (w : CP) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) (k : K) (f : Std) :
    compactRepresentation k (liftPair w B hB f) =
      liftPair w B hB (complexStandardRep n ds (compactProjection w k) f) := by
  funext b
  apply (toSmooth F n).injective
  rw [ArchimedeanGL.SmoothFamily.compactRepresentation_apply, compactAction_apply, toSmooth_rightAction]
  cases b
  · simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using liftStandard_compact w k f
  · have h := Representation.IntertwiningMap.isIntertwining _ _ (liftCompactIntertwiner w B hB) k f
    change liftIntertwiner w B hB (complexStandardRep n ds (compactProjection w k) f) =
      smoothRightAction F n k.val (liftIntertwiner w B hB f) at h
    simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using h.symm

private theorem liftPair_enveloping (w : CP) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) (q : EnvelopingAlgebra F n) (f : Std) :
    q • liftPair w B hB f =
      liftPair w B hB (Langlands.Archimedean.envelopingAction (complexStandardLie n ds)
        (complexPlaceEnvelopingProjection F n w q) f) := by
  funext b
  apply (toSmooth F n).injective
  change toSmooth F n (operator F n q ((liftPair w B hB f) b)) = _
  rw [toSmooth_operator]
  cases b
  · simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using liftStandard_enveloping w q f
  · simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using liftIntertwiner_enveloping w B hB q f

private theorem liftPair_eval (w : CP) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : Std) (g : A) :
    evalCLM F n g (liftPair w B hB f false) = f.val (projection w g) ∧
    evalCLM F n g (liftPair w B hB f true) = B f (projection w g) := by
  simp only [evalCLM_apply, liftPair, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact ⟨rfl, rfl⟩

private theorem liftPair_compactFinite (w : CP) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : Std) :
    FiniteDimensional ℂ (FiniteVectors.orbitSpan (compactRepresentation (ι := Bool)) (liftPair w B hB f)) := by
  let Q := FiniteVectors.orbitSpan (complexStandardRep n ds) f
  have : Module.Finite ℂ Q := (isComplexGKModule_complexStandardModule n ds).1 f
  apply Submodule.finiteDimensional_of_le (S₂ := Q.map (liftPair w B hB))
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  change compactRepresentation k (liftPair w B hB f) ∈ _
  rw [liftPair_compact]
  exact Submodule.mem_map_of_mem (FiniteVectors.action_mem_orbitSpan _ _ _)

private def placeCompactMap (w : CP) : C(U, A) :=
  ⟨fun k => (complexPlaceCompactInclusion F n w ⟨k.val.val, k.2⟩).val,
    continuous_subtype_val.comp ((complexPlaceCompactInclusion F n w).continuous.comp
      ((Units.continuous_val.comp continuous_subtype_val).subtype_mk _))⟩

omit [NumberField F] in
private theorem placeCompactMap_mem (w : CP) (k : U) : placeCompactMap w k ∈ K :=
  (complexPlaceCompactInclusion F n w ⟨k.val.val, k.2⟩).2

omit [NumberField F] in
private theorem projection_placeCompactMap (w : CP) (k : U) : projection w (placeCompactMap w k) = k.val := by
  have h := complexPlaceGL_unitary w (⟨k.val.val, k.2⟩ : Matrix.unitaryGroup (Fin n) ℂ)
  have he : placeCompactMap w k = inclusion w k.val := by
    change (complexPlaceCompactInclusion F n w ⟨k.val.val, k.2⟩).val = _
    apply (archimedeanGLCoordinates F n).injective
    change _ = archimedeanGLCoordinates F n
      ((archimedeanGLCoordinates F n).symm (complexPlaceGL F n w k.val))
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact h.symm.trans (congrArg (complexPlaceGL F n w) (Units.ext rfl))
  rw [he, projection_inclusion]

set_option maxHeartbeats 1600000 in
private theorem compact_projection_atPlace (w : CP) (ν : Measure U) [ν.IsHaarMeasure]
    (κ : C(U, ℂ)) (hκ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun h : U => fun k => κ (h⁻¹ * k)))) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : Std) (g : G) :
    ∃ p : Std, (∀ x : G, p.val x = ∫ k : U, κ k * f.val (x * k.val * g) ∂ν) ∧
      ∀ x : G, B p x = ∫ k : U, κ k * B f (x * k.val * g) ∂ν := by
  let L := liftPair w B hB
  let Q := LinearMap.range L
  let j := placeCompactMap (r := r) w
  let P : Fam →ₗ[ℂ] Fam := averageLM j ν κ
  have hstab (k : K) (q : EnvelopingAlgebra F n) (v : Fam) (hv : v ∈ Q) :
      compactRepresentation k (q • v) ∈ Q := by
    obtain ⟨v, rfl⟩ := hv
    change compactRepresentation k (q • liftPair w B hB v) ∈ Q
    rw [liftPair_enveloping, liftPair_compact]
    exact LinearMap.mem_range_self _ _
  have hfin (v : Fam) (hv : v ∈ Q) : FiniteDimensional ℂ
      (FiniteVectors.orbitSpan compactRepresentation v) := by
    obtain ⟨v, rfl⟩ := hv
    exact liftPair_compactFinite w B hB v
  have hPQ : Q.map P ≤ Q := by
    apply Submodule.map_le_iff_le_comap.mpr
    intro v hv
    let O := FiniteVectors.orbitSpan (compactRepresentation (ι := Bool)) v
    have : FiniteDimensional ℂ O := hfin v hv
    have hO : O ≤ Q := Submodule.span_le.mpr (by
      rintro _ ⟨k, rfl⟩
      change compactRepresentation k v ∈ Q
      simpa only [one_smul] using hstab k 1 v hv)
    have ha : P v ∈ O.topologicalClosure := by
      apply ArchimedeanGL.SmoothFamily.averageLM_mem_topologicalClosure
      intro k
      exact O.le_topologicalClosure
        (FiniteVectors.action_mem_orbitSpan compactRepresentation ⟨j k, placeCompactMap_mem w k⟩ v)
    rw [O.closed_of_finiteDimensional.submodule_topologicalClosure_eq] at ha
    exact hO ha
  let E : Fam →ₗ[ℂ] (U → ℂ) :=
    LinearMap.pi fun k => (evalCLM F n (inclusion w k.val)).toLinearMap.comp (LinearMap.proj false)
  have hE_inj : Function.Injective (E.comp Q.subtype) := by
    rintro ⟨v, hv⟩ ⟨v', hv'⟩ he
    obtain ⟨f₁, rfl⟩ := hv
    obtain ⟨f₂, rfl⟩ := hv'
    have hEq : f₁ = f₂ := by
      apply Subtype.ext
      apply ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary f₁.2.1 f₂.2.1
      intro k hk
      have eq := congrFun he (⟨k, hk⟩ : U)
      change evalCLM F n (inclusion w k) (liftPair w B hB f₁ false) =
        evalCLM F n (inclusion w k) (liftPair w B hB f₂ false) at eq
      rw [(liftPair_eval w B hB f₁ _).1, (liftPair_eval w B hB f₂ _).1, projection_inclusion] at eq
      exact eq
    subst f₂
    rfl
  obtain ⟨d, α, β, hβ, hsep⟩ :=
    hasFiniteCompactConvolutionKernel_of_finite_translates κ κ.continuous hκ
  let T := Submodule.span ℂ (Set.range α)
  have : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range α)
  have hET (v : Fam) (hv : v ∈ Q.map P) : E v ∈ T := by
    obtain ⟨v, hv, rfl⟩ := hv
    obtain ⟨f, rfl⟩ := hv
    have he : E (P (L f)) = ∑ l, (∫ k : U, β l k * f.val k.val ∂ν) • α l := by
      funext x
      change evalCLM F n (inclusion w x.val) (P (L f) false) = _
      rw [show P (L f) false = CompactIndexAverage.averageLM j ν κ (L f false) from rfl,
        CompactIndexAverage.eval_averageLM]
      simp only [L, (liftPair_eval w B hB f _).1, map_mul, projection_inclusion,
        projection_placeCompactMap, j]
      have hs : (∫ k : U, κ (x⁻¹ * k) * f.val k.val ∂ν) =
          ∑ l, α l x * (∫ k : U, β l k * f.val k.val ∂ν) := by
        simp_rw [hsep, Finset.sum_mul, mul_assoc]
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl (fun l _ => integral_const_mul _ _)
        · intro l _
          exact (((hβ l).mul (f.2.1.1.continuous.comp continuous_subtype_val)).const_mul
            (α l x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [show (∫ k : U, κ k * f.val (x.val * k.val) ∂ν) =
        ∫ k : U, κ (x⁻¹ * k) * f.val k.val ∂ν by
          rw [← integral_mul_left_eq_self (fun k : U => κ (x⁻¹ * k) * f.val k.val) x]
          simp only [inv_mul_cancel_left]; rfl, hs]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [he]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hRank : FiniteDimensional ℂ (Q.map P) := by
    let e : (Q.map P) →ₗ[ℂ] T := (E.comp (Q.map P).subtype).codRestrict T (fun v => hET v v.2)
    have hi : Function.Injective e := by
      intro u v h
      have hh := hE_inj (show E.comp Q.subtype ⟨u.val, hPQ u.2⟩ =
        E.comp Q.subtype ⟨v.val, hPQ v.2⟩ from congrArg Subtype.val h)
      exact Subtype.ext (congrArg (fun z : Q => z.val) hh)
    exact FiniteDimensional.of_injective e hi
  have hjoint (b : Bool) : IsJointFinite F n (toSmooth F n (L f b)) := by
    cases b
    · simpa only [L, liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using liftStandard_jointFinite w f
    · simpa only [L, liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using liftIntertwiner_jointFinite w B hB f
  obtain ⟨p, hp⟩ := averagedTranslate_mem j ν κ Q hstab (placeCompactMap_mem w) hfin hRank
    (LinearMap.mem_range_self L f) hjoint (inclusion w g)
  refine ⟨p, fun x => ?_, fun x => ?_⟩
  · have h := congrArg (fun v : Fam => evalCLM F n (inclusion w x) (v false)) hp
    change evalCLM F n (inclusion w x) (L p false) =
      evalCLM F n (inclusion w x) (P (rightRepresentation (inclusion w g) (L f)) false) at h
    rw [show P (rightRepresentation (inclusion w g) (L f)) false =
      CompactIndexAverage.averageLM j ν κ (rightAction F n (inclusion w g) (L f false)) from rfl,
      CompactIndexAverage.eval_averageLM] at h
    simpa only [L, (liftPair_eval w B hB _ _).1, evalCLM_rightAction, map_mul,
      projection_inclusion, j, projection_placeCompactMap] using h
  · have h := congrArg (fun v : Fam => evalCLM F n (inclusion w x) (v true)) hp
    change evalCLM F n (inclusion w x) (L p true) =
      evalCLM F n (inclusion w x) (P (rightRepresentation (inclusion w g) (L f)) true) at h
    rw [show P (rightRepresentation (inclusion w g) (L f)) true =
      CompactIndexAverage.averageLM j ν κ (rightAction F n (inclusion w g) (L f true)) from rfl,
      CompactIndexAverage.eval_averageLM] at h
    simpa only [L, (liftPair_eval w B hB _ _).2, evalCLM_rightAction, map_mul,
      projection_inclusion, j, projection_placeCompactMap] using h

variable (r) in
/-- Compact convolution of a genuine translate gives a compact-finite standard vector,
and exact Whittaker intertwiners commute with this operation on both function spaces. -/
def ComplexWhittakerCompactProjectionStatement : Prop :=
  ∀ (ds : List ComplexCharacterData) (a : ℂˣ) (ν : Measure U), ν.IsHaarMeasure →
  ∀ (κ : C(U, ℂ)),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : U => fun k => κ (h⁻¹ * k))) →
  ∀ (B : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ] (G → ℂ)),
    IsComplexWhittakerIntertwiner r ds a B →
  ∀ (f : Automorphic.complexStandardKFinite (r + 1) ds) (g : G),
    ∃ p : Automorphic.complexStandardKFinite (r + 1) ds,
      (∀ x : G, p.val x = ∫ k : U, κ k * f.val (x * k.val * g) ∂ν) ∧
      ∀ x : G, B p x = ∫ k : U, κ k * B f (x * k.val * g) ∂ν

theorem complexWhittakerCompactProjection : ComplexWhittakerCompactProjectionStatement r := by
  intro ds a ν hν κ hκ B hB f g
  let F : Type := ℚ⟮Complex.I⟯
  have : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional (Complex.isIntegral_I ℚ)
  have : NumberField F := {}
  let e : F →+* ℂ := algebraMap F ℂ
  have he : InfinitePlace.IsComplex (InfinitePlace.mk e) := by
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff]
    intro h
    let i : F := ⟨Complex.I, IntermediateField.mem_adjoin_simple_self ℚ _⟩
    have hi := congrArg (fun f : F →+* ℂ => (f i).im) h
    change (starRingEnd ℂ Complex.I).im = Complex.I.im at hi
    norm_num at hi
  exact compact_projection_atPlace ⟨InfinitePlace.mk e, he⟩ ν κ hκ B hB f g

end CompactAverage

section Growth

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}
variable {ds : List ComplexCharacterData} {a : ℂˣ}

local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "n" => (r + 1)
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "V" => complexWhittakerModel r ds a
local notation "R" => complexWhittakerRightDerivative r ds a

private def liftWord (w : CP) (Xs : List Mat) : EnvelopingAlgebra F n :=
  (Xs.map fun X => envelopingGenerator F n (complexify F n (complexPlaceLieInclusion F n w X))).prod

private theorem liftModel_derivative (w : CP) (X : Mat) (W : V) :
    smoothDifferential F n (complexPlaceLieInclusion F n w X) (liftModel w W) =
      liftModel w (R X W) := by
  apply Subtype.ext
  funext g
  change (smoothDifferential F n (complexPlaceLieInclusion F n w X)
      (liftSmooth w W.val (contMDiff_of_mem_complexWhittakerModel W.2))).val g =
    rightDerivative (matrixModel ℂ n) X W.val (projection w g)
  rw [smoothDifferential_lift, complexProjection_complexInclusion, Pi.single_eq_same]

private theorem liftModel_derivativeWord (w : CP) (Xs : List Mat) (W : V) :
    ArchimedeanGL.envelopingAction F n (liftWord w Xs) (liftModel w W) =
      liftModel w ((Xs.map R).prod W) := by
  induction Xs with
  | nil => simp [liftWord]
  | cons X Xs ih =>
    rw [show liftWord w (X :: Xs) =
      envelopingGenerator F n (complexify F n (complexPlaceLieInclusion F n w X)) * liftWord w Xs
      from rfl, ArchimedeanGL.envelopingAction_mul, ih, envelopingAction_real_generator,
      liftModel_derivative, List.map_cons, List.prod_cons, Module.End.mul_apply]

private theorem uniformGrowthAtPlace (w : CP) (W : V) :
    ∃ N : ℕ, ∀ Xs : List Mat, ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : Langlands.GeneralLinear n ℂ,
        ‖((Xs.map R).prod W).val g‖ ≤ C * max 1 (complexMatrixHeight g) ^ N := by
  obtain ⟨C, d, hC, hg⟩ := complexWhittakerModel_moderateGrowth W.2
  let A := 1 + 2 * ((r + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbound (g : InfiniteAdelicGL F n) :
      ‖(liftModel w W).val g‖ ≤ (C * A ^ d) * matrixHeight F n g ^ (2 * d) := by
    change ‖W.val (projection w g)‖ ≤ _
    calc
      _ ≤ C * max 1 (complexMatrixHeight (projection w g)) ^ d := hg _
      _ ≤ C * (A * matrixHeight F n g ^ 2) ^ d :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (height_projection w g) _) hC
      _ = _ := by rw [mul_pow, pow_mul, mul_assoc]
  obtain ⟨hK, hZ⟩ := liftModel_finite w W
  refine ⟨2 * d, fun Xs => ?_⟩
  obtain ⟨D, hD, hgrowth⟩ := @finiteUniformDifferentialGrowth F _ _ n
    (liftModel w W) hK hZ (C * A ^ d) (mul_nonneg hC (pow_nonneg hA _)) (2 * d)
    hbound (liftWord w Xs)
  refine ⟨D * (1 + ((r + 1 : ℕ) : ℝ)) ^ (2 * d), by positivity, fun g => ?_⟩
  have h := hgrowth (inclusion w g)
  rw [liftModel_derivativeWord] at h
  change ‖((Xs.map R).prod W).val (projection w (inclusion w g))‖ ≤ _ at h
  rw [projection_inclusion] at h
  exact h.trans (by
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (one_le_matrixHeight F n _)) (height_inclusion w g) _) hD)

end Growth

end ComplexLocalWhittakerGrowth

open ComplexLocalWhittakerGrowth

/-- One matrix-height exponent bounds every finite word of real right derivatives of a vector
of the complex local Whittaker model. -/
def ComplexWhittakerUniformDerivativeGrowthStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ) (W : complexWhittakerModel r ds a),
    ∃ N : ℕ, ∀ Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : Langlands.GeneralLinear (r + 1) ℂ,
        ‖((Xs.map (complexWhittakerRightDerivative r ds a)).prod W).val g‖ ≤
          C * max 1 (complexMatrixHeight g) ^ N

theorem complexWhittakerUniformDerivativeGrowth : ComplexWhittakerUniformDerivativeGrowthStatement := by
  intro r ds a W
  let F : Type := ℚ⟮Complex.I⟯
  have : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional (Complex.isIntegral_I ℚ)
  have : NumberField F := {}
  let e : F →+* ℂ := algebraMap F ℂ
  have he : InfinitePlace.IsComplex (InfinitePlace.mk e) := by
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff]
    intro h
    let i : F := ⟨Complex.I, IntermediateField.mem_adjoin_simple_self ℚ _⟩
    have hi := congrArg (fun f : F →+* ℂ => (f i).im) h
    change (starRingEnd ℂ Complex.I).im = Complex.I.im at hi
    norm_num at hi
  exact uniformGrowthAtPlace ⟨InfinitePlace.mk e, he⟩ W

/-- Evaluation at the identity on the compact-finite standard vectors determines an exact
complex Whittaker intertwiner. -/
def ComplexWhittakerEvaluationStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B C : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℂ → ℂ)),
    IsComplexWhittakerIntertwiner r ds a B → IsComplexWhittakerIntertwiner r ds a C →
    (∀ f, B f 1 = C f 1) → B = C

theorem complexWhittakerEvaluation : ComplexWhittakerEvaluationStatement := by
  intro r ds a B C hB hC h
  let F : Type := ℚ⟮Complex.I⟯
  have : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional (Complex.isIntegral_I ℚ)
  have : NumberField F := {}
  let e : F →+* ℂ := algebraMap F ℂ
  have he : InfinitePlace.IsComplex (InfinitePlace.mk e) := by
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff]
    intro h'
    let i : F := ⟨Complex.I, IntermediateField.mem_adjoin_simple_self ℚ _⟩
    have hi := congrArg (fun f : F →+* ℂ => (f i).im) h'
    change (starRingEnd ℂ Complex.I).im = Complex.I.im at hi
    norm_num at hi
  exact eq_of_eval_atPlace ⟨InfinitePlace.mk e, he⟩ hB hC h

end Langlands.Global.RankinSelbergGlobal
