import Langlands.Global.ArchimedeanAnalyticJetProof
import Langlands.Global.ArchimedeanCompactComponentCoverageProof
import Langlands.Global.ArchimedeanCompactGroupFiniteProof
import Langlands.Global.ArchimedeanEnvelopingJetProof
import Langlands.Global.ArchimedeanJointFiniteAnalyticityProof
import Langlands.Global.ArchimedeanPlaceEnveloping
import Langlands.Global.ArchimedeanSeparateJointFiniteProof
import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter

/-! # Real Whittaker intertwiners are determined by their evaluation at the identity -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean NumberField
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanGL

namespace RealWhittakerEvaluation

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "A" => ArchimedeanMatrix F n
local notation "AG" => Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing F)
local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "S" => SmoothFunctions F n

private def matrixProjection (v : RP) : A →ₐ[ℝ] M :=
  (realPlaceScalarProjection F v).mapMatrix

private def projection (v : RP) : AG →* G :=
  (Matrix.GeneralLinearGroup.map (realPlaceScalarProjection F v).toRingHom).comp
    (archimedeanGLCoordinates F n).toMonoidHom

omit [NumberField F] in
private theorem projection_surjective (v : RP) :
    Function.Surjective (projection F r v) := by
  intro g
  refine ⟨(archimedeanGLCoordinates F n).symm (assemble F n (fun _ => g, fun _ => 1)), ?_⟩
  apply Units.ext
  change matrixProjection F r v
    (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm
      (assemble F n (fun _ => g, fun _ => 1)))).val = g.val
  rw [ContinuousMulEquiv.apply_symm_apply]
  rfl

private def compactProjection (v : RP) (k : standardInfiniteCompact F n) :
    Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨(projection F r v k.val).val, ((mem_standardInfiniteCompact_iff F n k.val).mp k.property).1 v⟩

omit [NumberField F] in
private theorem toUnits_compactProjection (v : RP) (k : standardInfiniteCompact F n) :
    Unitary.toUnits (compactProjection F r v k) = projection F r v k.val :=
  Units.ext rfl

private def pullback (v : RP) (W : G → ℂ)
    (hW : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ W) : S := by
  refine ⟨W ∘ projection F r v, ?_⟩
  let P := (matrixProjection F r v).toLinearMap.toContinuousLinearMap
  have hP : Set.MapsTo P {x : A | IsUnit x} {x : M | IsUnit x} :=
    fun _ hx => (show IsUnit _ from hx).map (matrixProjection F r v)
  have hPdiff : ContDiff ℝ ∞ (P : A → M) := P.contDiff
  have hExt : ContDiffOn ℝ ∞ (unitsExtension W ∘ P) {x : A | IsUnit x} :=
    (contDiffOn_unitsExtension hW).comp hPdiff.contDiffOn hP
  have hVal : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ (Units.val : ArchimedeanGL F n → A) :=
    Units.contMDiff_val
  have hSmooth := (contMDiffOn_iff_contDiffOn.mpr hExt).comp_contMDiff hVal
    (fun g => g.isUnit)
  change ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞
    (fun x : ArchimedeanGL F n =>
      W (projection F r v ((archimedeanGLCoordinates F n).symm x)))
  refine hSmooth.congr ?_
  intro x
  rw [Function.comp_apply, Function.comp_apply]
  have heq : P x.val =
      (projection F r v ((archimedeanGLCoordinates F n).symm x)).val := by
    change matrixProjection F r v x.val = matrixProjection F r v
      (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm x)).val
    rw [ContinuousMulEquiv.apply_symm_apply]
  exact ((congrArg (unitsExtension W) heq).trans (unitsExtension_val W _)).symm

private theorem pullback_differential (v : RP) (X : RealLieAlgebra F n) (W : G → ℂ)
    (hW : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ W) (g : AG) :
    (smoothDifferential F n X (pullback F r v W hW)).val g =
      rightDerivative (matrixModel ℝ n) (realPlaceLieProjection F n v X)
        W (projection F r v g) := by
  let P := (matrixProjection F r v).toLinearMap.toContinuousLinearMap
  let x : A := (archimedeanGLCoordinates F n g).val
  let E := unitsExtension W ∘ P
  have hE (h : ArchimedeanGL F n) :
      E h.val = (pullback F r v W hW).val ((archimedeanGLCoordinates F n).symm h) := by
    change unitsExtension W (matrixProjection F r v h.val) = W
      (projection F r v ((archimedeanGLCoordinates F n).symm h))
    have hh : matrixProjection F r v h.val =
        (projection F r v ((archimedeanGLCoordinates F n).symm h)).val := by
      change _ = matrixProjection F r v
        (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm h)).val
      rw [ContinuousMulEquiv.apply_symm_apply]
    rw [hh, unitsExtension_val]
  rw [smoothDifferential_eq_of_extension F n X _ E hE,
    rightDerivative_eq_fderiv hW]
  have hPx : P x = (projection F r v g).val := rfl
  have hd : DifferentiableAt ℝ (unitsExtension W) (P x) :=
    differentiableAt_unitsExtension hW (hPx ▸ (projection F r v g).isUnit)
  have hPd : HasFDerivAt (P : A → M) P x := P.hasFDerivAt
  have hD : fderiv ℝ E x = (fderiv ℝ (unitsExtension W) (P x)).comp P :=
    (hd.hasFDerivAt.comp x hPd).fderiv
  change fderiv ℝ E x _ = _
  rw [hD, ContinuousLinearMap.comp_apply]
  change fderiv ℝ (unitsExtension W) (P x)
    (matrixProjection F r v (x * realLieAlgebraToMatrix F n X)) = _
  rw [map_mul]
  rfl

variable (ds : List RealBlock)

local notation "V" => Automorphic.realStandardKFinite n ds
local notation "D" => V →ₗ[ℂ] (G → ℂ)
local notation "ρ" => realStandardRep n ds
local notation "π" => realStandardLie n ds

private def coefficients (v : RP) (B : D)
    (hB : ∀ f : V, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (B f)) : V →ₗ[ℂ] S where
  toFun f := pullback F r v (B f) (hB f)
  map_add' f e := by apply Subtype.ext; funext g; exact congrFun (map_add B f e) _
  map_smul' z f := by apply Subtype.ext; funext g; exact congrFun (map_smul B z f) _

private theorem coefficients_enveloping (v : RP) {a : ℝˣ} {B : D}
    (hB : IsRealWhittakerIntertwiner r ds a B) (u : EnvelopingAlgebra F n) (f : V) :
    ArchimedeanGL.envelopingAction F n u (coefficients F r ds v B hB.2.1 f) =
      coefficients F r ds v B hB.2.1
        (Archimedean.envelopingAction π (realPlaceEnvelopingProjection F n v u) f) := by
  induction u using Archimedean.InfinitesimalCharacter.envInduction generalizing f with
  | algebraMap z =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | ι Z =>
    change ArchimedeanGL.envelopingAction F n (envelopingGenerator F n Z) _ =
      coefficients F r ds v B hB.2.1
        (Archimedean.envelopingAction π
          (realPlaceEnvelopingProjection F n v (envelopingGenerator F n Z)) f)
    rw [envelopingAction_generator, realPlaceEnvelopingProjection_generator]
    rw [realPlaceEnvelopingGenerator, Archimedean.envelopingAction,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      have hZ : (z ⊗ₜ[ℝ] realPlaceLieProjection F n v X : ℂ ⊗[ℝ] M) =
          z • ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [complexSmoothLieAction_tmul, realPlaceComplexLieProjection_tmul, hZ,
        map_smul, LinearMap.smul_apply]
      congr 1
      apply Subtype.ext
      funext g
      change (smoothDifferential F n X (pullback F r v (B f) (hB.2.1 f))).val g =
        B (π ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) f) (projection F r v g)
      rw [pullback_differential F r v X (B f) (hB.2.1 f)]
      exact (congrFun (hB.2.2.2.2 _ f _ (realStandardLie_one_tmul_apply_coe n ds _ f)) _).symm
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply, hX, hY]
  | mul u w hu hw =>
    rw [envelopingAction_mul, hw, hu, map_mul, map_mul, Module.End.mul_apply]
  | add u w hu hw =>
    simp only [map_add, LinearMap.add_apply, hu, hw]

private theorem coefficients_compact (v : RP) {a : ℝˣ} {B : D}
    (hB : IsRealWhittakerIntertwiner r ds a B) (k : standardInfiniteCompact F n) (f : V) :
    smoothRightAction F n k.val (coefficients F r ds v B hB.2.1 f) =
      coefficients F r ds v B hB.2.1 (ρ (compactProjection F r v k) f) := by
  let k' : unitaryCompact ℝ n := ⟨Unitary.toUnits (compactProjection F r v k),
    (compactProjection F r v k).property⟩
  apply Subtype.ext
  funext g
  change B f (projection F r v (g * k.val)) =
    B (ρ (compactProjection F r v k) f) (projection F r v g)
  rw [hB.2.2.2.1 k' f _ (realStandardRep_apply_coe n ds _ f), map_mul]
  change B f (_ * _) = B f (_ * Unitary.toUnits (compactProjection F r v k))
  rw [toUnits_compactProjection]

omit [NumberField F] in
private theorem projection_mem_center (v : RP) (z : EnvelopingCenter F n) :
    realPlaceEnvelopingProjection F n v z.val ∈
      Subalgebra.center ℂ (RealPlaceEnvelopingAlgebra n) := by
  rw [Subalgebra.mem_center_iff]
  intro w
  obtain ⟨u, rfl⟩ := realPlaceEnvelopingProjection_surjective F n v w
  simpa only [map_mul] using congrArg (realPlaceEnvelopingProjection F n v)
    ((Subalgebra.mem_center_iff.mp z.property) u)

private theorem coefficients_jointFinite (v : RP) {a : ℝˣ} {B : D}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : V) :
    IsJointFinite F n (coefficients F r ds v B hB.2.1 f) := by
  let L := coefficients F r ds v B hB.2.1
  apply separateJointFinite F n (L f)
  · have hle : centerOrbitSpan F n (L f) ≤ Submodule.span ℂ {L f} := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, rfl⟩
      change ArchimedeanGL.envelopingAction F n z.val (L f) ∈ Submodule.span ℂ {L f}
      rw [coefficients_enveloping F r ds v hB]
      obtain ⟨c, hc⟩ := realStandardLie_hasInfinitesimalCharacter n ds _
        (projection_mem_center F r v z)
      rw [hc, Module.algebraMap_end_apply, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    exact Submodule.finiteDimensional_of_le hle
  · apply compactGroupFiniteDifferential F n (L f)
    have : Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan ρ f) :=
      (isRealGKModule_realStandardModule n ds).1 f
    have hle : Langlands.FiniteVectors.orbitSpan
        ((smoothRightAction F n).comp (standardInfiniteCompact F n).subtype) (L f) ≤
        (Langlands.FiniteVectors.orbitSpan ρ f).map L := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      change smoothRightAction F n k.val (L f) ∈ _
      rw [coefficients_compact F r ds v hB]
      exact Submodule.mem_map_of_mem
        (Langlands.FiniteVectors.action_mem_orbitSpan ρ (compactProjection F r v k) f)
    exact Submodule.finiteDimensional_of_le hle

private theorem coefficients_eval_compact (v : RP) {a : ℝˣ} {B : D}
    (hB : IsRealWhittakerIntertwiner r ds a B) (k : standardInfiniteCompact F n) (f : V) :
    (coefficients F r ds v B hB.2.1 f).val k.val =
      B (ρ (compactProjection F r v k) f) 1 := by
  have h := congrArg (fun z : S => z.val (1 : AG)) (coefficients_compact F r ds v hB k f)
  change B f (projection F r v (1 * k.val)) =
    B (ρ (compactProjection F r v k) f) (projection F r v 1) at h
  change B f (projection F r v k.val) = _
  simpa only [one_mul, map_one] using h

theorem eq_of_eval (v : RP) {a : ℝˣ} {B C : D}
    (hB : IsRealWhittakerIntertwiner r ds a B) (hC : IsRealWhittakerIntertwiner r ds a C)
    (h : ∀ f : V, B f 1 = C f 1) : B = C := by
  apply LinearMap.ext
  intro f
  funext g
  obtain ⟨x, rfl⟩ := projection_surjective F r v g
  let F₀ := coefficients F r ds v B hB.2.1 f - coefficients F r ds v C hC.2.1 f
  have hFin : IsJointFinite F n F₀ := (jointFiniteFunctions F n).sub_mem
    (coefficients_jointFinite F r ds v hB f) (coefficients_jointFinite F r ds v hC f)
  obtain ⟨k, hx⟩ := compactComponentCoverage F n x
  have hZero (u : EnvelopingAlgebra F n) :
      (ArchimedeanGL.envelopingAction F n u F₀).val k.val = 0 := by
    simp only [F₀, map_sub, Submodule.coe_sub, Pi.sub_apply,
      coefficients_enveloping F r ds v hB, coefficients_enveloping F r ds v hC,
      coefficients_eval_compact F r ds v hB, coefficients_eval_compact F r ds v hC, h, sub_self]
  have hx₀ := analyticMatrixJetUniqueness F n F₀ k.val
    (jointFiniteAnalyticity F n F₀ hFin) (envelopingZeroJet F n F₀ k.val hZero) x hx
  exact sub_eq_zero.mp hx₀

end RealWhittakerEvaluation

/-- Evaluation at the identity on all source vectors determines a specified real Whittaker
coefficient map. -/
def RealWhittakerEvaluationStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (a : ℝˣ)
    (B C : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
    IsRealWhittakerIntertwiner r ds a B → IsRealWhittakerIntertwiner r ds a C →
    (∀ f, B f 1 = C f 1) → B = C

theorem realWhittakerEvaluation : RealWhittakerEvaluationStatement := by
  intro r ds a B C hB hC h
  exact RealWhittakerEvaluation.eq_of_eval ℚ r ds ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
    hB hC h

end Langlands.Global.RankinSelbergGlobal
