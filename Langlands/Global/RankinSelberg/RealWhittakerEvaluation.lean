import Langlands.Global.ArchimedeanAnalyticJetProof
import Langlands.Global.ArchimedeanCompactComponentCoverageProof
import Langlands.Global.ArchimedeanCompactGroupFiniteProof
import Langlands.Global.ArchimedeanEnvelopingJetProof
import Langlands.Global.ArchimedeanFiniteUniformGrowthProof
import Langlands.Global.ArchimedeanJointFiniteAnalyticityProof
import Langlands.Global.ArchimedeanPlaceEnveloping
import Langlands.Global.ArchimedeanPlaceRestriction
import Langlands.Global.ArchimedeanSeparateJointFiniteProof
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel
import Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter

/-! # Identity evaluation and derivative growth of real Whittaker intertwiners -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean NumberField
open scoped Classical ContDiff Manifold Matrix.Norms.Operator NNReal TensorProduct

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

private theorem coefficients_finite (v : RP) {a : ℝˣ} {B : D}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : V) :
    IsCenterFinite F n (coefficients F r ds v B hB.2.1 f) ∧
      FiniteVectors.IsFiniteVector
        ((smoothRightAction F n).comp (standardInfiniteCompact F n).subtype)
        (coefficients F r ds v B hB.2.1 f) := by
  let L := coefficients F r ds v B hB.2.1
  constructor
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
  · have : Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan ρ f) :=
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

private theorem coefficients_jointFinite (v : RP) {a : ℝˣ} {B : D}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : V) :
    IsJointFinite F n (coefficients F r ds v B hB.2.1 f) := by
  obtain ⟨hZ, hK⟩ := coefficients_finite F r ds v hB f
  exact separateJointFinite F n _ hZ (compactGroupFiniteDifferential F n _ hK)

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

private def inclusion (v : RP) : G →* AG :=
  (archimedeanGLCoordinates F n).symm.toMonoidHom.comp (realPlaceGL F n v)

omit [NumberField F] in
private theorem projection_inclusion (v : RP) (g : G) :
    projection F r v (inclusion F r v g) = g := by
  apply Units.ext
  change matrixProjection F r v
    (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm
      (realPlaceGL F n v g))).val = g.val
  rw [ContinuousMulEquiv.apply_symm_apply, realPlaceGL_val]
  ext i j
  change (Pi.mulSingle v g.val : RP → M) v i j = g.val i j
  rw [Pi.mulSingle_eq_same]

private theorem norm_projection_entry (v : RP) (g : AG) (i j : Fin n) :
    ‖(projection F r v g).val i j‖ ≤ matrixHeight F n g := by
  let x := (archimedeanGLCoordinates F n g).val i j
  change ‖x.1 v‖ ≤ _
  exact (norm_le_pi_norm x.1 v).trans ((norm_fst_le x).trans
    ((ArchimedeanGL.norm_entry_le (archimedeanGLCoordinates F n g).val i j).trans
      (norm_val_le_matrixHeight F n g)))

private theorem height_projection (v : RP) (g : AG) :
    realMatrixHeight (projection F r v g) ≤ (2 * (n : ℝ) * n) * matrixHeight F n g ^ 2 := by
  unfold realMatrixHeight
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (matrixHeight F n g ^ 2 + matrixHeight F n g ^ 2) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => add_le_add
        (pow_le_pow_left₀ (norm_nonneg _) (norm_projection_entry F r v g i j) _) ?_
      rw [← map_inv]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_projection_entry F r v g⁻¹ i j).trans_eq (matrixHeight_inv F n g)) _
    _ = _ := by simp; ring

private theorem rowNorm_le_rank_mul (X : A) (b : ℝ) (hb : 0 ≤ b)
    (hX : ∀ i j, ‖X i j‖ ≤ b) : ‖X‖ ≤ (n : ℝ) * b := by
  let B : ℝ≥0 := ⟨b, hb⟩
  have h : ‖X‖₊ ≤ (n : ℝ≥0) * B := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    have hs : (∑ j, ‖X i j‖₊) ≤ ∑ _j : Fin n, B := by
      apply Finset.sum_le_sum
      intro j _
      exact_mod_cast hX i j
    simpa [nsmul_eq_mul] using hs
  exact_mod_cast h

private theorem norm_inclusion_entry (v : RP) (g : G) (i j : Fin n) :
    ‖(realPlaceGL F n v g).val i j‖ ≤ realMatrixHeight g := by
  have h₁ : (1 : ℝ) ≤ realMatrixHeight g :=
    le_trans (by norm_num) (RealPlaceRestriction.two_le_realMatrixHeight (Nat.succ_pos r) g)
  have hb : 0 ≤ realMatrixHeight g := zero_le_one.trans h₁
  rw [realPlaceGL_val]
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg hb).mpr
    intro w
    change ‖(Pi.mulSingle v g.val : RP → M) w i j‖ ≤ realMatrixHeight g
    by_cases h : w = v
    · subst w
      rw [Pi.mulSingle_eq_same]
      exact RealPlaceRestriction.norm_entry_le_realMatrixHeight (Nat.succ_pos r) g i j
    · rw [Pi.mulSingle_eq_of_ne h, Matrix.one_apply]
      split_ifs <;> simp [h₁, hb]
  · apply (pi_norm_le_iff_of_nonneg hb).mpr
    intro w
    change ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ realMatrixHeight g
    rw [Matrix.one_apply]
    split_ifs <;> simp [h₁, hb]

private theorem height_inclusion (v : RP) (g : G) :
    matrixHeight F n (inclusion F r v g) ≤ (n : ℝ) * realMatrixHeight g := by
  have hval (x : G) :
      ‖(archimedeanGLCoordinates F n (inclusion F r v x)).val‖ ≤ (n : ℝ) * realMatrixHeight x := by
    change ‖(archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm
      (realPlaceGL F n v x))).val‖ ≤ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact rowNorm_le_rank_mul F r _ _ (RealPlaceRestriction.realMatrixHeight_nonneg _)
      (norm_inclusion_entry F r v x)
  have hi := hval g⁻¹
  rw [map_inv, map_inv, RealPlaceRestriction.realMatrixHeight_inv] at hi
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le r))
  unfold matrixHeight
  exact max_le
    (one_le_mul_of_one_le_of_one_le hn
      (le_trans (by norm_num) (RealPlaceRestriction.two_le_realMatrixHeight (Nat.succ_pos r) g)))
    (max_le (hval g) hi)

private def liftWord (v : RP) (Xs : List M) : EnvelopingAlgebra F n :=
  (Xs.map fun X => envelopingGenerator F n (complexify F n (realPlaceLieInclusion F n v X))).prod

private theorem liftWord_apply (v : RP) (Xs : List M) (W : G → ℂ)
    (hW : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ W) (g : AG) :
    (ArchimedeanGL.envelopingAction F n (liftWord F r v Xs) (pullback F r v W hW)).val g =
      RealLocalWhittaker.iteratedRightDerivative r Xs W (projection F r v g) := by
  induction Xs generalizing g with
  | nil => simp [liftWord, pullback, RealLocalWhittaker.iteratedRightDerivative]
  | cons X Xs ih =>
      have hSmooth := RealUniformWhittaker.contMDiff_iteratedRightDerivative hW Xs
      have he :
          ArchimedeanGL.envelopingAction F n (liftWord F r v Xs) (pullback F r v W hW) =
            pullback F r v (RealLocalWhittaker.iteratedRightDerivative r Xs W) hSmooth :=
        Subtype.ext (funext ih)
      rw [show liftWord F r v (X :: Xs) = envelopingGenerator F n
        (complexify F n (realPlaceLieInclusion F n v X)) * liftWord F r v Xs from rfl,
        ArchimedeanGL.envelopingAction_mul, he,
        envelopingAction_real_generator, pullback_differential, realProjection_realInclusion,
        Pi.single_eq_same]
      rfl

theorem coefficients_uniformDerivativeGrowth (v : RP) {a : ℝˣ} {B : D}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : V) :
    RealUniformWhittaker.HasUniformDerivativeGrowth (B f) := by
  obtain ⟨C, d, hC, hg⟩ := RealLocalWhittaker.HasPolynomialGrowth.of_bound (hB.2.2.1 f)
  let k : ℝ := 2 * (n : ℝ) * n
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hbound (g : AG) :
      ‖(coefficients F r ds v B hB.2.1 f).val g‖ ≤ (C * k ^ d) * matrixHeight F n g ^ (2 * d) := by
    calc
      _ ≤ C * realMatrixHeight (projection F r v g) ^ d := hg _
      _ ≤ C * (k * matrixHeight F n g ^ 2) ^ d :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (RealPlaceRestriction.realMatrixHeight_nonneg _)
            (height_projection F r v g) _) hC
      _ = _ := by rw [mul_pow, pow_mul, mul_assoc]
  obtain ⟨hZ, hK⟩ := coefficients_finite F r ds v hB f
  refine ⟨2 * d, fun Xs => ?_⟩
  obtain ⟨E, hE, he⟩ := @finiteUniformDifferentialGrowth F _ _ n (coefficients F r ds v B hB.2.1 f)
    hK hZ (C * k ^ d) (by positivity) (2 * d) hbound (liftWord F r v Xs)
  refine ⟨E * (n : ℝ) ^ (2 * d), by positivity, fun g => ?_⟩
  have hb := he (inclusion F r v g)
  change ‖(ArchimedeanGL.envelopingAction F n (liftWord F r v Xs)
    (pullback F r v (B f) (hB.2.1 f))).val (inclusion F r v g)‖ ≤ _ at hb
  rw [liftWord_apply, projection_inclusion] at hb
  refine hb.trans ?_
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (matrixHeight_nonneg F n _) (height_inclusion F r v g) _) hE

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

/-- Every exact real Whittaker coefficient has one polynomial height exponent for
all its right derivative words. -/
def RealExactWhittakerDerivativeGrowthStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (a : ℝˣ),
    realWhittakerModel r ds a ≤ RealUniformWhittaker.uniformGrowthFunctions r

theorem realExactWhittakerDerivativeGrowth : RealExactWhittakerDerivativeGrowthStatement := by
  intro r ds a
  refine iSup_le fun B => iSup_le fun hB => ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨hB.2.1 f, RealWhittakerEvaluation.coefficients_uniformDerivativeGrowth ℚ r ds
    ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩ hB f⟩

end Langlands.Global.RankinSelbergGlobal
