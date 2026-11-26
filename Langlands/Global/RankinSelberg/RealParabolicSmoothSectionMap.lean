import Langlands.Global.RankinSelberg.RealParabolicLocalizedTests
import Langlands.Global.RankinSelberg.RealBorelAverageContinuity
import Langlands.Global.RankinSelberg.RealWhittakerStandardEvaluation

/-! # Compact transverse tests as genuine smooth real standard vectors -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator Topology BoundedContinuousFunction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open RealStandardCompactBanach RealBruhatDistributionRestriction RealBorelAverageContinuity
open RealBorelTestAverage DerivativeSmoothVectors

private local instance (d : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedAddCommGroup

private local instance (d : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedSpace

local notation "G" => fun d : ℕ => Langlands.GeneralLinear d ℝ
local notation "M" => fun d : ℕ => Matrix (Fin d) (Fin d) ℝ
local notation "X" => fun m n : ℕ => Matrix (Fin m) (Fin n) ℝ

variable {m n : ℕ}

local notation "r" => n + m
local notation "N" => (n + m) + 1
local notation "I" => matrixModel ℝ N
local notation:max "R" ds:max => representation (n := N) ds
local notation:max "D" ds:max => DerivativeSmoothVectors I (R ds)
local notation "U" => Matrix.unitaryGroup (Fin N) ℝ
local notation "KGL" => unitaryCompact ℝ N
local notation "Test" => 𝓓((⊤ : Opens (X (m + 1) n)), ℂ)
local notation "AmbientTest" => 𝓓(invertibleDomain r, ℂ)

private theorem exists_ambientCutoff :
    ∃ (K : Compacts (M N)) (V : Set (M N)) (η : M N → ℂ),
      (K : Set (M N)) ⊆ invertibleDomain r ∧ IsOpen V ∧
      (∀ k : G N, k ∈ KGL → k.val ∈ V) ∧ ContDiff ℝ ∞ η ∧ tsupport η ⊆ K ∧
      ∀ x ∈ V, η x = 1 := by
  let C : Set (M N) := Units.val '' (KGL : Set (G N))
  have hC : IsCompact C :=
    (isCompact_iff_compactSpace.mpr (RealPrincipalSeriesDuality.compactSpace_unitaryCompact N)).image
      Units.continuous_val
  have hCΩ : C ⊆ invertibleDomain r := by rintro _ ⟨k, _, rfl⟩; exact Units.isUnit k
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (continuous_id : Continuous (id : M N → M N)).continuousOn
  let W := (invertibleDomain r : Set (M N)) ∩ Metric.ball 0 (B + 1)
  have hW : IsOpen W := (invertibleDomain r).isOpen.inter Metric.isOpen_ball
  have hCW : C ⊆ W := by
    intro x hx
    exact ⟨hCΩ hx, by rw [Metric.mem_ball, dist_zero_right]; exact (hB x hx).trans_lt (by linarith)⟩
  obtain ⟨O, hO, hCO, hOW⟩ := hC.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hCW)
  have hK : IsCompact (closure O) := (isCompact_closedBall (0 : M N) (B + 1)).of_isClosed_subset
    isClosed_closure (fun x hx => Metric.ball_subset_closedBall (hOW hx).2)
  obtain ⟨V, hV, hCV, hVO⟩ := hC.exists_isOpen_closure_subset (hO.mem_nhdsSet.mpr hCO)
  obtain ⟨f, hf, _, hSupp, hOne⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hO
    (isClosed_closure : IsClosed (closure V)) hVO
  let η : M N → ℂ := fun x => (f x : ℂ)
  refine ⟨⟨closure O, hK⟩, V, η, fun x hx => (hOW hx).1, hV,
    fun k hk => hCV ⟨k, hk, rfl⟩, Complex.ofRealCLM.contDiff.comp hf, ?_, ?_⟩
  · change tsupport η ⊆ closure O
    have : Function.support η = Function.support f := by
      ext x
      simp [η, Function.mem_support]
    rw [tsupport, this, hSupp]
  · intro x hx
    simp only [η, (hOne x).mp (subset_closure hx), Complex.ofReal_one]

private theorem wordTest_eq_iteratedRightDerivative {V : Set (M N)} (hV : IsOpen V)
    (t : AmbientTest) {F : G N → ℂ} (hF : ContMDiff I 𝓘(ℝ, ℂ) ∞ F)
    (he : ∀ u : G N, u.val ∈ V → t u.val = F u) (Xs : List (M N)) :
    ∀ u : G N, u.val ∈ V → rightDerivativeWordTestCLM Xs t u.val =
      RealLocalWhittaker.iteratedRightDerivative r Xs F u := by
  induction Xs generalizing t F with
  | nil => exact he
  | cons Y Xs ih =>
    intro u hu
    let t' := rightDerivativeWordTestCLM Xs t
    let F' := RealLocalWhittaker.iteratedRightDerivative r Xs F
    have hF' : ContMDiff I 𝓘(ℝ, ℂ) ∞ F' :=
      RealUniformWhittaker.contMDiff_iteratedRightDerivative hF Xs
    have hEq : (t' : M N → ℂ) =ᶠ[𝓝 u.val] unitsExtension F' := by
      filter_upwards [hV.mem_nhds hu, isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit u)] with x hx hxU
      obtain ⟨v, rfl⟩ := hxU
      rw [unitsExtension_val]
      exact ih t hF he v hx
    change rightDerivativeTestCLM Y t' u.val = rightDerivative I Y F' u
    rw [rightDerivativeTestCLM_apply, rightDerivativeTest_apply, rightDerivative_eq_fderiv hF', hEq.fderiv_eq]

private def restrictToOrthogonal : (M N →ᵇ ℂ) →L[ℝ] C(U, ℂ) := by
  let L : (M N →ᵇ ℂ) →ₗ[ℝ] C(U, ℂ) :=
    { toFun := fun h => ⟨fun k => h (Unitary.toUnits k).val,
        h.continuous.comp (Units.continuous_val.comp continuous_unitary_toUnits)⟩
      map_add' := fun _ _ => ContinuousMap.ext fun _ => rfl
      map_smul' := fun _ _ => ContinuousMap.ext fun _ => rfl }
  exact L.mkContinuous 1 fun h => by
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun k => h.norm_coe_le_norm _

variable {d₁ d₂ : List RealBlock} (hm : realRank d₁ = m + 1) (hn : realRank d₂ = n)
variable (f : realStandardModule (m + 1) d₁) (g : realStandardModule n d₂)

private def sectionInStandard (φ : Test) : realStandardModule N (d₂ ++ d₁) :=
  ⟨standardSection (m := m + 1) (n := n) f.val g.val φ,
    realParabolicStandardSection (m + 1) n d₁ d₂ hm hn f.val g.val f.2 g.2 φ
      φ.contDiff φ.hasCompactSupport⟩

/-- The actual compact parabolic section in the genuine derivative carrier. -/
def smoothSectionVector (φ : Test) : D (d₂ ++ d₁) :=
  derivativeEquiv _ (sectionInStandard hm hn f g φ)

/-- Reconstruction of the genuine right translate gives the scalar section right translated
in the original group coordinates. -/
theorem reconstruct_translate_smoothSectionVector (φ : Test) (q u : G N) :
    ((derivativeEquiv (d₂ ++ d₁)).symm
      (DerivativeSmoothVectors.representation I (R (d₂ ++ d₁)) q
        (smoothSectionVector hm hn f g φ))).val u =
      standardSection (m := m + 1) (n := n) f.val g.val φ (u * q) := by
  rw [smoothSectionVector, ← derivativeEquiv_translate, LinearEquiv.symm_apply_apply]
  rfl

private theorem continuous_fixedSupportSection (L : Compacts (X (m + 1) n))
    (hL : (L : Set (X (m + 1) n)) ⊆ (⊤ : Opens (X (m + 1) n))) :
    Continuous (fun φ : 𝓓_{L}(X (m + 1) n, ℂ) =>
      smoothSectionVector hm hn f g (TestFunction.ofSupportedIn hL φ)) := by
  obtain ⟨K, V, η, hK, hV, hKV, hη, hηK, hη₁⟩ := exists_ambientCutoff (m := m) (n := n)
  obtain ⟨P, hP⟩ := realParabolicLocalizedTests (m + 1) n d₁ d₂ hm hn f.val g.val f.2 g.2 K
    (fun x hx => hK hx) L η hη hηK
  let J : 𝓓_{K}(M N, ℂ) →L[ℝ] AmbientTest := TestFunction.ofSupportedInCLM ℝ hK
  let Q : 𝓓_{L}(X (m + 1) n, ℂ) →L[ℝ] AmbientTest := J.comp (P.restrictScalars ℝ)
  apply (isEmbedding_derivativeCoordinates I (R (d₂ ++ d₁))).isInducing.continuous_iff.mpr
  apply continuous_pi
  intro Xs
  let B := (restrictToOrthogonal (m := m) (n := n)).comp
    ((TestFunction.toBoundedContinuousFunctionCLM ℝ).comp ((rightDerivativeWordTestCLM Xs).comp Q))
  have hEq : (fun φ : 𝓓_{L}(X (m + 1) n, ℂ) =>
        (derivativeCLM I (R (d₂ ++ d₁)) Xs
          (smoothSectionVector hm hn f g (TestFunction.ofSupportedIn hL φ))).val) = B := by
    funext φ
    apply ContinuousMap.ext
    intro k
    let F := sectionInStandard hm hn f g (TestFunction.ofSupportedIn hL φ)
    change (derivativeCLM I (R (d₂ ++ d₁)) Xs (derivativeEquiv _ F)).val k =
      rightDerivativeWordTestCLM Xs (Q φ) (Unitary.toUnits k).val
    rw [derivativeCLM_compactEval]
    have he (u : G N) (hu : u.val ∈ V) : Q φ u.val = F.val u := by
      change P φ u.val = standardSection (m := m + 1) (n := n) f.val g.val φ u
      rw [hP φ u, hη₁ _ hu, one_mul]
    exact (wordTest_eq_iteratedRightDerivative hV (Q φ) F.2.1.1 he Xs
      (Unitary.toUnits k) (hKV (Unitary.toUnits k) k.property)).symm
  apply continuous_induced_rng.mpr
  change Continuous (fun φ : 𝓓_{L}(X (m + 1) n, ℂ) =>
    (derivativeCLM I (R (d₂ ++ d₁)) Xs
      (smoothSectionVector hm hn f g (TestFunction.ofSupportedIn hL φ))).val)
  rw [hEq]
  exact B.continuous

private theorem standardSection_test_add (φ ψ : Test) (u : G N) :
    standardSection (m := m + 1) (n := n) f.val g.val (φ + ψ) u =
      standardSection (m := m + 1) (n := n) f.val g.val φ u + standardSection (m := m + 1) (n := n) f.val g.val ψ u := by
  unfold standardSection compactSection
  split_ifs
  · exact mul_add _ _ _
  · simp

private theorem standardSection_test_smul (c : ℂ) (φ : Test) (u : G N) :
    standardSection (m := m + 1) (n := n) f.val g.val (c • φ) u = c * standardSection (m := m + 1) (n := n) f.val g.val φ u := by
  unfold standardSection compactSection
  split_ifs
  · exact mul_left_comm _ _ _
  · simp

private theorem sectionInStandard_add (φ ψ : Test) :
    sectionInStandard hm hn f g (φ + ψ) = sectionInStandard hm hn f g φ +
      sectionInStandard hm hn f g ψ :=
  Subtype.ext (funext (standardSection_test_add f g φ ψ))

private theorem sectionInStandard_smul (c : ℂ) (φ : Test) :
    sectionInStandard hm hn f g (c • φ) = c • sectionInStandard hm hn f g φ :=
  Subtype.ext (funext (standardSection_test_smul f g c φ))

/-- Continuity and complex linearity of the smooth section as a function of the compact
transverse test. -/
def smoothSectionMap : Test →L[ℂ] D (d₂ ++ d₁) :=
  TestFunction.mkCLM ℂ (smoothSectionVector hm hn f g)
    (fun φ ψ => by
      simp only [smoothSectionVector, sectionInStandard_add, map_add])
    (fun c φ => by
      simp only [smoothSectionVector, sectionInStandard_smul, map_smul])
    (continuous_fixedSupportSection hm hn f g)

@[simp] theorem smoothSectionMap_apply (φ : Test) :
    smoothSectionMap hm hn f g φ = smoothSectionVector hm hn f g φ := rfl

/-- Compactly supported smooth rectangle tests define a continuous complex-linear family
in the genuine smooth standard module of the concatenated real block list. -/
def RealParabolicSmoothSectionMapStatement : Prop :=
  ∀ (m n : ℕ) (d₁ d₂ : List RealBlock) (hm : realRank d₁ = m + 1) (hn : realRank d₂ = n)
    (f : realStandardModule (m + 1) d₁) (g : realStandardModule n d₂),
    ∃ P : 𝓓((⊤ : Opens (X (m + 1) n)), ℂ) →L[ℂ]
        DerivativeSmoothVectors (matrixModel ℝ (n + m + 1))
          (representation (n := n + m + 1) (d₂ ++ d₁)),
      ∀ φ, P φ = smoothSectionVector hm hn f g φ

theorem realParabolicSmoothSectionMap : RealParabolicSmoothSectionMapStatement := by
  intro m n d₁ d₂ hm hn f g
  exact ⟨smoothSectionMap hm hn f g, fun _ => rfl⟩

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
