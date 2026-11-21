import Langlands.Analysis.GaussianWeightedMoment
import Langlands.Global.RankinSelberg.RealGodementGaussianPolynomial
import Langlands.Global.RankinSelberg.RealGodementSchwartzMajorant

/-! # Gaussian moment detection for the real compact Godement pairings -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealGodementGaussianPolynomial (Coordinates gaussianPolynomial gaussianPolynomial_apply
  matrixEuclidean matrixEuclidean_norm_sq matrixGaussian halfGaussian halfGaussian_apply
  realLinearPolynomial eval_realLinearPolynomial)
open PartialJacquet (normExponent)
open GramFormula (realPositionExponent)
open Langlands.Analysis.GaussianWeightedMoment
  (integrable_mul_of_hasCompactSupport integral_eq_zero_of_gaussian_moments)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

variable {m : ℕ}

local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ
local notation "K" => unitaryCompact ℝ (m + 1)

/-- The Godement section written out as an integral over the lower group. -/
theorem sectionValue_eq_integral (μ : Measure G) (c : RealCharacterData) (f : G → ℂ)
    (Φ : X → ℂ) (g : H) :
    sectionValue μ c f Φ g = determinantWeight c ((m : ℂ) / 2) g *
      ∫ h, f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h * Φ (rowPoint h.val g) ∂μ :=
  rfl

/-- The rectangular argument `h · (last m rows of k)` of the compact Godement integrand. -/
def compactSample (x : K × G) : X := rowPoint x.2.val x.1.val

theorem continuous_compactSample : Continuous (compactSample (m := m)) := by
  have hRows : Continuous (fun q : H => lastRows q.val) :=
    continuous_matrix fun i j => Units.continuous_val.matrix_elem i.succ j
  exact (Units.continuous_val.comp continuous_snd).matrix_mul
    ((hRows.comp continuous_subtype_val).comp continuous_fst)

private def outerWeight (c : RealCharacterData) (w : K → ℂ) (k : K) : ℂ :=
  w k * determinantWeight c ((m : ℂ) / 2) k.val

private def lowerWeight (c : RealCharacterData) (f : G → ℂ) (h : G) : ℂ :=
  f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h

private def jointWeight (c : RealCharacterData) (f : G → ℂ) (w : K → ℂ) (x : K × G) : ℂ :=
  outerWeight c w x.1 * lowerWeight c f x.2

private theorem continuous_outerWeight (c : RealCharacterData) {w : K → ℂ} (hw : Continuous w) :
    Continuous (outerWeight c w) :=
  hw.mul ((contMDiff_determinantWeight c _).continuous.comp continuous_subtype_val)

private theorem continuous_lowerWeight (c : RealCharacterData) {f : G → ℂ} (hf : Continuous f) :
    Continuous (lowerWeight c f) :=
  (hf.comp continuous_inv).mul (contMDiff_determinantWeight c _).continuous

private theorem continuous_jointWeight (c : RealCharacterData) {f : G → ℂ} (hf : Continuous f)
    {w : K → ℂ} (hw : Continuous w) : Continuous (jointWeight c f w) :=
  ((continuous_outerWeight c hw).comp continuous_fst).mul
    ((continuous_lowerWeight c hf).comp continuous_snd)

private theorem compact_pairing_product [MeasurableSpace K] (μ : Measure G) [SFinite μ]
    (κ : Measure K) [SFinite κ]
    (c : RealCharacterData) (f : G → ℂ) (w : K → ℂ) (Φ : X → ℂ)
    (h : Integrable (fun x => Φ (compactSample x) * jointWeight c f w x) (κ.prod μ)) :
    Integrable (fun k => w k * sectionValue μ c f Φ k.val) κ ∧
    (∫ k, w k * sectionValue μ c f Φ k.val ∂κ) =
      ∫ x, Φ (compactSample x) * jointWeight c f w x ∂κ.prod μ := by
  have hp (k : K) :
      (∫ y, Φ (compactSample (k, y)) * jointWeight c f w (k, y) ∂μ) =
        w k * sectionValue μ c f Φ k.val := by
    have hk (y : G) : Φ (compactSample (k, y)) * jointWeight c f w (k, y) =
        outerWeight c w k * (f y⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) y *
          Φ (rowPoint y.val k.val)) := by
      simp only [compactSample, jointWeight, lowerWeight]
      ring
    simp only [hk, integral_const_mul, outerWeight, sectionValue_eq_integral, mul_assoc]
  refine ⟨h.integral_prod_left.congr (ae_of_all _ hp), ?_⟩
  rw [integral_prod _ h]
  simp only [hp]

private theorem integrable_schwartz_joint [MeasurableSpace K] [BorelSpace K]
    (μ : Measure G) [μ.IsHaarMeasure] (c : RealCharacterData)
    (ds : List RealBlock) {f : G → ℂ} (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (hc : ∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2)
    (κ : Measure K) [IsFiniteMeasure κ] {w : K → ℂ} (hw : Continuous w) (Φ : 𝓢(X, ℂ)) :
    Integrable (fun x => Φ (compactSample x) * jointWeight c f w x) (κ.prod μ) := by
  let T : Set H := Set.range (fun k : K => k.val)
  have hT : IsCompact T := isCompact_range continuous_subtype_val
  obtain ⟨b, hb, hBound⟩ := realGodementSchwartzMajorant m μ c ds f hf hc Φ T hT
  have hO : Integrable (outerWeight c w) κ :=
    (continuous_outerWeight c hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hMaj := hO.norm.mul_prod hb
  have hC : Continuous (fun x => Φ (compactSample x) * jointWeight c f w x) :=
    (Φ.continuous.comp continuous_compactSample).mul
      (continuous_jointWeight c hf.1.continuous hw)
  refine hMaj.mono' hC.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hx := hBound x.1.val ⟨x.1, rfl⟩ x.2
  calc ‖Φ (compactSample x) * jointWeight c f w x‖
      = ‖outerWeight c w x.1‖ *
          (‖f x.2⁻¹‖ * ‖determinantWeight c (((m : ℂ) + 1) / 2) x.2‖ *
            ‖Φ (rowPoint x.2.val x.1.val)‖) := by
        simp only [compactSample, jointWeight, lowerWeight, norm_mul]
        ring
    _ ≤ ‖outerWeight c w x.1‖ * b x.2 :=
        mul_le_mul_of_nonneg_left hx (norm_nonneg _)

/-- In the real Godement convergence half-plane, every Schwartz section pairs integrably with
continuous compact weights. A continuous weight annihilating the polynomial Gaussian sections
annihilates the section of every bounded measurable compactly supported test. -/
def RealGodementGaussianPairingStatement : Prop :=
  ∀ (m : ℕ) (μ : Measure (Langlands.GeneralLinear m ℝ)) [μ.IsHaarMeasure]
    (c : RealCharacterData) (ds : List RealBlock) (f : Langlands.GeneralLinear m ℝ → ℂ),
    f ∈ principalSeries ℝ m (realPositionCharacter ds) →
    (∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2) →
    ∀ [MeasurableSpace (unitaryCompact ℝ (m + 1))] [BorelSpace (unitaryCompact ℝ (m + 1))]
      (κ : Measure (unitaryCompact ℝ (m + 1))) [IsFiniteMeasure κ]
      (w : unitaryCompact ℝ (m + 1) → ℂ), Continuous w →
      (∀ Φ : 𝓢(Matrix (Fin m) (Fin (m + 1)) ℝ, ℂ),
        Integrable (fun k => w k * sectionValue μ c f Φ k.val) κ) ∧
      ((∀ P : MvPolynomial (Coordinates m (m + 1)) ℂ,
          (∫ k, w k * sectionValue μ c f (gaussianPolynomial P) k.val ∂κ) = 0) →
        ∀ Φ : Matrix (Fin m) (Fin (m + 1)) ℝ → ℂ, Measurable Φ → HasCompactSupport Φ →
          (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) →
          (∫ k, w k * sectionValue μ c f Φ k.val ∂κ) = 0)

private theorem pairing_aux (μ : Measure G) [μ.IsHaarMeasure] (c : RealCharacterData)
    (ds : List RealBlock) {f : G → ℂ} (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (hc : ∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2)
    [MeasurableSpace K] [BorelSpace K] (κ : Measure K) [IsFiniteMeasure κ] {w : K → ℂ}
    (hw : Continuous w) :
    (∀ Φ : 𝓢(X, ℂ), Integrable (fun k => w k * sectionValue μ c f Φ k.val) κ) ∧
      ((∀ P : MvPolynomial (Coordinates m (m + 1)) ℂ,
          (∫ k, w k * sectionValue μ c f (gaussianPolynomial P) k.val ∂κ) = 0) →
        ∀ Φ : X → ℂ, Measurable Φ → HasCompactSupport Φ → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) →
          (∫ k, w k * sectionValue μ c f Φ k.val ∂κ) = 0) := by
  let W := jointWeight c f w
  let p : K × G → EuclideanSpace ℝ (Fin m × Fin (m + 1)) :=
    matrixEuclidean m (m + 1) ∘ compactSample
  have hW : Measurable W := (continuous_jointWeight c hf.1.continuous hw).measurable
  have hp : Measurable p :=
    ((matrixEuclidean m (m + 1)).continuous.comp continuous_compactSample).measurable
  have hS (Φ : 𝓢(X, ℂ)) := integrable_schwartz_joint μ c ds hf hc κ hw Φ
  have hhalfE : Integrable (fun x => (Real.exp (-‖p x‖ ^ 2 / 2) : ℂ) * W x) (κ.prod μ) := by
    refine (hS (halfGaussian m (m + 1))).congr (ae_of_all _ fun x => ?_)
    simp only [W, p, Function.comp_apply, matrixEuclidean_norm_sq, halfGaussian_apply]
  refine ⟨fun Φ => (compact_pairing_product μ κ c f w _ (hS Φ)).1, fun hzero Φ hΦm hΦc hΦb => ?_⟩
  let e := matrixEuclidean m (m + 1)
  let F : EuclideanSpace ℝ (Fin m × Fin (m + 1)) → ℂ := Φ ∘ e.symm
  have hF : Measurable F := hΦm.comp e.symm.continuous.measurable
  obtain ⟨C, hC⟩ := hΦb
  have hFi := integrable_mul_of_hasCompactSupport hp hW hhalfE hF
    (hΦc.comp_homeomorph e.symm.toHomeomorph) ⟨C, fun y => hC (e.symm y)⟩
  have hΦi : Integrable (fun x => Φ (compactSample x) * W x) (κ.prod μ) := by
    simpa only [F, p, e, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hFi
  rw [(compact_pairing_product μ κ c f w Φ hΦi).2]
  have hmot (L : EuclideanSpace ℝ (Fin m × Fin (m + 1)) →L[ℝ] ℝ) (j : ℕ) :
      (∫ x, (L (p x) : ℂ) ^ j * ((Real.exp (-‖p x‖ ^ 2) : ℂ) * W x) ∂κ.prod μ) = 0 := by
    let P := (realLinearPolynomial (L.toLinearMap.comp e.toLinearEquiv.toLinearMap)) ^ j
    have heq (x : K × G) :
        (L (p x) : ℂ) ^ j * ((Real.exp (-‖p x‖ ^ 2) : ℂ) * W x) =
          gaussianPolynomial P (compactSample x) * W x := by
      simp only [P, gaussianPolynomial_apply, map_pow, eval_realLinearPolynomial,
        LinearMap.comp_apply, ContinuousLinearEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
        ContinuousLinearMap.coe_coe, matrixGaussian, p, e, Function.comp_apply,
        matrixEuclidean_norm_sq, mul_assoc]
    simp_rw [heq]
    exact (compact_pairing_product μ κ c f w _ (hS (gaussianPolynomial P))).2.symm.trans
      (hzero P)
  simpa only [F, p, e, W, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using
    integral_eq_zero_of_gaussian_moments hp hW hhalfE hmot hF hFi

theorem realGodementGaussianPairing : RealGodementGaussianPairingStatement :=
  fun _ μ _ c ds _ hf hc _ _ κ _ _ hw => pairing_aux μ c ds hf hc κ hw

end Langlands.Global.RankinSelbergGlobal.RealGodement
