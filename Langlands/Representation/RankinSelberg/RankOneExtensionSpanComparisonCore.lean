import Langlands.Representation.RankinSelberg.RankOneExtensionUnfoldingIntegral
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-!
# Measure-theoretic core of the rank-one extension comparison

JPSS (1983), Lemma 5.5, compares an integral over `N_(t+2) \ GL_(t+2)` with an integral over
`N_(t+1) \ GL_(t+1) × M_(1×(t+1))`. This module isolates the change of variables behind that
comparison. The representation theory enters only through abstract hypotheses on a continuous
function `H` on `GL_(1+(t+1))`:

* `H` is invariant under left translation by `B(n, 0, 1)` for `n ∈ N_(t+1)`;
* on the cells `B(g, x, h) u(y)`, `H` is a product `1_U(h) fB([g], x) φ(y)`;
* the integrand `fQ` on the larger quotient is the `y`-integral of `H(u(y) B(g, x, h))` at
  the chart point `([g], x, h)` whenever that integral converges.

Under a chart transfer from the disintegration of the quotient measure, `fQ` is integrable and
`∫ fQ = C ρ(U) (∫ φ) ∫ fB`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Matrix GeneralLinear QuotientIntegration HarmonicAnalysis
open scoped ENNReal NNReal

section Descent

variable {K : Type*} [Field K] {t : ℕ} {E : Type*}

theorem rankOneExtensionLowerBlock_mul_zero_one (m m' : Langlands.GeneralLinear (t + 1) K) :
    rankOneExtensionLowerBlock t (m * m') 0 1 =
      rankOneExtensionLowerBlock t m 0 1 * rankOneExtensionLowerBlock t m' 0 1 := by
  rw [rankOneExtensionLowerBlock_mul]
  simp

/-- `B(g, 0, 1) B(1, x, h) = B(g, x, h)`. -/
theorem rankOneExtensionLowerBlock_zero_one_mul_lowerCell (m : Langlands.GeneralLinear (t + 1) K)
    (x : Matrix (Fin 1) (Fin (t + 1)) K) (h : lowerTriangularSubgroup 1 K) :
    rankOneExtensionLowerBlock t m 0 1 * rankOneExtensionLowerCell x h =
      rankOneExtensionLowerBlock t m (x 0) (lowerScalarUnit h) := by
  rw [rankOneExtensionLowerCell, rankOneExtensionLowerBlock_mul]
  simp

/-- The function `([g], z) ↦ H(B(g, 0, 1) z)` on `N_(t+1) \ GL_(t+1) × GL_(1+(t+1))`, for `H`
invariant under left translation by `B(n, 0, 1)`, `n ∈ N_(t+1)`. -/
def rankOneExtensionCellDescent (H : Langlands.GeneralLinear (1 + (t + 1)) K → E)
    (hH : ∀ (n : upperUnipotent (t + 1) K) (z : Langlands.GeneralLinear (1 + (t + 1)) K),
      H (rankOneExtensionLowerBlock t n.val 0 1 * z) = H z) :
    LeftQuotient (upperUnipotent (t + 1) K) × Langlands.GeneralLinear (1 + (t + 1)) K → E :=
  fun p => descend (upperUnipotent (t + 1) K)
    (fun g => H (rankOneExtensionLowerBlock t g 0 1 * p.2))
    (fun n g => by
      change H (rankOneExtensionLowerBlock t (n.val * g) 0 1 * p.2) = _
      rw [rankOneExtensionLowerBlock_mul_zero_one, mul_assoc, hH]) p.1

@[simp] theorem rankOneExtensionCellDescent_mk (H : Langlands.GeneralLinear (1 + (t + 1)) K → E)
    (hH : ∀ (n : upperUnipotent (t + 1) K) (z : Langlands.GeneralLinear (1 + (t + 1)) K),
      H (rankOneExtensionLowerBlock t n.val 0 1 * z) = H z)
    (g : Langlands.GeneralLinear (t + 1) K) (z : Langlands.GeneralLinear (1 + (t + 1)) K) :
    rankOneExtensionCellDescent H hH (Quotient.mk _ g, z) =
      H (rankOneExtensionLowerBlock t g 0 1 * z) := rfl

end Descent

section Topology

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {t : ℕ} {E : Type*}

theorem rankOneExtensionCellDescent_lowerBlock (H : Langlands.GeneralLinear (1 + (t + 1)) K → E)
    (hH : ∀ (n : upperUnipotent (t + 1) K) (z : Langlands.GeneralLinear (1 + (t + 1)) K),
      H (rankOneExtensionLowerBlock t n.val 0 1 * z) = H z)
    (q : LeftQuotient (upperUnipotent (t + 1) K)) (r : Langlands.GeneralLinear (t + 1) K)
    (z : Langlands.GeneralLinear (1 + (t + 1)) K) :
    rankOneExtensionCellDescent H hH (q, rankOneExtensionLowerBlock t r 0 1 * z) =
      rankOneExtensionCellDescent H hH (rightTranslate _ r q, z) := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [rightTranslate_mk, rankOneExtensionCellDescent_mk, rankOneExtensionCellDescent_mk,
      rankOneExtensionLowerBlock_mul_zero_one, mul_assoc]

omit [IsTopologicalRing K] in
theorem continuous_rankOneExtensionLowerBlock_zero_one :
    Continuous fun g : Langlands.GeneralLinear (t + 1) K => rankOneExtensionLowerBlock t g 0 1 := by
  have hval : ∀ g : Langlands.GeneralLinear (t + 1) K, (rankOneExtensionLowerBlock t g 0 1).val =
      Matrix.reindex (rankOneExtensionCellCoordinates t) (rankOneExtensionCellCoordinates t)
        (Matrix.fromBlocks g.val 0 (Matrix.of fun (_ : Fin 1) => (0 : Fin (t + 1) → K))
          (Matrix.of fun (_ _ : Fin 1) => (1 : K))) := by
    intro g
    rw [rankOneExtensionCellBlocks_val, rankOneExtensionCellBlocks_lowerBlock, Units.val_one]
  have hblock : ∀ {m : Langlands.GeneralLinear (t + 1) K → Matrix (Fin (t + 1)) (Fin (t + 1)) K},
      Continuous m → Continuous fun g =>
        Matrix.reindex (rankOneExtensionCellCoordinates t) (rankOneExtensionCellCoordinates t)
          (Matrix.fromBlocks (m g) 0 (Matrix.of fun (_ : Fin 1) => (0 : Fin (t + 1) → K))
            (Matrix.of fun (_ _ : Fin 1) => (1 : K))) := by
    intro m hm
    exact (hm.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex
      _ _
  have hinv : ∀ g : Langlands.GeneralLinear (t + 1) K,
      (rankOneExtensionLowerBlock t g 0 1)⁻¹ = rankOneExtensionLowerBlock t g⁻¹ 0 1 := by
    intro g
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    rw [← rankOneExtensionLowerBlock_mul_zero_one, mul_inv_cancel,
      rankOneExtensionLowerBlock_one_zero_one]
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (hblock Units.continuous_val).congr fun g => (hval g).symm
  · refine (hblock Units.continuous_coe_inv).congr fun g => ?_
    rw [hinv, hval]

theorem continuous_rankOneExtensionCellDescent [TopologicalSpace E]
    (H : Langlands.GeneralLinear (1 + (t + 1)) K → E)
    (hH : ∀ (n : upperUnipotent (t + 1) K) (z : Langlands.GeneralLinear (1 + (t + 1)) K),
      H (rankOneExtensionLowerBlock t n.val 0 1 * z) = H z) (hHc : Continuous H) :
    Continuous (rankOneExtensionCellDescent H hH) := by
  have hq : IsOpenQuotientMap (Prod.map (leftQuotientMap (upperUnipotent (t + 1) K))
      (id : Langlands.GeneralLinear (1 + (t + 1)) K → Langlands.GeneralLinear (1 + (t + 1)) K)) :=
    (leftQuotient_isOpenQuotientMap _).prodMap IsOpenQuotientMap.id
  refine hq.continuous_comp_iff.mp ?_
  exact hHc.comp ((continuous_rankOneExtensionLowerBlock_zero_one.comp continuous_fst).mul
    continuous_snd)

end Topology

section Scaling

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] {t : ℕ}
  (ν : Measure K) [SigmaFinite ν] [ν.IsAddLeftInvariant]
  (χ : K →*₀ ℝ≥0) (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν)

include hχ in
/-- The change of variables `y ↦ g y` on `K^(t+1)`, for `g ∈ GL_(t+1)`. -/
theorem integral_generalLinear_mulVec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Langlands.GeneralLinear (t + 1) K) (f : (Fin (t + 1) → K) → E)
    (hf : StronglyMeasurable f) :
    (Integrable (fun y => f (g.val *ᵥ y)) (Measure.pi fun _ => ν) ↔
        Integrable f (Measure.pi fun _ => ν)) ∧
      ∫ y, f (g.val *ᵥ y) ∂(Measure.pi fun _ => ν) =
        (χ g.val.det)⁻¹ • ∫ y, f y ∂(Measure.pi fun _ => ν) := by
  have hdet : g.val.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hmap := productMeasure_map_matrix ν χ hχ hdet
  have hm : Measurable (Matrix.toLin' g.val) := (LinearMap.continuous_on_pi _).measurable
  have hχ0 : χ g.val.det ≠ 0 := (map_ne_zero χ).mpr hdet
  have hfun : (fun y => f (g.val *ᵥ y)) = f ∘ Matrix.toLin' g.val := by
    funext y
    simp only [Function.comp, Matrix.toLin'_apply]
  have hint := integrable_map_measure (μ := Measure.pi fun _ : Fin (t + 1) => ν)
    hf.aestronglyMeasurable hm.aemeasurable
  have hintegral := integral_map (μ := Measure.pi fun _ : Fin (t + 1) => ν) hm.aemeasurable
    hf.aestronglyMeasurable
  rw [hmap] at hint hintegral
  rw [hfun]
  refine ⟨?_, ?_⟩
  · rw [← hint]
    constructor
    · intro h
      have h2 := h.smul_measure_nnreal (c := χ g.val.det)
      rwa [smul_smul, mul_inv_cancel₀ hχ0, one_smul] at h2
    · intro h
      exact h.smul_measure_nnreal
  · rw [← integral_smul_nnreal_measure]
    exact hintegral.symm

end Scaling

section Core

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] {t : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (t + 1) K)]
  [BorelSpace (Langlands.GeneralLinear (t + 1) K)]
  [MeasurableSpace (Langlands.GeneralLinear (1 + (t + 1)) K)]
  [BorelSpace (Langlands.GeneralLinear (1 + (t + 1)) K)]
  [MeasurableSpace (LeftQuotient (upperUnipotent (t + 1) K))]
  [BorelSpace (LeftQuotient (upperUnipotent (t + 1) K))]
  [MeasurableSpace (lowerTriangularSubgroup 1 K)] [BorelSpace (lowerTriangularSubgroup 1 K)]

/-- The measure-theoretic core of JPSS (1983), Lemma 5.5. -/
theorem rankOneExtensionUnfoldingCore
    (μ : Measure (LeftQuotient (upperUnipotent (t + 1) K))) [SFinite μ]
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (t + 1) K) g) μ μ)
    (dx : Measure (Matrix (Fin 1) (Fin (t + 1)) K)) [SFinite dx]
    (ρ : Measure (lowerTriangularSubgroup 1 K)) [SFinite ρ] [ρ.IsMulRightInvariant]
    (ν : Measure K) [SigmaFinite ν] [NullSingletonClass ν] [ν.IsAddLeftInvariant]
    (χ : K →*₀ ℝ≥0) (hχm : Measurable χ)
    (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν)
    (D : LeftQuotient (upperUnipotent (t + 1) K) → ℝ≥0∞) (hDm : Measurable D)
    (hD : ∀ g : Langlands.GeneralLinear (t + 1) K,
      D (Quotient.mk _ g) = (((χ g.val.det)⁻¹ : ℝ≥0) : ℝ≥0∞))
    {Q₂ : Type*} [MeasurableSpace Q₂] (μ₂ : Measure Q₂)
    (chart : LeftQuotient (upperUnipotent (t + 1) K) ×
      (Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K) → Q₂)
    (C : ℂ) (fQ : Q₂ → ℂ)
    (htr : Integrable (fQ ∘ chart) ((μ.withDensity D).prod (dx.prod ρ)) →
      Integrable fQ μ₂ ∧
        ∫ q, fQ q ∂μ₂ = C * ∫ p, fQ (chart p) ∂((μ.withDensity D).prod (dx.prod ρ)))
    (H : Langlands.GeneralLinear (1 + (t + 1)) K → ℂ) (hHc : Continuous H)
    (hH : ∀ (n : upperUnipotent (t + 1) K) (z : Langlands.GeneralLinear (1 + (t + 1)) K),
      H (rankOneExtensionLowerBlock t n.val 0 1 * z) = H z)
    (hJ : ∀ (g : Langlands.GeneralLinear (t + 1) K) (x : Matrix (Fin 1) (Fin (t + 1)) K)
      (h : lowerTriangularSubgroup 1 K),
      Integrable (fun y => H (rankOneExtensionUpperCell t y *
        rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h))) (Measure.pi fun _ => ν) →
      fQ (chart (Quotient.mk _ g, (x, h))) =
        ∫ y, H (rankOneExtensionUpperCell t y *
          rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h)) ∂(Measure.pi fun _ => ν))
    (fB : LeftQuotient (upperUnipotent (t + 1) K) × Matrix (Fin 1) (Fin (t + 1)) K → ℂ)
    (hfB : Integrable fB (μ.prod dx))
    (φ : (Fin (t + 1) → K) → ℂ) (hφ : Integrable φ (Measure.pi fun _ => ν))
    (U : Set (lowerTriangularSubgroup 1 K)) (hUm : MeasurableSet U) (hUρ : ρ U ≠ ∞)
    (hχU : ∀ h ∈ U, χ (lowerScalarEntry h) = 1)
    (hWc : ∀ (g : Langlands.GeneralLinear (t + 1) K) (x : Matrix (Fin 1) (Fin (t + 1)) K)
      (h : lowerTriangularSubgroup 1 K) (y : Fin (t + 1) → K),
      H (rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h) *
          rankOneExtensionUpperCell t y) =
        U.indicator (fun _ => (1 : ℂ)) h * fB (Quotient.mk _ g, x) * φ y) :
    Integrable fQ μ₂ ∧
      ∫ q, fQ q ∂μ₂ = C * (ρ.real U : ℂ) * (∫ y, φ y ∂(Measure.pi fun _ => ν)) *
        ∫ z, fB z ∂(μ.prod dx) := by
  classical
  have := secondCountable_generalLinear (K := K) (1 + (t + 1))
  have hΨm : StronglyMeasurable (rankOneExtensionCellDescent H hH) :=
    (continuous_rankOneExtensionCellDescent H hH hHc).measurable.stronglyMeasurable
  obtain ⟨hint, hintegral⟩ := integral_cellExchange_reorder (upperUnipotent (t + 1) K) dx ν μ hμ
    ρ χ hχm hχ (rankOneExtensionCellDescent H hH) hΨm (rankOneExtensionCellDescent_lowerBlock H hH)
  -- The exchanged integrand is a product.
  have hR : (fun z : (LeftQuotient (upperUnipotent (t + 1) K) × (Matrix (Fin 1) (Fin (t + 1)) K ×
        lowerTriangularSubgroup 1 K)) × (Fin (t + 1) → K) =>
      (χ (lowerScalarEntry z.1.2.2))⁻¹ ^ (t + 1) •
        rankOneExtensionCellDescent H hH
          (z.1.1, rankOneExtensionLowerCell z.1.2.1 z.1.2.2 * rankOneExtensionUpperCell t z.2)) =
      fun z => (fB (z.1.1, z.1.2.1) * U.indicator (fun _ => (1 : ℂ)) z.1.2.2) * φ z.2 := by
    funext z
    obtain ⟨⟨q, x, h⟩, y⟩ := z
    induction q using Quotient.inductionOn with
    | h g =>
      change (χ (lowerScalarEntry h))⁻¹ ^ (t + 1) •
          H (rankOneExtensionLowerBlock t g 0 1 *
            (rankOneExtensionLowerCell x h * rankOneExtensionUpperCell t y)) = _
      rw [← mul_assoc, rankOneExtensionLowerBlock_zero_one_mul_lowerCell, hWc]
      by_cases hh : h ∈ U
      · rw [hχU h hh, inv_one, one_pow, one_smul]
        ring
      · simp [hh]
  have hind : Integrable (U.indicator fun _ => (1 : ℂ)) ρ :=
    (integrable_indicator_iff hUm).mpr (integrableOn_const hUρ)
  have hA := measurePreserving_prodAssoc μ dx ρ
  have hfirst : Integrable (fun w : LeftQuotient (upperUnipotent (t + 1) K) ×
      (Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K) =>
      fB (w.1, w.2.1) * U.indicator (fun _ => (1 : ℂ)) w.2.2) (μ.prod (dx.prod ρ)) := by
    rw [← hA.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding]
    exact hfB.mul_prod hind
  have hfirstval : ∫ w, fB (w.1, w.2.1) * U.indicator (fun _ => (1 : ℂ)) w.2.2
      ∂(μ.prod (dx.prod ρ)) = (∫ z, fB z ∂(μ.prod dx)) * (ρ.real U : ℂ) := by
    rw [← hA.integral_comp' (fun w : LeftQuotient (upperUnipotent (t + 1) K) ×
      (Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K) =>
      fB (w.1, w.2.1) * U.indicator (fun _ => (1 : ℂ)) w.2.2)]
    have h := integral_prod_mul (μ := μ.prod dx) (ν := ρ) fB (U.indicator fun _ => (1 : ℂ))
    rw [integral_indicator_const _ hUm] at h
    rw [Complex.real_smul, mul_one] at h
    exact h
  have hRint : Integrable (fun z : (LeftQuotient (upperUnipotent (t + 1) K) ×
      (Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K)) × (Fin (t + 1) → K) =>
      (fB (z.1.1, z.1.2.1) * U.indicator (fun _ => (1 : ℂ)) z.1.2.2) * φ z.2)
      ((μ.prod (dx.prod ρ)).prod (Measure.pi fun _ => ν)) :=
    hfirst.mul_prod hφ
  have hRval : ∫ z, (fB (z.1.1, z.1.2.1) * U.indicator (fun _ => (1 : ℂ)) z.1.2.2) * φ z.2
      ∂((μ.prod (dx.prod ρ)).prod (Measure.pi fun _ => ν)) =
      (∫ z, fB z ∂(μ.prod dx)) * (ρ.real U : ℂ) * ∫ y, φ y ∂(Measure.pi fun _ => ν) := by
    rw [← hfirstval]
    exact integral_prod_mul (μ := μ.prod (dx.prod ρ)) (ν := Measure.pi fun _ => ν)
      (fun w : LeftQuotient (upperUnipotent (t + 1) K) ×
        (Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K) =>
        fB (w.1, w.2.1) * U.indicator (fun _ => (1 : ℂ)) w.2.2) φ
  rw [hR] at hint hintegral
  have hLint := hint.mpr hRint
  -- Fubini in `y`.
  have hae := hLint.prod_right_ae
  have hFint := hLint.integral_prod_left
  have hFval := integral_prod _ hLint
  -- The inner integral is the density times the integrand at the chart point.
  have hpt : ∀ p : LeftQuotient (upperUnipotent (t + 1) K) ×
      (Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K),
      Integrable (fun y => rankOneExtensionCellDescent H hH
        (p.1, rankOneExtensionUpperCell t y * rankOneExtensionLowerCell p.2.1 p.2.2))
        (Measure.pi fun _ => ν) →
      (D p.1).toReal • fQ (chart p) = ∫ y, rankOneExtensionCellDescent H hH
        (p.1, rankOneExtensionUpperCell t y * rankOneExtensionLowerCell p.2.1 p.2.2)
        ∂(Measure.pi fun _ => ν) := by
    rintro ⟨q, x, h⟩ hp
    induction q using Quotient.inductionOn with
    | h g =>
      have hfun : (fun y => rankOneExtensionCellDescent H hH
          (Quotient.mk _ g, rankOneExtensionUpperCell t y * rankOneExtensionLowerCell x h)) =
          fun y => H (rankOneExtensionUpperCell t (g.val *ᵥ y) *
            rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h)) := by
        funext y
        rw [rankOneExtensionCellDescent_mk, ← mul_assoc, rankOneExtensionLowerBlock_upperCell,
          mul_assoc, rankOneExtensionLowerBlock_zero_one_mul_lowerCell]
      have hcont : Continuous fun y => H (rankOneExtensionUpperCell t y *
          rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h)) :=
        hHc.comp ((continuous_rankOneExtensionUpperCell t).mul continuous_const)
      obtain ⟨hiff, hval⟩ := integral_generalLinear_mulVec ν χ hχ g _
        hcont.measurable.stronglyMeasurable
      change Integrable (fun y => rankOneExtensionCellDescent H hH
        (Quotient.mk _ g, rankOneExtensionUpperCell t y * rankOneExtensionLowerCell x h))
        (Measure.pi fun _ => ν) at hp
      change (D (Quotient.mk _ g)).toReal • fQ (chart (Quotient.mk _ g, (x, h))) =
        ∫ y, rankOneExtensionCellDescent H hH
          (Quotient.mk _ g, rankOneExtensionUpperCell t y * rankOneExtensionLowerCell x h)
          ∂(Measure.pi fun _ => ν)
      rw [hfun] at hp ⊢
      rw [hval, hJ g x h (hiff.mp hp), hD, ENNReal.coe_toReal, NNReal.smul_def]
  have hEq : (fun p => (D p.1).toReal • fQ (chart p)) =ᵐ[μ.prod (dx.prod ρ)]
      fun p => ∫ y, rankOneExtensionCellDescent H hH
        (p.1, rankOneExtensionUpperCell t y * rankOneExtensionLowerCell p.2.1 p.2.2)
        ∂(Measure.pi fun _ => ν) := by
    filter_upwards [hae] with p hp
    exact hpt p hp
  -- The density on the first factor.
  have hDlt : ∀ q, D q < ∞ := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [hD]
      exact ENNReal.coe_lt_top
  have hDm' : Measurable fun p : LeftQuotient (upperUnipotent (t + 1) K) ×
      (Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K) => D p.1 :=
    hDm.comp measurable_fst
  have hP : (μ.withDensity D).prod (dx.prod ρ) =
      (μ.prod (dx.prod ρ)).withDensity fun p => D p.1 := prod_withDensity_left hDm
  have hint2 : Integrable (fQ ∘ chart) ((μ.withDensity D).prod (dx.prod ρ)) := by
    rw [hP, integrable_withDensity_iff_integrable_smul' hDm' (ae_of_all _ fun p => hDlt p.1)]
    exact (integrable_congr hEq).mpr hFint
  obtain ⟨hI, hV⟩ := htr hint2
  refine ⟨hI, ?_⟩
  rw [hV, hP, integral_withDensity_eq_integral_toReal_smul hDm' (ae_of_all _ fun p => hDlt p.1),
    integral_congr_ae hEq, ← hFval, hintegral, hRval]
  ring

end Core

end Langlands.RankinSelberg
