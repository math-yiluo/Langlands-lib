import Langlands.Representation.RankinSelberg.InducedTailIntermediateComparison
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof

/-! # Integral, continuation and span assembly for the intermediate tail -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear MeasureTheory Whittaker HarmonicAnalysis
open scoped ENNReal

universe uF uP uQ uX uH uV uW

section ChangeOfVariables

variable {P : Type uP} {Q : Type uQ} {X : Type uX} {H : Type uH}
variable [MeasurableSpace P] [MeasurableSpace Q] [MeasurableSpace X] [MeasurableSpace H]

/-- A positive scalar multiple of a pushforward along a measurable embedding
transports integrability and the actual Bochner integral. -/
theorem changeOfVariables_of_measure_eq {μP : Measure P} {m : Measure (Q × (X × H))}
    {chart : Q × (X × H) → P} (hchart : MeasurableEmbedding chart) {C : ℝ} (hC : 0 < C)
    (hμ : μP = ENNReal.ofReal C • Measure.map chart m) (f : P → ℂ) :
    (Integrable f μP ↔ Integrable (f ∘ chart) m) ∧
      ∫ y, f y ∂μP = (C : ℂ) * ∫ z, f (chart z) ∂m := by
  subst hμ
  refine ⟨?_, ?_⟩
  · rw [integrable_smul_measure (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top,
      hchart.integrable_map_iff]
  · rw [integral_smul_measure, hchart.integral_map, ENNReal.toReal_ofReal hC.le,
      Complex.real_smul]

/-- The same transport when the chart is only almost-everywhere measurable and
the transported function is almost-everywhere strongly measurable. -/
theorem changeOfVariables_of_measure_eq_of_aemeasurable {μP : Measure P}
    {m : Measure (Q × (X × H))} {chart : Q × (X × H) → P} (hchart : AEMeasurable chart m)
    {C : ℝ} (hC : 0 < C) (hμ : μP = ENNReal.ofReal C • Measure.map chart m)
    {f : P → ℂ} (hf : AEStronglyMeasurable f (Measure.map chart m)) :
    (Integrable f μP ↔ Integrable (f ∘ chart) m) ∧
      ∫ y, f y ∂μP = (C : ℂ) * ∫ z, f (chart z) ∂m := by
  subst hμ
  refine ⟨?_, ?_⟩
  · rw [integrable_smul_measure (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top,
      integrable_map_measure hf hchart]
  · rw [integral_smul_measure, integral_map hchart hf, ENNReal.toReal_ofReal hC.le,
      Complex.real_smul]

variable {μP : Measure P} {μQ : Measure Q} {η : Measure X} {ρ : Measure H}
variable [SFinite μQ] [SFinite η] [SFinite ρ]

/-- **Localized disintegration comparison.** Suppose the full quotient
integral is transported, with an explicit real constant `C`, to the product of
the small quotient with density `D` and the two localization parameter spaces.
If the transported full function times the real density is the tail function
times the two localization indicators, then integrability of the tail function
gives integrability of the full function, and the full integral is the tail
integral times `C` and both real localization volumes. -/
theorem integrable_and_integral_of_localized_disintegration
    (chart : Q × (X × H) → P) {D : Q → ℝ≥0∞} (hD : Measurable D) (hDtop : ∀ q, D q ≠ ∞)
    {C : ℝ} {f : P → ℂ} {g : Q → ℂ}
    (hcov : Integrable f μP ↔
      Integrable (f ∘ chart) ((μQ.withDensity D).prod (η.prod ρ)))
    (hint : Integrable f μP → ∫ y, f y ∂μP =
      (C : ℂ) * ∫ z, f (chart z) ∂(μQ.withDensity D).prod (η.prod ρ))
    {S : Set X} {U : Set H} (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hSfin : η S ≠ ∞) (hUfin : ρ U ≠ ∞)
    (hpt : ∀ q x h, f (chart (q, (x, h))) * ((D q).toReal : ℂ) =
      g q * (S.indicator (fun _ => (1 : ℂ)) x * U.indicator (fun _ => (1 : ℂ)) h))
    (hg : Integrable g μQ) :
    Integrable f μP ∧
      ∫ y, f y ∂μP = ((C * (η.real S * ρ.real U) : ℝ) : ℂ) * ∫ q, g q ∂μQ := by
  have hD1 : Measurable fun z : Q × (X × H) => D z.1 := hD.comp measurable_fst
  have hDlt : ∀ᵐ z ∂μQ.prod (η.prod ρ), D z.1 < ∞ :=
    Filter.Eventually.of_forall fun z => lt_top_iff_ne_top.mpr (hDtop z.1)
  have hfun : (fun z : Q × (X × H) => (D z.1).toReal • (f ∘ chart) z) =
      fun z => g z.1 * (S.indicator (fun _ => (1 : ℂ)) z.2.1 *
        U.indicator (fun _ => (1 : ℂ)) z.2.2) := by
    funext z
    obtain ⟨q, x, h⟩ := z
    rw [Function.comp_apply, Complex.real_smul, mul_comm]
    exact hpt q x h
  have hm : (μQ.withDensity D).prod (η.prod ρ) =
      (μQ.prod (η.prod ρ)).withDensity fun z => D z.1 :=
    prod_withDensity_left hD
  have hfi : Integrable f μP := by
    refine hcov.mpr ?_
    rw [hm, integrable_withDensity_iff_integrable_smul' hD1 hDlt, hfun]
    exact integrable_localized_product hg hS hU hSfin hUfin
  refine ⟨hfi, ?_⟩
  rw [hint hfi, hm, integral_withDensity_eq_integral_toReal_smul hD1 hDlt]
  change (C : ℂ) * ∫ z, (D z.1).toReal • (f ∘ chart) z ∂μQ.prod (η.prod ρ) = _
  rw [hfun, integral_localized_product g hS hU]
  push_cast
  ring

end ChangeOfVariables

section Density

/-- The real value of an extended-real integer power of a positive real number. -/
theorem toReal_ofReal_zpow {r : ℝ} (hr : 0 < r) (z : ℤ) :
    (ENNReal.ofReal r ^ z).toReal = r ^ z := by
  have hr' : r.toNNReal ≠ 0 := by
    simpa only [ne_eq, Real.toNNReal_eq_zero, not_le] using hr
  rw [ENNReal.ofReal, ← ENNReal.coe_zpow hr', ENNReal.coe_toReal, NNReal.coe_zpow,
    Real.coe_toNNReal r hr.le]

/-- An integer power of a positive real number is a finite extended real. -/
theorem ofReal_zpow_ne_top {r : ℝ} (hr : 0 < r) (z : ℤ) : ENNReal.ofReal r ^ z ≠ ∞ :=
  ENNReal.zpow_ne_top (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top z

end Density

section ZeroRows

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
variable [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F)]

/-- Forgetting the zero-row matrix variable is a measurable equivalence. -/
def zeroRowsMeasurableEquiv (Q : Type uQ) [MeasurableSpace Q] :
    Q × Matrix (Fin 0) (Fin (n + 1)) F ≃ᵐ Q where
  toFun := Prod.fst
  invFun q := (q, 0)
  left_inv z := by
    obtain ⟨q, x⟩ := z
    simp only [Prod.mk.injEq, true_and]
    exact Subsingleton.elim _ _
  right_inv _ := rfl
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_id.prodMk measurable_const

/-- With zero rectangular rows and the unit point mass, absolute convergence is
integrability of the quotient integrand at the unique zero matrix. -/
theorem unequalRankConverges_zero_rows_iff (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (k : ℕ) (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ (n + (0 + k + 1))) (W' : InverseWhittakerFunctions ψ n)
    (s : ℂ) :
    UnequalRankConverges ψ abv 0 k μ (Measure.dirac 0) W W' s ↔
      Integrable (unequalRankIntegrand ψ abv 0 k W W' s 0) μ := by
  let e := zeroRowsMeasurableEquiv (F := F) (n := n) (LeftUnipotentQuotient n F)
  have hmap : Measure.map e (μ.prod (Measure.dirac 0)) = μ := by
    change Measure.map Prod.fst (μ.prod (Measure.dirac 0)) = μ
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hfun : (fun qx : LeftUnipotentQuotient n F × Matrix (Fin 0) (Fin (n + 1)) F =>
      unequalRankIntegrand ψ abv 0 k W W' s qx.2 qx.1) =
      unequalRankIntegrand ψ abv 0 k W W' s 0 ∘ e := by
    funext qx
    change unequalRankIntegrand ψ abv 0 k W W' s qx.2 qx.1 =
      unequalRankIntegrand ψ abv 0 k W W' s 0 qx.1
    rw [Subsingleton.elim qx.2 0]
  unfold UnequalRankConverges
  rw [hfun, ← integrable_map_equiv e, hmap]

/-- With zero rectangular rows and the unit point mass, the iterated integral
is the quotient integral at the unique zero matrix. -/
theorem unequalRankIntegral_zero_rows (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (k : ℕ) (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ (n + (0 + k + 1))) (W' : InverseWhittakerFunctions ψ n)
    (s : ℂ) :
    unequalRankIntegral ψ abv 0 k μ (Measure.dirac 0) W W' s =
      ∫ q, unequalRankIntegrand ψ abv 0 k W W' s 0 q ∂μ := by
  unfold unequalRankIntegral
  congr 1
  funext q
  exact integral_dirac' (fun x => unequalRankIntegrand ψ abv 0 k W W' s x q) 0
    StronglyMeasurable.of_subsingleton_dom

end ZeroRows

section Span

open RationalContinuationLinear

/-- A nonzero constant multiple of a rational function in a value set puts the
rational function itself in the Laurent span. -/
theorem mem_zetaSpan_of_const_mul_mem {values : Set RationalFunctions} {c : ℂ}
    (hc : c ≠ 0) {R : RationalFunctions} (h : RatFunc.C c * R ∈ values) :
    R ∈ zetaSpan values := by
  have hmem := Submodule.smul_mem (zetaSpan values) (LaurentPolynomial.C c⁻¹)
    (mem_zetaSpan h)
  rwa [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_C, ← mul_assoc,
    ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at hmem

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
variable {n : ℕ} (j k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
variable [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
variable (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))

/-- If actual full coefficients converge on a right half-plane and their
integral is `c` times a function with rational continuation `R` there, then
`C c * R` is an actual full zeta value. -/
theorem const_mul_mem_unequalRankZetaValues_of_eq
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {Wf : WhittakerFunctions ψ (n + (j + k + 1))} (hWf : Wf ∈ whittakerSet ψ _ π)
    {Wf' : InverseWhittakerFunctions ψ n} (hWf' : Wf' ∈ inverseWhittakerSet ψ n σ)
    {f : ℂ → ℂ} {R : RationalFunctions} (hR : HasRationalContinuation q f R) (c : ℂ)
    (a : ℝ) (hconv : ∀ s : ℂ, a < s.re → UnequalRankConverges ψ abv j k μ ν Wf Wf' s)
    (heq : ∀ s : ℂ, a < s.re → unequalRankIntegral ψ abv j k μ ν Wf Wf' s = c * f s) :
    RatFunc.C c * R ∈ unequalRankZetaValues q ψ abv j k μ ν π σ :=
  ⟨Wf, hWf, Wf', hWf', ⟨a, hconv⟩,
    continuation_of_eq_on_right (hasRationalContinuation_const_mul c hR) ⟨a, heq⟩⟩

/-- The span form of `const_mul_mem_unequalRankZetaValues_of_eq` for a nonzero
constant. -/
theorem mem_zetaSpan_unequalRankZetaValues_of_eq
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {Wf : WhittakerFunctions ψ (n + (j + k + 1))} (hWf : Wf ∈ whittakerSet ψ _ π)
    {Wf' : InverseWhittakerFunctions ψ n} (hWf' : Wf' ∈ inverseWhittakerSet ψ n σ)
    {f : ℂ → ℂ} {R : RationalFunctions} (hR : HasRationalContinuation q f R) {c : ℂ}
    (hc : c ≠ 0) (a : ℝ)
    (hconv : ∀ s : ℂ, a < s.re → UnequalRankConverges ψ abv j k μ ν Wf Wf' s)
    (heq : ∀ s : ℂ, a < s.re → unequalRankIntegral ψ abv j k μ ν Wf Wf' s = c * f s) :
    R ∈ zetaSpan (unequalRankZetaValues q ψ abv j k μ ν π σ) :=
  mem_zetaSpan_of_const_mul_mem hc
    (const_mul_mem_unequalRankZetaValues_of_eq q ψ abv j k μ ν hWf hWf' hR c a hconv heq)

end Span

section Assembly

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {Q : Type uQ} {X : Type uX} {H : Type uH}
variable [MeasurableSpace Q] [MeasurableSpace X] [MeasurableSpace H]

/-- **Zero-row full value from a localized disintegration.** For every `s` in
a right half-plane, the actual zero-row full integrand is transported by the
explicit change of variables, and times the density it equals the tail function
times two localization indicators. If the tail functions are integrable there
and their integrals have rational continuation `R`, then `R` lies in the
Laurent span of the actual zero-row full zeta values. The positive constant
`C` and both localization volumes are kept explicit and removed only at the
span level. -/
theorem mem_zetaSpan_of_localized_disintegration
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    {π : Representation ℂ (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {Wf : WhittakerFunctions ψ (n + (0 + k + 1))} (hWf : Wf ∈ whittakerSet ψ _ π)
    {Wf' : InverseWhittakerFunctions ψ n} (hWf' : Wf' ∈ inverseWhittakerSet ψ n σ)
    (μQ : Measure Q) [SFinite μQ] (η : Measure X) [SFinite η] (ρ : Measure H) [SFinite ρ]
    (chart : Q × (X × H) → LeftUnipotentQuotient n F)
    {D : Q → ℝ≥0∞} (hD : Measurable D) (hDtop : ∀ x, D x ≠ ∞) {C : ℝ} (hC : 0 < C)
    {S : Set X} {U : Set H} (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hSpos : 0 < η.real S) (hUpos : 0 < ρ.real U)
    (g : ℂ → Q → ℂ) {R : RationalFunctions} (a : ℝ)
    (hcov : ∀ s : ℂ, a < s.re →
      (Integrable (unequalRankIntegrand ψ abv 0 k Wf Wf' s 0) μ ↔
        Integrable (unequalRankIntegrand ψ abv 0 k Wf Wf' s 0 ∘ chart)
          ((μQ.withDensity D).prod (η.prod ρ))) ∧
      (Integrable (unequalRankIntegrand ψ abv 0 k Wf Wf' s 0) μ →
        ∫ y, unequalRankIntegrand ψ abv 0 k Wf Wf' s 0 y ∂μ =
          (C : ℂ) * ∫ z, unequalRankIntegrand ψ abv 0 k Wf Wf' s 0 (chart z)
            ∂(μQ.withDensity D).prod (η.prod ρ)))
    (hpt : ∀ s : ℂ, a < s.re → ∀ x y h,
      unequalRankIntegrand ψ abv 0 k Wf Wf' s 0 (chart (x, (y, h))) * ((D x).toReal : ℂ) =
        g s x * (S.indicator (fun _ => (1 : ℂ)) y * U.indicator (fun _ => (1 : ℂ)) h))
    (hg : ∀ s : ℂ, a < s.re → Integrable (g s) μQ)
    (hR : HasRationalContinuation q (fun s => ∫ x, g s x ∂μQ) R) :
    R ∈ zetaSpan (unequalRankZetaValues q ψ abv 0 k μ (Measure.dirac 0) π σ) := by
  have hSfin : η S ≠ ∞ := by
    intro h0
    simp [Measure.real, h0] at hSpos
  have hUfin : ρ U ≠ ∞ := by
    intro h0
    simp [Measure.real, h0] at hUpos
  have hc : (((C * (η.real S * ρ.real U)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos hC (mul_pos hSpos hUpos)).ne'
  have key : ∀ s : ℂ, a < s.re →
      Integrable (unequalRankIntegrand ψ abv 0 k Wf Wf' s 0) μ ∧
        ∫ y, unequalRankIntegrand ψ abv 0 k Wf Wf' s 0 y ∂μ =
          ((C * (η.real S * ρ.real U) : ℝ) : ℂ) * ∫ x, g s x ∂μQ := fun s hs =>
    integrable_and_integral_of_localized_disintegration chart hD hDtop (hcov s hs).1
      (hcov s hs).2 hS hU hSfin hUfin (hpt s hs) (hg s hs)
  refine mem_zetaSpan_unequalRankZetaValues_of_eq q ψ abv 0 k μ (Measure.dirac 0)
    hWf hWf' hR hc a (fun s hs => ?_) (fun s hs => ?_)
  · exact (unequalRankConverges_zero_rows_iff ψ abv k μ Wf Wf' s).mpr (key s hs).1
  · rw [unequalRankIntegral_zero_rows]
    exact (key s hs).2

end Assembly

end Langlands.RankinSelberg.InducedTailIntermediate
