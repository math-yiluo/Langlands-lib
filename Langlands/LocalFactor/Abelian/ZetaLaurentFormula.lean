import Langlands.LocalFactor.Abelian.ZetaFiniteFormula
import Langlands.LocalFactor.Abelian.TateLatticeZeta

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)
local notation "TestFunction" => @HarmonicAnalysis.SchwartzBruhat F.Carrier T.topology

/-- Every test-function integral has a finite Laurent numerator in its convergence region. -/
theorem exists_laurent_formula (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (χ : Character) (a : ℕ) (hχ : ConductorAt T χ a) (μ : LocalHaar)
    (f : TestFunction) :
    letI := T.topology
    letI := borel F.Carrier
    ∃ A : ℤ →₀ ℂ, ∀ s, ConvergesAt T π χ s →
      zeta T μ.measure f χ s = lFactorAt T π χ a s * laurentEvaluation T A s := by
  classical
  let := T.topology
  let := borel F.Carrier
  obtain ⟨L, N, C, hLN, _, _, hL, hN⟩ :=
    HarmonicAnalysis.schwartzBruhatValuationBounds p F T f
  let P : ℤ →₀ ℂ := ∑ i ∈ Finset.range ((N : ℤ) - L).toNat,
    Finsupp.single (L + i) ((χ π : ℂ) ^ (L + i) *
      shellCoefficient T π χ μ f (L + i))
  let J := ∫ x in integralUnits T, characterExtension T χ x ∂μ.measure
  have hP (s : ℂ) : laurentEvaluation T P s =
      ∑ i ∈ Finset.range ((N : ℤ) - L).toNat,
        ((χ π : ℂ) * spectralVariable T s) ^ (L + i) *
          shellCoefficient T π χ μ f (L + i) := by
    dsimp only [P]
    rw [laurentEvaluation_finset_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [laurentEvaluation_single, mul_zpow]
    ring
  have hform (s : ℂ) (hs : ConvergesAt T π χ s) :
      zeta T μ.measure f χ s = laurentEvaluation T P s +
        ((χ π : ℂ) * spectralVariable T s) ^ (N : ℤ) * (f 0 * J) *
          (1 - (χ π : ℂ) * spectralVariable T s)⁻¹ := by
    rw [hP]
    exact zeta_eq_prefix_add_tail T π hπ χ μ f L N hLN hL hN s hs
  by_cases ha : a = 0
  · obtain ⟨B, hB⟩ := exists_laurent_eulerClear T P (χ π : ℂ)
    refine ⟨B + Finsupp.single (N : ℤ) ((χ π : ℂ) ^ (N : ℤ) * (f 0 * J)), ?_⟩
    intro s hs
    have hd : 1 - (χ π : ℂ) * spectralVariable T s ≠ 0 := by
      simpa only [RegularPoint, ne_eq, not_true_eq_false, false_or] using
        regularPoint_of_convergesAt T π χ 0 s hs
    rw [hform s hs, lFactorAt, ite_eq_left ha, laurentEvaluation_add,
      hB s, laurentEvaluation_single, mul_zpow]
    field_simp [hd]
  · refine ⟨P, ?_⟩
    intro s hs
    have hJ : J = 0 := by
      simpa only [J, ite_eq_right ha] using setIntegral_integralUnits_characterExtension T μ χ hχ
    rw [hform s hs, hJ, mul_zero, mul_zero, zero_mul, add_zero, lFactorAt, ite_eq_right ha,
      one_mul]

/-- The analytic and finite-expansion clauses for the actual local zeta integral. -/
theorem zeta_analysis (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (χ : Character) (a : ℕ) (hχ : ConductorAt T χ a) (μ : LocalHaar)
    (f : TestFunction) :
    letI := T.topology
    letI := borel F.Carrier
    (∀ s, ConvergesAt T π χ s → Integrable (zetaIntegrand T f χ s) μ.measure) ∧
    DifferentiableOn ℂ (zeta T μ.measure f χ) {s | ConvergesAt T π χ s} ∧
    (∃! Z : ℂ → ℂ, ExtendsIntegral T π μ.measure f χ Z) ∧
    (∀ Z : ℂ → ℂ, ExtendsIntegral T π μ.measure f χ Z →
      ∃! A : ℤ →₀ ℂ,
        (∀ s₀ : ℂ, Z =ᶠ[𝓝[≠] s₀]
          (fun s => lFactorAt T π χ a s * laurentEvaluation T A s)) ∧
        (∀ s, RegularPoint T π χ a s →
          Z s = lFactorAt T π χ a s * laurentEvaluation T A s)) := by
  let := T.topology
  let := borel F.Carrier
  obtain ⟨A, hA⟩ := exists_laurent_formula T π hπ χ a hχ μ f
  exact ⟨zeta_integrable T π hπ χ μ f,
    zeta_differentiableOn_of_laurent_formula T π χ a μ.measure f A hA,
    existsUnique_extendsIntegral_of_laurent_formula T π χ a μ.measure f A hA,
    existsUnique_laurent_of_laurent_formula T π χ a μ.measure f A hA⟩

end Langlands.LocalFactor.PadicAbelian
