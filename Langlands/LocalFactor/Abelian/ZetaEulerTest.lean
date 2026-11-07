import Langlands.LocalFactor.Abelian.ZetaLaurentFormula

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)
local notation "TestFunction" => @HarmonicAnalysis.SchwartzBruhat F.Carrier T.topology

/-- The explicit unramified or ramified test has exactly the Euler integral. -/
theorem test_function_euler (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (χ : Character) (a : ℕ) (hχ : ConductorAt T χ a) (μ : LocalHaar) :
    letI := T.topology
    letI := borel F.Carrier
    let test : F.Carrier → ℂ :=
      if a = 0 then (integerRing T).indicator (fun _ => (1 : ℂ)) else
        (integralUnits T).indicator (fun x => (characterExtension T χ x)⁻¹)
    (∃ f : TestFunction, ∀ x, f x = test x) ∧
      ∀ s, ConvergesAt T π χ s →
        zeta T μ.measure test χ s =
          (μ.measure (integralUnits T)).toReal * lFactorAt T π χ a s := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  dsimp only
  by_cases ha : a = 0
  · simp only [ite_eq_left ha]
    refine ⟨?_, ?_⟩
    · refine ⟨cosetTest T 0 0, ?_⟩
      intro x
      rw [cosetTest_coe, coset_zero, integerRing_eq_lattice_zero]
    · intro s hs
      rw [integerRing_eq_lattice_zero,
        zeta_additiveLattice T π hπ χ μ hs 0,
        setIntegral_integralUnits_characterExtension T μ χ hχ]
      simp only [ha, ite_true, neg_zero, zpow_zero, mul_one, lFactorAt]
      ring
  · simp only [ite_eq_right ha]
    refine ⟨⟨⟨_, ramifiedTest_isLocallyConstant T χ hχ ha,
      ramifiedTest_hasCompactSupport T χ⟩, fun _ => rfl⟩, ?_⟩
    intro s _
    have he : zetaIntegrand T
        ((integralUnits T).indicator (fun x => (characterExtension T χ x)⁻¹)) χ s =
        (integralUnits T).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ integralUnits T
      · have hne : characterExtension T χ x ≠ 0 := by
          rw [show x = ((Units.mk0 x hx.1 : F.Carrierˣ) : F.Carrier) from rfl,
            characterExtension_unit]
          exact (χ (Units.mk0 x hx.1)).ne_zero
        rw [zetaIntegrand, ite_eq_right hx.1, Set.indicator_of_mem hx,
          Set.indicator_of_mem hx, log_normalizedAbs_orderShell T 0 hx]
        simp [hne]
      · by_cases h0 : x = 0
        · simp [zetaIntegrand, h0, integralUnits]
        · simp [zetaIntegrand, h0, Set.indicator_of_notMem hx]
    have hU : MeasurableSet (integralUnits T) := (orderShell_compact_measurable T 0).2
    rw [zeta, he, integral_indicator hU,
      setIntegral_const, measureReal_def, Complex.real_smul, mul_one, lFactorAt,
      ite_eq_right ha, mul_one]

end Langlands.LocalFactor.PadicAbelian
