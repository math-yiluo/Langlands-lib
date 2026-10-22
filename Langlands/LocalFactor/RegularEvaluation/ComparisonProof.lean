import Langlands.LocalFactor.RegularEvaluation.ComparisonStatement

/-! Proof of the published comparison between the generic regular evaluation and the
specialized local-factor adapters. -/

namespace Langlands.LocalFactor.RegularEvaluation

universe uK uV uW uF

/-- The polynomial Euler adapter is the identity on carriers; both unit values invert
`Units.mk0` of the same Euler denominator with the same nonzero certificate. -/
theorem eulerComparison {K : Type uK} [Field K]
    {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : Module.End K V) : EulerComparison A := by
  refine ⟨fun z => ⟨?_, fun h => ⟨⟨z, h⟩, rfl⟩⟩, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  rintro ⟨x, rfl⟩
  exact x.2

/-- The spectral Euler adapter is the identity on carriers; spectral substitution is
`mapInput`, whose value is the composite value by `value_mapInput`. -/
theorem spectralEulerComparison {V : Type uW} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Module.End ℂ V) (q : ℝ) (hq : 0 < q) :
    SpectralEulerComparison A q hq := by
  refine ⟨fun s => ⟨?_, fun h => ⟨⟨s, h⟩, rfl⟩⟩, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun x => value_mapInput _ _ _, fun _ => rfl⟩
  rintro ⟨x, rfl⟩
  exact x.2

/-- `ReciprocalEntire.eval` is `Units.mk0` of the inverse denominator, while `value`
inverts the unit of the denominator; the two units have the same underlying scalar. -/
theorem reciprocalEntireComparison (F : ReciprocalEntire) :
    ReciprocalEntireComparison F := by
  refine ⟨fun z => ⟨?_, fun h => ⟨⟨z, h⟩, rfl⟩⟩, fun _ => rfl, fun _ => rfl, fun x => ?_⟩
  · rintro ⟨x, rfl⟩
    exact x.2
  · apply Units.ext
    rw [ReciprocalEntire.coe_eval, coe_value]
    rfl

/-- The p-adic adapter is `Equiv.subtypeEquivRight` along
`regularPoint_iff_polynomial_ne_zero` at the actual conductor and uniformizer unit;
`regularLValue` uses the same denominator and certificate as `value`. -/
theorem padicAbelianComparison {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData)
    (χ : @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology) :
    PadicAbelianComparison T χ :=
  ⟨PadicAbelian.regularPoint_iff_polynomial_ne_zero T χ, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun x => value_mapInput _ _ _, fun _ => rfl⟩

/-- The exact published comparison statement, with all four universes independent. -/
theorem comparisonStatement : ComparisonStatement.{uK, uV, uW, uF} := by
  refine ⟨?_, ?_, reciprocalEntireComparison, ?_⟩
  · intro K _ V _ _ _ A
    exact eulerComparison A
  · intro V _ _ _ A q hq
    exact spectralEulerComparison A q hq
  · intro p _ F T χ
    exact padicAbelianComparison T χ

end Langlands.LocalFactor.RegularEvaluation
