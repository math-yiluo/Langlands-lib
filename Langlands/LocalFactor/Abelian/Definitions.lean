import Langlands.HarmonicAnalysis.Conductor
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The actual abelian Gauss integral on a finite p-adic field. -/

noncomputable section

open MeasureTheory Topology
open scoped WithZero WithZeroTopology

namespace Langlands.HarmonicAnalysis.Quasicharacter

universe u
variable {F : Type u} [Field F] [TopologicalSpace F]

/-- A quasicharacter as a complex-valued function on the field, extended by
zero only at zero. On nonzero inputs this is the original unit-valued character. -/
def extendZero (χ : Quasicharacter F) (x : F) : ℂ := by
  classical
  exact if h : x = 0 then 0 else (χ (Units.mk0 x h) : ℂ)

@[simp]
theorem extendZero_zero (χ : Quasicharacter F) : extendZero χ 0 = 0 := by
  simp [extendZero]

@[simp]
theorem extendZero_unit (χ : Quasicharacter F) (u : Fˣ) :
    extendZero χ (u : F) = (χ u : ℂ) := by
  simp [extendZero]

theorem extendZero_ne_zero (χ : Quasicharacter F) {x : F} (hx : x ≠ 0) :
    extendZero χ x ≠ 0 := by
  simp [extendZero, hx]

theorem continuousOn_extendZero [ContinuousInv₀ F] (χ : Quasicharacter F) :
    ContinuousOn (extendZero χ) {x : F | x ≠ 0} := by
  have hunit : Continuous (fun x : {x : F // x ≠ 0} => Units.mk0 x.val x.property) :=
    Units.isEmbedding_val₀.isInducing.continuous_iff.mpr continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : {x : F // x ≠ 0} => extendZero χ x.val)
  apply (Units.continuous_val.comp (χ.continuous.comp hunit)).congr
  intro x
  simp only [Function.comp_apply, extendZero, dite_eq_right x.property]
  rfl

/-- The abelian epsilon integrand, with additive character sign `+x`.
Its use below is on a compact valuation shell disjoint from zero. -/
def epsilonIntegrand (χ : Quasicharacter F) (ψ : UnitaryAdditiveCharacter F)
    (x : F) : ℂ :=
  (extendZero χ x)⁻¹ * ψ.complex x

theorem continuousOn_epsilonIntegrand [ContinuousInv₀ F]
    (χ : Quasicharacter F) (ψ : UnitaryAdditiveCharacter F) :
    ContinuousOn (epsilonIntegrand χ ψ) {x : F | x ≠ 0} :=
  ((continuousOn_extendZero χ).inv₀ (fun _x hx => extendZero_ne_zero χ hx)).mul
    ψ.continuous_complex.continuousOn

end Langlands.HarmonicAnalysis.Quasicharacter

namespace Langlands.PadicField.TopologicalData

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology
    (@borel F.Carrier T.topology)

/-- The actual valuation shell of elements of order `-k`. -/
def valuationShell (k : ℤ) : Set F.Carrier :=
  {x | T.discreteValuation x = WithZero.exp k}

theorem valuationShell_ne_zero (k : ℤ) {x : F.Carrier}
    (hx : x ∈ T.valuationShell k) : x ≠ 0 := by
  intro h
  have hv : (0 : ℤᵐ⁰) = WithZero.exp k := by simpa [valuationShell, h] using hx
  exact WithZero.exp_ne_zero hv.symm

/-- A nonzero valuation shell is compact in the supplied local-field topology. -/
theorem valuationShell_compact_closed (k : ℤ) :
    letI := T.topology
    IsCompact (T.valuationShell k) ∧ IsClosed (T.valuationShell k) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  let γ := e.symm (WithZero.exp k)
  have hs : T.valuationShell k = {x | ValuativeRel.valuation F.Carrier x = γ} := by
    ext x
    change e (ValuativeRel.valuation F.Carrier x) = WithZero.exp k ↔
      ValuativeRel.valuation F.Carrier x = γ
    constructor
    · intro h
      apply e.injective
      simpa [γ] using h
    · intro h
      rw [h]
      exact e.apply_symm_apply _
  rw [hs]
  have hc : IsClosed {x | ValuativeRel.valuation F.Carrier x = γ} :=
    isClosed_eq IsValuativeTopology.continuous_valuation continuous_const
  exact ⟨(IsNonarchimedeanLocalField.isCompact_closedBall F.Carrier γ).of_isClosed_subset
    hc (fun _x hx => hx.le), hc⟩

open HarmonicAnalysis

/-- The compact shell `c⁻¹ Oˣ` in Tate's ramified formula, expressed intrinsically
as the shell of order `-(n(ψ)+a(χ))`. -/
def epsilonShell (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter) : Set F.Carrier :=
  T.valuationShell (T.additiveConductor ψ + (T.multiplicativeConductor χ : ℤ))

theorem epsilonIntegrand_integrable (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    IntegrableOn (Quasicharacter.epsilonIntegrand χ ψ) (T.epsilonShell χ ψ) μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  apply ContinuousOn.integrableOn_compact'
  · exact (T.valuationShell_compact_closed _).1
  · exact (T.valuationShell_compact_closed _).2.measurableSet
  · exact (Quasicharacter.continuousOn_epsilonIntegrand χ ψ).mono
      (fun _x hx => T.valuationShell_ne_zero _ hx)

/-- The convergent additive-Haar Gauss integral in Tate (3.2.6.2).
The integral is constructed for every quasicharacter; it is used as the epsilon
expression in the ramified branch. -/
def abelianGaussIntegral (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) : ℂ :=
  letI := T.topology
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  ∫ x in T.epsilonShell χ ψ, Quasicharacter.epsilonIntegrand χ ψ x ∂μ.measure

private theorem exists_abelianScale (k : ℤ) :
    ∃ c : F.Carrierˣ, T.discreteValuation (c : F.Carrier) = WithZero.exp (-k) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  obtain ⟨x, hx⟩ :=
    ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-k)))
  have hv : T.discreteValuation x = WithZero.exp (-k) := by
    change e (ValuativeRel.valuation F.Carrier x) = WithZero.exp (-k)
    rw [hx, e.apply_symm_apply]
  have hx0 : x ≠ 0 := by
    intro h
    have hzero : (0 : ℤᵐ⁰) = WithZero.exp (-k) := by simpa [h] using hv
    exact WithZero.exp_ne_zero hzero.symm
  exact ⟨Units.mk0 x hx0, hv⟩

/-- An actual field unit of prescribed order, chosen from the proved
surjectivity of the specified local-field valuation. -/
def abelianScale (k : ℤ) : F.Carrierˣ :=
  (T.exists_abelianScale k).choose

theorem abelianScale_value (k : ℤ) :
    T.discreteValuation (T.abelianScale k : F.Carrier) = WithZero.exp (-k) :=
  (T.exists_abelianScale k).choose_spec

theorem abelianScale_order (k : ℤ) : T.ord (T.abelianScale k : F.Carrier) = k := by
  simp [ord, T.abelianScale_value]

/-- The shell really is the inverse scale times the group of integral units. -/
theorem mem_valuationShell_iff_scaled_integral_unit (k : ℤ) (u : F.Carrierˣ) :
    (u : F.Carrier) ∈ T.valuationShell k ↔
      u * T.abelianScale k ∈ T.principalUnits 0 := by
  rw [T.mem_principalUnits_zero, Units.val_mul, map_mul, T.abelianScale_value]
  change T.discreteValuation (u : F.Carrier) = WithZero.exp k ↔
    T.discreteValuation (u : F.Carrier) * WithZero.exp (-k) = 1
  have h : (WithZero.exp (-k) : ℤᵐ⁰)⁻¹ = WithZero.exp k := by
    rw [← WithZero.exp_neg]
    simp
  rw [← h]
  exact (mul_eq_one_iff_eq_inv₀ WithZero.exp_ne_zero).symm

private theorem abelian_residueCardinality_pos : 0 < T.residueCardinality := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  change 0 < Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F.Carrier).integer)
  exact Nat.card_pos

/-- The absolute-value denominator in the abelian formula is strictly positive. -/
theorem abelianScale_abs_pos (k : ℤ) : 0 < T.normalizedAbs (T.abelianScale k : F.Carrier) := by
  rw [normalizedAbs, ite_eq_right (Units.ne_zero _)]
  exact zpow_pos (Nat.cast_pos.mpr T.abelian_residueCardinality_pos) _

/-- An unramified quasicharacter takes the same value on any two units of the
same valuation. This removes the scale choice from the unramified formula. -/
theorem unramified_value_eq_of_value_eq (χ : MultiplicativeCharacter)
    (hχ : T.IsUnramifiedQuasicharacter χ) (c d : F.Carrierˣ)
    (hcd : T.discreteValuation (c : F.Carrier) = T.discreteValuation (d : F.Carrier)) :
    χ c = χ d := by
  have hd : T.discreteValuation (d : F.Carrier) ≠ 0 := by
    simp
  have hu : T.discreteValuation ((c / d : F.Carrierˣ) : F.Carrier) = 1 := by
    rw [Units.val_div_eq_div_val, map_div₀, hcd, div_self hd]
  exact div_eq_one.mp (by simpa only [map_div] using hχ (c / d) hu)

/-- The normalized absolute value depends only on the valuation of a unit. -/
theorem normalizedAbs_unit_eq_of_value_eq (c d : F.Carrierˣ)
    (hcd : T.discreteValuation (c : F.Carrier) = T.discreteValuation (d : F.Carrier)) :
    T.normalizedAbs (c : F.Carrier) = T.normalizedAbs (d : F.Carrier) := by
  simp only [normalizedAbs, ite_eq_right (Units.ne_zero _), ord, hcd]

/-- The finite additive-Haar volume of the actual integer ring. -/
def integerVolume (μ : LocalHaar) : ℝ :=
  letI := T.topology
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  μ.measure.real (T.Integers : Set F.Carrier)

theorem integerVolume_measure_ne_top (μ : LocalHaar) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    μ.measure (T.Integers : Set F.Carrier) ≠ ⊤ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  exact (IsNonarchimedeanLocalField.isCompact_closedBall F.Carrier 1).measure_ne_top

/-- Tate's measure-dependent abelian epsilon expression. The ramified branch
is a proved convergent integral; the unramified denominator is proved positive.
Nonvanishing and functional-equation identification are separate theorems. -/
def abelianEpsilonExpression (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) : ℂ := by
  classical
  let c := T.abelianScale (T.additiveConductor ψ + (T.multiplicativeConductor χ : ℤ))
  exact if T.multiplicativeConductor χ = 0 then
    (χ c : ℂ) / (T.normalizedAbs (c : F.Carrier) : ℂ) * (T.integerVolume μ : ℂ)
  else T.abelianGaussIntegral χ ψ μ

theorem abelianEpsilonExpression_unramified (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (hχ : T.IsUnramifiedQuasicharacter χ) :
    T.abelianEpsilonExpression χ ψ μ =
      (χ (T.abelianScale (T.additiveConductor ψ)) : ℂ) /
        (T.normalizedAbs (T.abelianScale (T.additiveConductor ψ) : F.Carrier) : ℂ) *
        (T.integerVolume μ : ℂ) := by
  simp [abelianEpsilonExpression, (T.multiplicativeConductor_eq_zero_iff χ).mpr hχ]

theorem abelianEpsilonExpression_ramified (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (hχ : ¬T.IsUnramifiedQuasicharacter χ) :
    T.abelianEpsilonExpression χ ψ μ = T.abelianGaussIntegral χ ψ μ := by
  simp [abelianEpsilonExpression,
    mt (T.multiplicativeConductor_eq_zero_iff χ).mp hχ]

/-- Any scale with the required valuation gives the same unramified expression. -/
theorem abelianEpsilonExpression_unramified_scale (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (hχ : T.IsUnramifiedQuasicharacter χ)
    (c : F.Carrierˣ)
    (hc : T.discreteValuation (c : F.Carrier) =
      WithZero.exp (-T.additiveConductor ψ)) :
    T.abelianEpsilonExpression χ ψ μ =
      (χ c : ℂ) / (T.normalizedAbs (c : F.Carrier) : ℂ) * (T.integerVolume μ : ℂ) := by
  have hval : T.discreteValuation
      (T.abelianScale (T.additiveConductor ψ) : F.Carrier) =
      T.discreteValuation (c : F.Carrier) := (T.abelianScale_value _).trans hc.symm
  rw [T.abelianEpsilonExpression_unramified χ ψ μ hχ,
    T.unramified_value_eq_of_value_eq χ hχ _ c hval,
    T.normalizedAbs_unit_eq_of_value_eq _ c hval]

end Langlands.PadicField.TopologicalData
