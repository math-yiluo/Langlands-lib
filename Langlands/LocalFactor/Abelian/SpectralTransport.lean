import Langlands.LocalFactor.Abelian.Transport
import Langlands.LocalFactor.Abelian.Padic

/-! # Rational and spectral abelian factors under actual field transport -/

noncomputable section

open MeasureTheory

namespace Langlands.PadicField.AbelianTransport

open HarmonicAnalysis ConductorTransport LocalFactor.PadicAbelian

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (e : F.Carrier ≃ₐ[Padic p] E.Carrier)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : TopologicalSpace E.Carrier := E.canonicalTopologicalData.topology
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : MeasurableSpace E.Carrier := borel E.Carrier

/-- Unramified character values agree on the independently chosen uniformizers. -/
theorem uniformizer_value_eq (χ : Quasicharacter F.Carrier)
    (hχ : F.canonicalTopologicalData.IsUnramifiedQuasicharacter χ) :
    quasicharacter F E e χ (uniformizerUnit E.canonicalTopologicalData) =
      χ (uniformizerUnit F.canonicalTopologicalData) := by
  have hE := (isUnramifiedQuasicharacter_iff F E e χ).2 hχ
  have hv :
      E.canonicalTopologicalData.discreteValuation
          (uniformizerUnit E.canonicalTopologicalData : E.Carrier) =
        E.canonicalTopologicalData.discreteValuation
          (unitsEquiv F E e (uniformizerUnit F.canonicalTopologicalData) : E.Carrier) := by
    rw [unitsEquiv_apply, CanonicalTransport.discreteValuation_map]
    simpa only [zpow_one] using
      (uniformizerUnit_zpow_value E.canonicalTopologicalData 1).trans
        (uniformizerUnit_zpow_value F.canonicalTopologicalData 1).symm
  have h := E.canonicalTopologicalData.unramified_value_eq_of_value_eq
    (quasicharacter F E e χ) hE _ _ hv
  simpa only [quasicharacter_apply, ContinuousMulEquiv.symm_apply_apply] using h

include e in
/-- The intrinsic spectral variable agrees at the same complex coordinate. -/
theorem spectralVariable_eq (s : ℂ) :
    spectralVariable E.canonicalTopologicalData s =
      spectralVariable F.canonicalTopologicalData s := by
  simp only [spectralVariable, CanonicalTransport.residueCardinality_eq F E e]

/-- Equality of the actual Euler polynomials, retaining their constant term one. -/
theorem lPolynomial_eq (χ : Quasicharacter F.Carrier) :
    lPolynomial E.canonicalTopologicalData (quasicharacter F E e χ) =
      lPolynomial F.canonicalTopologicalData χ := by
  classical
  unfold lPolynomial
  rw [multiplicativeConductor_eq]
  by_cases h : F.canonicalTopologicalData.multiplicativeConductor χ = 0
  · simp only [h, ite_true, uniformizer_value_eq F E e χ
      ((F.canonicalTopologicalData.multiplicativeConductor_eq_zero_iff χ).1 h)]
  · simp only [h, ite_false]

/-- The reciprocal Euler factors agree as rational functions, with poles retained. -/
theorem rationalLFactor_eq (χ : Quasicharacter F.Carrier) :
    rationalLFactor E.canonicalTopologicalData (quasicharacter F E e χ) =
      rationalLFactor F.canonicalTopologicalData χ := by
  simp only [rationalLFactor, lPolynomial_eq]

/-- The exact regularity predicate is preserved at the unchanged spectral coordinate. -/
theorem regularPoint_iff (χ : Quasicharacter F.Carrier) (s : ℂ) :
    RegularPoint E.canonicalTopologicalData (uniformizerUnit E.canonicalTopologicalData)
      (quasicharacter F E e χ)
      (E.canonicalTopologicalData.multiplicativeConductor (quasicharacter F E e χ)) s ↔
    RegularPoint F.canonicalTopologicalData (uniformizerUnit F.canonicalTopologicalData)
      χ (F.canonicalTopologicalData.multiplicativeConductor χ) s := by
  rw [regularPoint_iff_polynomial_ne_zero, regularPoint_iff_polynomial_ne_zero,
    lPolynomial_eq, spectralVariable_eq F E e]

/-- Equivalence of actual regular spectral domains, preserving the complex coordinate. -/
def regularPointEquiv (χ : Quasicharacter F.Carrier) :
    {s : ℂ // RegularPoint F.canonicalTopologicalData
      (uniformizerUnit F.canonicalTopologicalData) χ
      (F.canonicalTopologicalData.multiplicativeConductor χ) s} ≃
    {s : ℂ // RegularPoint E.canonicalTopologicalData
      (uniformizerUnit E.canonicalTopologicalData) (quasicharacter F E e χ)
      (E.canonicalTopologicalData.multiplicativeConductor (quasicharacter F E e χ)) s} where
  toFun s := ⟨s.val, (regularPoint_iff F E e χ s.val).2 s.property⟩
  invFun s := ⟨s.val, (regularPoint_iff F E e χ s.val).1 s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem regularPointEquiv_val (χ : Quasicharacter F.Carrier)
    (s : {s : ℂ // RegularPoint F.canonicalTopologicalData
      (uniformizerUnit F.canonicalTopologicalData) χ
      (F.canonicalTopologicalData.multiplicativeConductor χ) s}) :
    (regularPointEquiv F E e χ s).val = s.val := rfl

/-- Unit-valued reciprocal evaluations agree on the corresponding regular domains. -/
theorem regularLValue_eq (χ : Quasicharacter F.Carrier)
    (s : {s : ℂ // RegularPoint F.canonicalTopologicalData
      (uniformizerUnit F.canonicalTopologicalData) χ
      (F.canonicalTopologicalData.multiplicativeConductor χ) s}) :
    regularLValue E.canonicalTopologicalData (quasicharacter F E e χ)
      (regularPointEquiv F E e χ s) =
        regularLValue F.canonicalTopologicalData χ s := by
  apply Units.ext
  change ((lPolynomial E.canonicalTopologicalData (quasicharacter F E e χ)).eval
    (spectralVariable E.canonicalTopologicalData s.val))⁻¹ =
      ((lPolynomial F.canonicalTopologicalData χ).eval
        (spectralVariable F.canonicalTopologicalData s.val))⁻¹
  rw [lPolynomial_eq, spectralVariable_eq F E e]

/-- The actual spectral Gauss integrand is preserved by the field map. -/
theorem gaussIntegrand_map (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (s : ℂ) (x : F.Carrier) :
    gaussIntegrand E.canonicalTopologicalData (quasicharacter F E e χ)
      (additiveCharacter F E e ψ).toAddChar s (e x) =
        gaussIntegrand F.canonicalTopologicalData χ ψ.toAddChar s x := by
  simp only [gaussIntegrand, characterExtension_eq_extendZero, extendZero_map,
    CanonicalTransport.normalizedAbs_map]
  change _ * (additiveCharacter F E e ψ (e x) : ℂ) = _ * (ψ x : ℂ)
  rw [additiveCharacter_apply, e.symm_apply_apply]

/-- The order-shell presentation corresponds to the same valuation-shell preimage. -/
theorem preimage_gaussShell (d : ℤ) :
    e ⁻¹' gaussShell E.canonicalTopologicalData d =
      gaussShell F.canonicalTopologicalData d := by
  simp only [gaussShell_eq_valuationShell, preimage_valuationShell]

/-- The fixed-Haar spectral epsilon expressions agree for every complex parameter. -/
theorem epsilon_eq (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier) (s : ℂ) :
    epsilon E.canonicalTopologicalData (quasicharacter F E e χ)
      (additiveCharacter F E e ψ) (haarMeasure F E e μ).measure s =
        epsilon F.canonicalTopologicalData χ ψ μ.measure s := by
  classical
  unfold epsilon epsilonAt
  rw [multiplicativeConductor_eq, additiveConductor_eq]
  by_cases h : F.canonicalTopologicalData.multiplicativeConductor χ = 0
  · simp only [h, ite_true, uniformizer_value_eq F E e χ
      ((F.canonicalTopologicalData.multiplicativeConductor_eq_zero_iff χ).1 h),
      CanonicalTransport.residueCardinality_eq F E e, integerRing_eq]
    have hv := integerVolume_eq F E e μ
    change ((haarMeasure F E e μ).measure
      (E.canonicalTopologicalData.Integers : Set E.Carrier)).toReal =
        (μ.measure (F.canonicalTopologicalData.Integers : Set F.Carrier)).toReal at hv
    rw [hv]
  · simp only [h, ite_false]
    rw [setIntegral_haarMeasure, preimage_gaussShell]
    simp only [gaussIntegrand_map]

/-- The unshifted Deligne convention keeps the transported Haar measure as input. -/
theorem deligneConstant_eq (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier) :
    deligneConstant E.canonicalTopologicalData (quasicharacter F E e χ)
      (additiveCharacter F E e ψ) (haarMeasure F E e μ).measure =
        deligneConstant F.canonicalTopologicalData χ ψ μ.measure :=
  epsilon_eq F E e χ ψ μ 0

/-- The centered convention is preserved without choosing a self-dual measure. -/
theorem centeredConstant_eq (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier) :
    centeredConstant E.canonicalTopologicalData (quasicharacter F E e χ)
      (additiveCharacter F E e ψ) (haarMeasure F E e μ).measure =
        centeredConstant F.canonicalTopologicalData χ ψ μ.measure :=
  epsilon_eq F E e χ ψ μ (1 / 2)

end Langlands.PadicField.AbelianTransport
