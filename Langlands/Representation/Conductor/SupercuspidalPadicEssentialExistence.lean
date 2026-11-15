import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput
import Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction
import Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction
import Langlands.Representation.Conductor.TrivialCharacterEpsilonReduction

/-!
# Essential vectors of supercuspidal representations over p-adic fields

Let `K` be a p-adic field with its canonical structures and let `π` be an irreducible
admissible generic supercuspidal representation of `GL_(n+2)(K)`. Under Jacquet's
normalizations, every nonzero Whittaker model of `π` contains an essential vector.

By JPSS 1983, §(8.1), Proposition (i), the standard L-factor of `π` is `1`. The
Whittaker function `W₀` on `GL_(n+2)` supported on `N · GL_(n+2)(O)` with
`W₀(u k) = ψ(u)` is a compactly supported smooth function on the mirabolic subgroup,
so the Kirillov theorem lifts it to a vector `w` of the model. The corank-one integral of
`w` against every spherical function `W(·; x; ψ̄)` of `GL_(n+1)` is the integral of the
indicator of the image of `GL_(n+1)(O)` in `N \ GL_(n+1)`, which is `1 = ∏ 1⁻¹`. So `w`
is essential with the L-polynomial `1`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial QuotientIntegration
open Langlands.GeneralLinear.Iwasawa
open Langlands.RankinSelberg.HighlyRamified

universe uF uV

namespace SupercuspidalPadic

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p)

local instance supercuspidalEssentialTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance supercuspidalEssentialValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance supercuspidalEssentialLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

/-- An absolute value of the canonical p-adic field that takes the value `q⁻¹` at a
uniformizing element, where `q` is the residue cardinality, and the value `1` on
valuation units, is the normalized absolute value of the canonical data. -/
theorem eq_normalizedAbsoluteValue :
    ∀ (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation K.Carrier).integer) →
    ∀ (abv : AbsoluteValue K.Carrier ℝ) (ϖ : K.Carrierˣ),
      IsUniformizingElement (ValuativeRel.valuation K.Carrier) ϖ →
      abv (ϖ : K.Carrier) = (q : ℝ)⁻¹ →
      (∀ x : K.Carrier, ValuativeRel.valuation K.Carrier x = 1 → abv x = 1) →
      abv = normalizedAbsoluteValue K.canonicalTopologicalData := by
  intro q hq abv ϖ hϖ habv hunit
  obtain ⟨ϖ₀, hϖ₀, habv₀⟩ := exists_uniformizingElement_normalizedAbs K
  have h1 := AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances q hq abv ϖ hϖ
    habv hunit
  have h2 := AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances q hq
    (normalizedAbsoluteValue K.canonicalTopologicalData) ϖ₀ hϖ₀
    (by rw [habv₀, hq]; rfl) (normalizedAbsoluteValue_eq_one K)
  exact h1.trans h2.symm

/-- **The standard L-polynomial of a supercuspidal representation is `1`** (JPSS 1983,
§(8.1), Proposition (i), against the trivial character of `GL_1`), for the canonical
residue cardinality and normalized absolute value. -/
theorem isCharacterLPolynomial_one_of_isSupercuspidal {n : ℕ} {V : Type uV}
    [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter K.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1 + 1) K.Carrier) V)
    (hirr : Representation.IsIrreducible π)
    (hsc : IsSupercuspidal π) :
    letI := borel (Langlands.GeneralLinear (0 + 1) K.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (0 + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient 0 K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient 0 K.Carrier) := ⟨rfl⟩
    IsCharacterLPolynomial K.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue K.canonicalTopologicalData) (rankOneQuotientHaar K.Carrier) 1
      π 1 := by
  obtain ⟨ν⟩ := nonempty_selfDualHaar K ψ
  have hσ : IsOfWhittakerType 0 (standardCharacter ψ 0)
      (rankOneCharacter (1 : K.Carrierˣ →* ℂˣ)) :=
    scalar_isOfWhittakerType_rankOne ψ _ rankOneCharacter_one_isSmooth
  have hL : IsPadicPairLPolynomial K ψ ν.val π (rankOneCharacter (1 : K.Carrierˣ →* ℂˣ)) 1 :=
    supercuspidalUnequalRankLFactor.{uF, uV, 0} p K ψ ν (n + 1) 0 π
      (rankOneCharacter (1 : K.Carrierˣ →* ℂˣ)) hirr hsc hσ (by omega)
  apply isCharacterLPolynomial_of_isPadicSymmetricLPolynomial K ψ ν.val π
  rw [IsPadicSymmetricLPolynomial, ite_eq_left (Nat.zero_le _)]
  exact hL

section Existence

variable {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) K.Carrier)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier)]
  [MeasurableSpace (upperUnipotent (n + 1) K.Carrier)]
  [BorelSpace (upperUnipotent (n + 1) K.Carrier)]
  [MeasurableSpace (LeftUnipotentQuotient n K.Carrier)]
  [MeasurableSpace (LeftUnipotentQuotient 0 K.Carrier)]
  [MeasurableSpace (Langlands.GeneralLinear 1 K.Carrier)]
  [BorelSpace (Langlands.GeneralLinear 1 K.Carrier)]

/-- **Essential vectors of supercuspidal representations.** Under Jacquet's
normalizations `h`, every nonzero Whittaker model of an irreducible admissible generic
supercuspidal representation `π` of `GL_(n+2)(K)` contains an essential vector: the
Kirillov lift of the zero-cell Whittaker function, with the L-polynomial `1`. -/
theorem exists_isEssentialVector
    {q : ℕ} {ψ : UnitaryAdditiveCharacter K.Carrier}
    {abv : AbsoluteValue K.Carrier ℝ} {ϖ : K.Carrierˣ}
    {μ : Measure (LeftUnipotentQuotient n K.Carrier)}
    (h : IsJacquetNormalization q ψ abv ϖ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) K.Carrier) V)
    (hπ : IsGeneric ψ (n + 1) π)
    (hsc : IsSupercuspidal π)
    (ℓ : glFunctionals ψ (n + 1) π) (hℓ : ℓ.val ≠ 0) :
    ∃ w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w := by
  let T := K.canonicalTopologicalData
  have hϖ := h.uniformizer
  have hψ := h.conductor
  have hμ := h.measure
  have habvT := eq_normalizedAbsoluteValue K q h.residueCardinality abv ϖ hϖ
    h.abv_uniformizer h.abv_unit
  have hq : q = T.residueCardinality := h.residueCardinality
  have hB : BorelSpace (LeftUnipotentQuotient n K.Carrier) := h.borel
  have hB0 : BorelSpace (LeftUnipotentQuotient 0 K.Carrier) := h.borel_rankOne
  -- Normalize the residue cardinality, the absolute value and the Borel structures.
  subst habvT hq
  obtain rfl := hB.measurable_eq
  obtain rfl := hB0.measurable_eq
  obtain rfl := (inferInstance : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier)).measurable_eq
  obtain rfl := (inferInstance : BorelSpace (upperUnipotent (n + 1) K.Carrier)).measurable_eq
  obtain rfl := (inferInstance : BorelSpace (Langlands.GeneralLinear 1 K.Carrier)).measurable_eq
  -- The Kirillov lift of the zero-cell function.
  obtain ⟨w, hw⟩ := Whittaker.modelKirillovTransfer whittakerTypeKirillov p inferInstance K T
    (n + 1) V π ψ (isOfWhittakerType_of_isGeneric K hπ) ℓ hℓ
    (zeroCellWhittaker hϖ hψ.1 (n + 1)) (isMirabolicTestFunction_zeroCellWhittaker hϖ hψ.1 (n + 1))
  refine ⟨w, ⟨⟨1, isCharacterLPolynomial_one_of_isSupercuspidal K ψ π hπ.1 hsc, ?_⟩, ?_⟩⟩
  · -- the corank-one integrals are identically `1`
    intro x
    have hint := integrable_integral_corankOneIntegrand_zeroCell K n μ hμ hϖ hψ.1
      (inverseSphericalWhittaker hψ.1 hϖ T.residueCardinality x)
      (fun g k hk => inverseSphericalWhittaker_mul_integral hψ.1 hϖ _ x g hk)
      (inverseSphericalWhittaker_one hψ.1 hϖ _ x)
    have hrw : ∀ s, corankOneIntegrand ψ (normalizedAbsoluteValue T) w.val
        (inverseSphericalWhittaker hψ.1 hϖ T.residueCardinality x) s =
        corankOneIntegrand ψ (normalizedAbsoluteValue T) (zeroCellWhittaker hϖ hψ.1 (n + 1))
          (inverseSphericalWhittaker hψ.1 hϖ T.residueCardinality x) s :=
      fun s => corankOneIntegrand_eq_zeroCell hϖ hψ.1 w.val hw _ s
    refine ⟨⟨0, fun s _ => ?_⟩, ?_⟩
    · unfold CorankOneConverges
      rw [hrw]
      exact (hint s).1
    · have hfac : essentialFactor (1 : ℂ[X]) x = 1 := by
        simp [essentialFactor]
      rw [hfac]
      apply hasRationalContinuation_one_of_eq_on_halfPlane 0
      intro s _
      unfold corankOneIntegral
      rw [hrw]
      exact (hint s).2
  · -- right `GL_(n+1)(O)`-invariance of the restriction to `diag(GL_(n+1), 1)`
    intro g k
    rw [hw (rankInclusion 1 (g * k.val)) (rankInclusion_lastRow _),
      hw (rankInclusion 1 g) (rankInclusion_lastRow _), map_mul]
    exact zeroCellWhittaker_mul_integral hϖ hψ.1 (n + 1) _
      (rankInclusion_mem_integralSubgroup k.property)

end Existence

end SupercuspidalPadic

end Langlands.Conductor
