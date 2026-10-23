import Langlands.Representation.Shahidi.UnipotentProduct
import Langlands.Representation.Shahidi.PairingMeasure
import Langlands.Representation.Shahidi.KirillovMeasure
import Langlands.Representation.Shahidi.QuotientTransport
import Langlands.Representation.Shahidi.CoordinateMeasures
import Langlands.Representation.Shahidi.CompactMeasures
import Langlands.Representation.Shahidi.RadicalMeasures

/-! # Coupled equal-rank measure conditions

The actual measures in Shahidi's items 1–7, with the shared pairing and the
smaller-group Weil equation. These are predicates on supplied choices; no
existence, comparison theorem, or extension to unequal ranks is asserted.
-/

noncomputable section

namespace Langlands.Shahidi

open MeasureTheory MeasureTheory.Measure GeneralLinear Whittaker HarmonicAnalysis QuotientIntegration

universe uF uV

/-- Both invariant directions and regularity are explicit in the group measures. -/
def IsRegularTwoSidedHaar {G : Type*} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] (μ : Measure G) : Prop :=
  μ.IsHaarMeasure ∧ μ.Regular ∧ IsMulRightInvariant μ

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
variable (O : Subring F) (n : ℕ)
variable [MeasurableSpace Fˣ]
  [MeasurableSpace (Langlands.GeneralLinear n F)]
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent n F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (KirillovQuotient n F)]
  [MeasurableSpace (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O)]
  [MeasurableSpace (Langlands.GeneralLinear ((n + 1) + (n + 1)) F)]

/-- The supplied measures, all on their actual groups, coordinate spaces or
left quotient. Scalar coordinate factors are regular additive Haar measures.
No equation among these choices is included in this data structure. -/
structure EqualRankMeasureData where
  dn₁ : Measure (upperUnipotent n F)
  dn₂ : Measure (Fin n → F)
  dn : Measure (upperUnipotent (n + 1) F)
  quotient : Measure (KirillovQuotient n F)
  primedQuotient : Measure (KirillovQuotient n F)
  daStar : Measure (Langlands.GeneralLinear n F)
  dzStar : Measure Fˣ
  dk : Measure (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O)
  dgStar : Measure (Langlands.GeneralLinear (n + 1) F)
  dx : Fin (n + 1) → AdditiveHaarMeasure F
  da : Fin (n + 1) → Fin (n + 1) → AdditiveHaarMeasure F
  intertwining : Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) F)
  jacquet : Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) F)
  swappedJacquet : Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) F)
  upper : Measure (Langlands.GeneralLinear ((n + 1) + (n + 1)) F)
  lower : Measure (Langlands.GeneralLinear ((n + 1) + (n + 1)) F)

variable {O n}

/-- Haar and regularity conditions on the actual group and additive measures.
The ambient pushforwards on `GL_(2n+2)` are not Haar measures on that full group. -/
def IsEqualRankHaarData (d : EqualRankMeasureData O n) : Prop :=
  IsRegularTwoSidedHaar d.dn₁ ∧
  d.dn₂.IsAddHaarMeasure ∧ d.dn₂.Regular ∧
  IsRegularTwoSidedHaar d.dn ∧
  IsRegularTwoSidedHaar d.daStar ∧
  IsRegularTwoSidedHaar d.dzStar ∧
  IsRegularTwoSidedHaar d.dk ∧
  IsRegularTwoSidedHaar d.dgStar ∧
  d.jacquet.IsAddHaarMeasure ∧ d.jacquet.Regular ∧
  (matrixCoordinateMeasure d.da).IsAddHaarMeasure ∧
  (matrixCoordinateMeasure d.da).Regular

variable [IsTopologicalRing F]
  [BorelSpace (Langlands.GeneralLinear n F)]
  [BorelSpace (upperUnipotent n F)]
  [BorelSpace (KirillovQuotient n F)]

/-- Composition of the unprimed quotient measure and `dn₁` is the supplied
smaller-group measure, via the integrable Weil equation. The right-invariance
witness is existentially quantified and supplies only the averaging instance. -/
def IsSmallerQuotientCompatible (d : EqualRankMeasureData O n) : Prop :=
  ∃ h : IsMulRightInvariant d.dn₁,
    letI := h
    QuotientIntegration.IsCompatible (upperUnipotent n F) d.daStar d.dn₁ d.quotient

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ψ : UnitaryAdditiveCharacter F)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (b : InvariantPositiveForm π) (ℓ : glFunctionals ψ n π)

/-- Measure item 1 with the same actual Hermitian form in Lemma 1.1 and
Proposition 1.2, ordered unipotent product, quotient reflection, and Weil
composition. Nonzeroness of the chosen Whittaker functional is explicit. -/
def IsPairingMeasureCompatible (d : EqualRankMeasureData O n) : Prop :=
  ℓ.val ≠ 0 ∧
  IsUnipotentProductMeasure d.dn₁ d.dn₂ d.dn ∧
  IsWhittakerPairingNormalized ψ n π b ℓ d.dn ∧
  IsKirillovPairingNormalized ψ n π ℓ b d.primedQuotient ∧
  IsQuotientReflectionRelated n F d.quotient d.primedQuotient ∧
  IsSmallerQuotientCompatible d

variable {ψ π b ℓ}

omit [BorelSpace (Langlands.GeneralLinear n F)] in
/-- The primed quotient is a nonzero regular right-invariant quotient measure.
These facts follow from Weil compatibility and reflection, rather than from
an additional unspecified choice of quotient measure. -/
theorem IsPairingMeasureCompatible.primed_quotient_properties
    {d : EqualRankMeasureData O n} (h : IsPairingMeasureCompatible ψ π b ℓ d) :
    d.primedQuotient ≠ 0 ∧ d.primedQuotient.Regular ∧
      ∀ g : Langlands.GeneralLinear n F,
        MeasurePreserving (rightTranslate (upperUnipotent n F) g)
          d.primedQuotient d.primedQuotient := by
  rcases h with ⟨_, _, _, _, href, hd, hcomp⟩
  let := hd
  have he : d.primedQuotient = reflectedQuotientMeasure n F d.quotient :=
    (isQuotientReflectionRelated_comm n F _ _).mp href
  rw [he]
  let := hcomp.regular
  exact ⟨(reflectedQuotientMeasure_ne_zero_iff n F _).2 hcomp.nonzero,
    reflectedQuotientMeasure_regular n F _,
    reflectedQuotientMeasure_right_invariant n F _ hcomp.right_invariant⟩

variable (ψ π b ℓ)

variable [IsLocalRing O]

/-- All seven equal-rank measure items, with the shared measure and pairing
choices explicit. The analytic hypotheses for their existence are separate. -/
def IsEqualRankMeasureNormalized (abv : AbsoluteValue F ℝ)
    (d : EqualRankMeasureData O n) : Prop :=
  IsEqualRankHaarData d ∧
  IsPairingMeasureCompatible ψ π b ℓ d ∧
  IsCompactVolumeCompatible O n d.daStar d.dn₂ d.dzStar d.dk d.dx ∧
  IsIwasawaMeasureCompatible O n abv d.dn₂ d.daStar d.dzStar d.dk d.dgStar ∧
  IsCoordinateMeasureCompatible n abv ψ d.dzStar d.dgStar d.dx d.da ∧
  IsEqualRankRadicalMeasureCompatible (n + 1) (matrixCoordinateMeasure d.da)
    d.intertwining d.jacquet d.swappedJacquet d.upper d.lower

variable {ψ π b ℓ}

omit [BorelSpace (Langlands.GeneralLinear n F)] [BorelSpace (KirillovQuotient n F)] in
/-- Both pairing equations refer to the identical supplied form and functional. -/
theorem IsEqualRankMeasureNormalized.pairings {abv : AbsoluteValue F ℝ}
    {d : EqualRankMeasureData O n} (h : IsEqualRankMeasureNormalized ψ π b ℓ abv d) :
    IsWhittakerPairingNormalized ψ n π b ℓ d.dn ∧
      IsKirillovPairingNormalized ψ n π ℓ b d.primedQuotient :=
  ⟨h.2.1.2.2.1, h.2.1.2.2.2.1⟩

omit [BorelSpace (Langlands.GeneralLinear n F)] [BorelSpace (KirillovQuotient n F)] in
/-- The first matrix-coordinate factor has the weighted central measure. -/
theorem IsEqualRankMeasureNormalized.corner {abv : AbsoluteValue F ℝ}
    {d : EqualRankMeasureData O n} (h : IsEqualRankMeasureNormalized ψ π b ℓ abv d) :
    (d.da 0 0).measure = fieldMeasureFromUnits abv d.dzStar :=
  h.2.2.2.2.1.corner

variable [BorelSpace (Langlands.GeneralLinear ((n + 1) + (n + 1)) F)]
  [BorelSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F)]

omit [BorelSpace (Langlands.GeneralLinear n F)] [BorelSpace (KirillovQuotient n F)] in
/-- The intertwining coordinate measure is forced by item 5, and the Jacquet
coordinate measures agree with each other, without being forced to that measure. -/
theorem IsEqualRankMeasureNormalized.radical_coordinates {abv : AbsoluteValue F ℝ}
    {d : EqualRankMeasureData O n} (h : IsEqualRankMeasureNormalized ψ π b ℓ abv d) :
    d.intertwining = matrixCoordinateMeasure d.da ∧ d.jacquet = d.swappedJacquet :=
  h.2.2.2.2.2.coordinate_eq

end Langlands.Shahidi
