import Langlands.Representation.Shahidi.LocalCoefficientPadic
import Langlands.Representation.Shahidi.EqualRankMeasures
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.Classification.ConstituentCompatibility
import Langlands.LocalFactor.Abelian.Padic
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Shahidi's Theorem 5.1: local coefficients and gamma factors of pairs

Shahidi 1984, Theorem 5.1 (printed page 103), announced on printed page 68: for
irreducible admissible generic `π₁` of `GL_m(F)` and `π₂` of `GL_n(F)` there is a
normalization of the measures defining `C_χ(s, π₁ ⊗ π₂)` such that
`C_χ(s, π₁ ⊗ π₂) = ω₂(-1)^m ε'(s, π₁ × π̃₂, ψ)`, where `ω₂` is the central character
of `π₂` and `ε'` is the JPSS gamma factor of page 68.

The measure normalization of pages 75–77 is split into its representation-independent
part `IsEqualRankGeometricNormalized` and the Hermitian-pairing equations of item 1;
`isEqualRankMeasureNormalized_iff` proves that the published full normalization is
exactly their conjunction. The statement asks, at equal ranks, for measures that are the
coordinate measures of an equal-rank datum with the geometric normalization (ranks at
least two), and at all positive ranks, for one scalar Haar measure shared by the two
Jacquet functionals.
-/

noncomputable section

namespace Langlands.Shahidi

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Whittaker GeneralLinear RankinSelberg
  QuotientIntegration

universe uF uV

section EqualRankWeyl

variable {F : Type uF} [Field F] (n : ℕ)

/-- At equal ranks the block Weyl element is an involution. -/
theorem blockWeyl_mul_self_equalRanks : blockWeyl n n F * blockWeyl n n F = 1 := by
  rw [blockWeyl, ← map_mul, ← map_one (GeneralLinear.permutation (n + n) F)]
  congr 1
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    simp only [blockWeylPermutation, Equiv.trans_apply, finCongr_apply, Fin.cast_eq_self,
      finAddFlip_apply_castAdd, finAddFlip_apply_natAdd]

/-- At equal ranks the swapped Jacquet integrand is evaluated on the lower radical `V`:
`w⁻¹ · upper(a) = lower(a) · w⁻¹`, the form of page 78 after `f ↦ R_{w₀⁻¹} f`. -/
theorem blockWeyl_inv_mul_upper_equalRanks (a : Matrix (Fin n) (Fin n) F) :
    (blockWeyl n n F)⁻¹ * upper n n F a = lower n n F a * (blockWeyl n n F)⁻¹ := by
  have hw : (blockWeyl n n F)⁻¹ = blockWeyl n n F :=
    inv_eq_of_mul_eq_one_right (blockWeyl_mul_self_equalRanks n)
  rw [lower, intertwiningUnipotent_equalRanks, hw,
    mul_assoc (blockWeyl n n F * upper n n F a), blockWeyl_mul_self_equalRanks, mul_one]

end EqualRankWeyl

section Geometric

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
variable {O : Subring F} {n : ℕ}
variable [MeasurableSpace Fˣ]
  [MeasurableSpace (Langlands.GeneralLinear n F)]
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent n F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (KirillovQuotient n F)]
  [MeasurableSpace (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O)]
  [MeasurableSpace (Langlands.GeneralLinear ((n + 1) + (n + 1)) F)]
variable [IsTopologicalRing F]
  [BorelSpace (Langlands.GeneralLinear n F)]
  [BorelSpace (upperUnipotent n F)]
  [BorelSpace (KirillovQuotient n F)]
  [IsLocalRing O]

/-- The representation-independent part of Shahidi's equal-rank measure normalization
(pages 75–77): the Haar conditions, the geometric relations of item 1 (`dn = dn₁ dn₂`,
the reflection relating the two quotient measures, and the Weil composition of the
quotient measure with `dn₁` to `d*g`), the compact volumes of items 2 and 3, the
Iwasawa decomposition of item 4, the coordinate measures of items 2, 3 and 5, and the
radical measures of items 6 and 7. Only the two Hermitian-pairing equations of item 1
(Lemma 1.1 and Proposition 1.2), which need a unitary representation, are omitted. -/
def IsEqualRankGeometricNormalized (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (d : EqualRankMeasureData O n) : Prop :=
  IsEqualRankHaarData d ∧
  IsUnipotentProductMeasure d.dn₁ d.dn₂ d.dn ∧
  IsQuotientReflectionRelated n F d.quotient d.primedQuotient ∧
  IsSmallerQuotientCompatible d ∧
  IsCompactVolumeCompatible O n d.daStar d.dn₂ d.dzStar d.dk d.dx ∧
  IsIwasawaMeasureCompatible O n abv d.dn₂ d.daStar d.dzStar d.dk d.dgStar ∧
  IsCoordinateMeasureCompatible n abv ψ d.dzStar d.dgStar d.dx d.da ∧
  IsEqualRankRadicalMeasureCompatible (n + 1) (matrixCoordinateMeasure d.da)
    d.intertwining d.jacquet d.swappedJacquet d.upper d.lower

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ψ : UnitaryAdditiveCharacter F}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {b : InvariantPositiveForm π} {ℓ : glFunctionals ψ n π}

omit [BorelSpace (Langlands.GeneralLinear n F)] [BorelSpace (KirillovQuotient n F)] in
/-- The published full normalization is the geometric normalization together with the
nonzero functional and the two pairing equations of item 1. -/
theorem isEqualRankMeasureNormalized_iff (abv : AbsoluteValue F ℝ)
    (d : EqualRankMeasureData O n) :
    IsEqualRankMeasureNormalized ψ π b ℓ abv d ↔
      IsEqualRankGeometricNormalized ψ abv d ∧ ℓ.val ≠ 0 ∧
        IsWhittakerPairingNormalized ψ n π b ℓ d.dn ∧
        IsKirillovPairingNormalized ψ n π ℓ b d.primedQuotient := by
  constructor
  · rintro ⟨hH, ⟨hℓ, hU, hW, hK, hR, hS⟩, hC, hI, hX, hA⟩
    exact ⟨⟨hH, hU, hR, hS, hC, hI, hX, hA⟩, hℓ, hW, hK⟩
  · rintro ⟨⟨hH, hU, hR, hS, hC, hI, hX, hA⟩, hℓ, hW, hK⟩
    exact ⟨hH, ⟨hℓ, hU, hW, hK, hR, hS⟩, hC, hI, hX, hA⟩

omit [BorelSpace (Langlands.GeneralLinear n F)] [BorelSpace (KirillovQuotient n F)] in
/-- Every fully normalized equal-rank datum is geometrically normalized. -/
theorem IsEqualRankMeasureNormalized.geometric {abv : AbsoluteValue F ℝ}
    {d : EqualRankMeasureData O n} (h : IsEqualRankMeasureNormalized ψ π b ℓ abv d) :
    IsEqualRankGeometricNormalized ψ abv d :=
  ((isEqualRankMeasureNormalized_iff abv d).mp h).1

omit [BorelSpace (Langlands.GeneralLinear n F)] [BorelSpace (KirillovQuotient n F)] in
/-- Under the geometric normalization the intertwining measure is the matrix-coordinate
measure of item 7 and the two Jacquet measures agree (item 6). -/
theorem IsEqualRankGeometricNormalized.radical_coordinates
    [BorelSpace (Langlands.GeneralLinear ((n + 1) + (n + 1)) F)]
    [BorelSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F)] {abv : AbsoluteValue F ℝ}
    {d : EqualRankMeasureData O n} (h : IsEqualRankGeometricNormalized ψ abv d) :
    d.intertwining = matrixCoordinateMeasure d.da ∧ d.jacquet = d.swappedJacquet :=
  h.2.2.2.2.2.2.2.coordinate_eq

end Geometric

/-- The canonical topology of a p-adic field makes it a topological ring. -/
theorem localCoefficientGammaTopologicalRing {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- For the measures `μ` of the intertwining integral `A(s, π, w_(m,n))` and `μJ`, `μJ'`
of the Jacquet functionals on `I(s, π₁ ⊗ π₂)` and `I(-s, π₂ ⊗ π₁)`, the local coefficient
`C_χ(s, π₁ ⊗ π₂)` exists and equals `ω(-1)^(m+1) γ(s, π₁ × π̃₂, ψ)`, with the gamma factor
taken for the self-dual measure `ν`. Both rational functions are evaluated at `q^{-s}`. -/
def IsLocalCoefficientGammaComparison {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {m n : ℕ} {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V₂)
    (ω : F.Carrierˣ →* ℂˣ)
    (μ μJ : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F.Carrier))
    (μJ' : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F.Carrier)) :
    Prop :=
  letI := F.canonicalTopologicalData.topology
  letI := borel F.Carrier
  haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  ∃ C G : RatFunc ℂ,
    F.canonicalTopologicalData.IsShahidiLocalCoefficient π₁ π₂ ψ μ μJ μJ' C ∧
    IsPadicSymmetricGammaFactor F ψ ν.val π₁ (smoothContragredient π₂) G ∧
    C = ((ω (-1) : ℂˣ) : ℂ) ^ (m + 1) • G

/-- Shahidi 1984, Theorem 5.1 (printed page 103), with the measure normalization of
pages 75–77. Let `ψ` be a unitary additive character of the p-adic field `F` whose
largest trivial ideal is `O` (page 70), `ν` the Haar measure on `F` self-dual for `ψ`,
`π₁`, `π₂` irreducible admissible generic representations of `GL_(m+1)(F)` and
`GL_(n+1)(F)`, and `ω` the central character of `π₂`.

* For all ranks, there are additive Haar measures `ν_I` and `ν_J` on `F` such that, with
  the product measure of `ν_I` for `A(s, π, w_(m,n))` and the product measure of the same
  `ν_J` for both Jacquet functionals, `C_χ(s, π₁ ⊗ π₂) = ω(-1)^(m+1) γ(s, π₁ × π̃₂, ψ)`.
* For equal ranks `n + 1 ≥ 2`, there is an equal-rank measure datum `d` over the integer
  ring, with the normalized absolute value, satisfying the geometric normalization of
  pages 75–77, such that the same comparison holds with the measures `d.intertwining`,
  `d.jacquet` and `d.swappedJacquet`. At rank one the recipe degenerates (see the
  Markdown) and only the first part applies. -/
def LocalCoefficientGammaStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
    F.canonicalTopologicalData.additiveConductor ψ = 0 →
    (∀ (m n : ℕ)
      {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
      (π₁ : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) V₁)
      (π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V₂),
      (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ m π₁) →
      (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ n π₂) →
      ∀ ω : F.Carrierˣ →* ℂˣ, Classification.HasGLCentralCharacter F.Carrier (n + 1) π₂ ω →
      letI := F.canonicalTopologicalData.topology
      letI := borel F.Carrier
      ∃ νI νJ : AdditiveHaarMeasure F.Carrier,
        IsLocalCoefficientGammaComparison F ψ ν π₁ π₂ ω
          (rectangularMeasure νI (n + 1) (m + 1)) (rectangularMeasure νJ (n + 1) (m + 1))
          (rectangularMeasure νJ (m + 1) (n + 1))) ∧
    (∀ (n : ℕ), 0 < n →
      ∀ {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
      (π₁ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V₁)
      (π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V₂),
      (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ n π₁) →
      (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ n π₂) →
      ∀ ω : F.Carrierˣ →* ℂˣ, Classification.HasGLCentralCharacter F.Carrier (n + 1) π₂ ω →
      letI := F.canonicalTopologicalData.topology
      haveI := localCoefficientGammaTopologicalRing F.canonicalTopologicalData
      letI := borel F.Carrier
      letI := borel F.Carrierˣ
      letI := borel (Langlands.GeneralLinear n F.Carrier)
      haveI : BorelSpace (Langlands.GeneralLinear n F.Carrier) := ⟨rfl⟩
      letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
      letI := borel (upperUnipotent n F.Carrier)
      haveI : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
      letI := borel (upperUnipotent (n + 1) F.Carrier)
      letI := borel (KirillovQuotient n F.Carrier)
      haveI : BorelSpace (KirillovQuotient n F.Carrier) := ⟨rfl⟩
      letI := borel (GeneralLinearGroup.integralSubgroup (Fin (n + 1))
        F.canonicalTopologicalData.Integers)
      letI := borel (Langlands.GeneralLinear ((n + 1) + (n + 1)) F.Carrier)
      ∃ d : EqualRankMeasureData F.canonicalTopologicalData.Integers n,
        IsEqualRankGeometricNormalized ψ F.canonicalTopologicalData.shahidiAbsoluteValue d ∧
        IsLocalCoefficientGammaComparison F ψ ν π₁ π₂ ω
          d.intertwining d.jacquet d.swappedJacquet)

end Langlands.Shahidi
