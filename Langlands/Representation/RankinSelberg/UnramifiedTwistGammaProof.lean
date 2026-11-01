import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaStatement
import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaCertificates
import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaAssembly
import Langlands.Representation.Twist.AlgebraProof

/-! # Complete symmetric unramified gamma spectral transport -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear Whittaker HarmonicAnalysis MeasureTheory

universe uF uV uW

namespace UnramifiedGammaTwist

section PairTransport

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (q : ℕ) (hq : 1 < q) (ψ : UnitaryAdditiveCharacter F)
  (abv : AbsoluteValue F ℝ) (ν : AdditiveHaarMeasure F)
  (χ₁ χ₂ : Fˣ →* ℂˣ) (u : ℂ)
  (h₁ : χ₁ (-1) = 1) (h₂ : χ₂ (-1) = 1)
  (hprod : ∀ x : Fˣ, (χ₁ x : ℂ) * (χ₂ x : ℂ) = (abv (x : F) : ℂ) ^ u)

include h₁ h₂ hprod in
/-- Complete ordered-pair transport under two determinant characters whose
product is the supplied absolute-value power. -/
theorem pair_factor
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {G : RationalFunctions} (h : IsPairGammaFactor q ψ abv ν π σ G) :
    IsPairGammaFactor q ψ abv ν
      (Langlands.twist (χ₁.comp determinant) π)
      (Langlands.twist (χ₂.comp determinant) σ)
      (rationalRescale (spectralShiftUnit q hq u) G) := by
  by_cases hnr : n < r
  · rw [isPairGammaFactor_of_lt hnr] at h ⊢
    exact unequal_factor_of_equation q ψ abv ν χ₁ χ₂
      (rationalRescale (spectralShiftUnit q hq u)) hnr π σ G
      (fun μ L L' hE =>
        unequal_equation ψ abv χ₁ χ₂ u h₁ h₂ hprod hnr q hq μ ν π σ L L' hE) h
  · by_cases hrn : r = n
    · subst r
      rw [isPairGammaFactor_self] at h ⊢
      exact equal_factor_of_equation q ψ abv ν χ₁ χ₂
        (rationalRescale (spectralShiftUnit q hq u)) π σ G
        (fun μ L L' hE =>
          equal_equation ψ abv χ₁ χ₂ u h₁ h₂ hprod q hq μ ν π σ L L' hE) h
    · exact False.elim ((not_isPairGammaFactor_of_lt (by omega)) h)

omit h₁ h₂ hprod in
/-- Specializing one character to the trivial character proves both twist
positions for the complete ordered-pair relation. -/
theorem pair_both (χ : Fˣ →* ℂˣ)
    (hχ : ∀ x : Fˣ, (χ x : ℂ) = (abv (x : F) : ℂ) ^ u)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {G : RationalFunctions} (h : IsPairGammaFactor q ψ abv ν π σ G) :
    IsPairGammaFactor q ψ abv ν π (Langlands.twist (χ.comp determinant) σ)
        (rationalRescale (spectralShiftUnit q hq u) G) ∧
      IsPairGammaFactor q ψ abv ν (Langlands.twist (χ.comp determinant) π) σ
        (rationalRescale (spectralShiftUnit q hq u) G) := by
  have hsign := character_neg_one abv χ u hχ
  constructor
  · simpa only [MonoidHom.one_comp, Langlands.twist_one] using
      pair_factor q hq ψ abv ν (1 : Fˣ →* ℂˣ) χ u (by simp) hsign
        (fun x => by simpa only [MonoidHom.one_apply, Units.val_one, one_mul] using hχ x)
        π σ h
  · simpa only [MonoidHom.one_comp, Langlands.twist_one] using
      pair_factor q hq ψ abv ν χ (1 : Fˣ →* ℂˣ) u hsign (by simp)
        (fun x => by simpa only [MonoidHom.one_apply, Units.val_one, mul_one] using hχ x)
        π σ h

end PairTransport

section PadicTransport

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (u : ℂ) (χ : F.Carrierˣ →* ℂˣ)
  (hχ : ∀ x : F.Carrierˣ,
    (χ x : ℂ) = (F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) : ℂ) ^ u)

include hχ in
/-- The canonical p-adic specialization keeps the field's actual residue
cardinality, normalized absolute value, additive character and Haar measure. -/
theorem padic_pair_both {r n : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    {G : RationalFunctions} (h : IsPadicPairGammaFactor F ψ ν π σ G) :
    IsPadicPairGammaFactor F ψ ν π (Langlands.twist (χ.comp determinant) σ)
        (rationalRescale (spectralShiftUnit F.canonicalTopologicalData.residueCardinality
          F.canonicalTopologicalData.residueCardinality_gt_one u) G) ∧
      IsPadicPairGammaFactor F ψ ν (Langlands.twist (χ.comp determinant) π) σ
        (rationalRescale (spectralShiftUnit F.canonicalTopologicalData.residueCardinality
          F.canonicalTopologicalData.residueCardinality_gt_one u) G) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  exact pair_both F.canonicalTopologicalData.residueCardinality
    F.canonicalTopologicalData.residueCardinality_gt_one ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData) ν u χ hχ π σ h

include hχ in
/-- Reading the larger rank first covers either rank order and exchanges the
two twist positions in the reversed branch. -/
theorem padic_symmetric_both {r n : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    {G : RationalFunctions} (h : IsPadicSymmetricGammaFactor F ψ ν π σ G) :
    IsPadicSymmetricGammaFactor F ψ ν π (Langlands.twist (χ.comp determinant) σ)
        (rationalRescale (spectralShiftUnit F.canonicalTopologicalData.residueCardinality
          F.canonicalTopologicalData.residueCardinality_gt_one u) G) ∧
      IsPadicSymmetricGammaFactor F ψ ν (Langlands.twist (χ.comp determinant) π) σ
        (rationalRescale (spectralShiftUnit F.canonicalTopologicalData.residueCardinality
          F.canonicalTopologicalData.residueCardinality_gt_one u) G) := by
  unfold IsPadicSymmetricGammaFactor at h ⊢
  split_ifs at h ⊢ with hnr
  · exact padic_pair_both F ψ ν u χ hχ π σ h
  · exact (padic_pair_both F ψ ν u χ hχ σ π h).symm

end PadicTransport

end UnramifiedGammaTwist

/-- Twisting either member by the supplied unramified determinant character
transports the complete symmetric gamma certificate by `X ↦ q^(-u) * X`. -/
theorem unramifiedTwistGamma : UnramifiedTwistGammaStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t V _ _ W _ _ π σ u χ hχ G h
  exact UnramifiedGammaTwist.padic_symmetric_both F ψ ν.val u χ hχ π σ h

end Langlands.RankinSelberg
