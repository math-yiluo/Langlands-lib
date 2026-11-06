import Langlands.Representation.RankinSelberg.ComponentFactorComparisonStatement
import Langlands.Representation.RankinSelberg.GammaModelInclusion
import Langlands.Representation.RankinSelberg.LaurentDivisibilityProof
import Langlands.Representation.Whittaker.SubquotientCoefficientModelInclusionProof
import Langlands.Representation.Whittaker.MirabolicFunctionalTransfer
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-!
# Pair-factor comparison for actual irreducible components

Extend component functionals to the smooth ambient representations. Compare
gamma equations on the nested images and L-polynomials on the nested zeta spans.
-/

noncomputable section

namespace Langlands.Whittaker

universe uG uV uW

/-- Smoothness supplies character locality whenever the functional is nonzero.
The zero functional has the zero ambient coefficient model. -/
theorem exists_coefficientModel_extension_of_smooth_subquotient
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) (hN : Jacquet.Localization.IsLimitOfCompactSubgroups N)
    (θ : N →* ℂˣ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (U : Subrepresentation ρ)
    (q : U.toRepresentation.IntertwiningMap σ) (hq : Function.Surjective q)
    (ℓ : functionals N θ σ) :
    ∃ L : functionals N θ ρ,
      (ℓ.val ≠ 0 → L.val ≠ 0) ∧ coefficientModel σ ℓ ≤ coefficientModel ρ L := by
  by_cases hℓ : ℓ.val = 0
  · refine ⟨0, fun h => (h hℓ).elim, ?_⟩
    rintro f ⟨w, rfl⟩
    refine ⟨0, ?_⟩
    apply Subtype.ext
    funext g
    change (0 : Module.Dual ℂ V) (ρ g 0) = ℓ.val (σ g w)
    rw [hℓ]
    rfl
  · let i : U.toRepresentation.IntertwiningMap ρ :=
      { toLinearMap := U.toSubmodule.subtype
        isIntertwining' := fun _ => rfl }
    have hσ : IsSmooth σ :=
      isSmooth_of_surjective q hq (isSmooth_of_injective i Subtype.val_injective hρ)
    have hθ := character_isLocallyConstant_of_hasFunctional N θ σ hσ ⟨ℓ, hℓ⟩
    obtain ⟨L, -, hL, hM⟩ :=
      subquotientCoefficientModelInclusion G N hN θ hθ ρ σ hρ U q hq ℓ
    exact ⟨L, hL, hM⟩

end Langlands.Whittaker

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW uV₂ uW₂

/-- Extend a functional on an actual p-adic component, in the original
coefficient-function ambient space. -/
theorem IsIrreducibleComponent.exists_coefficientModel_extension
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
    {ξ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V₂}
    (hξ : letI := F.canonicalTopologicalData.topology; IsSmooth ξ)
    (hc : IsIrreducibleComponent ξ π)
    (θ : upperUnipotent (n + 1) F.Carrier →* ℂˣ) (ℓ : functionals _ θ π) :
    ∃ L : functionals _ θ ξ,
      (ℓ.val ≠ 0 → L.val ≠ 0) ∧ coefficientModel π ℓ ≤ coefficientModel ξ L := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  obtain ⟨-, U, q, hq⟩ := hc
  exact exists_coefficientModel_extension_of_smooth_subquotient _
    (upperUnipotent_isLimitOfCompactSubgroups F F.canonicalTopologicalData (n + 1))
    θ ξ π hξ U q hq ℓ

section PadicComparison

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  {ξ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
  {η : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂}

/-- Actual component coefficients belong to the ambient intrinsic Whittaker set. -/
theorem IsIrreducibleComponent.whittakerSet_subset
    (hξ : letI := F.canonicalTopologicalData.topology; IsSmooth ξ)
    (hc : IsIrreducibleComponent ξ π) :
    letI := F.canonicalTopologicalData.topology
    whittakerSet ψ r π ⊆ whittakerSet ψ r ξ := by
  let := F.canonicalTopologicalData.topology
  rintro f ⟨ℓ, hf⟩
  obtain ⟨L, -, hM⟩ :=
    hc.exists_coefficientModel_extension F hξ (standardCharacter ψ r) ℓ
  exact ⟨L, hM hf⟩

/-- The same inclusion for the inverse character on the second representation. -/
theorem IsIrreducibleComponent.inverseWhittakerSet_subset
    (hη : letI := F.canonicalTopologicalData.topology; IsSmooth η)
    (hc : IsIrreducibleComponent η σ) :
    letI := F.canonicalTopologicalData.topology
    inverseWhittakerSet ψ n σ ⊆ inverseWhittakerSet ψ n η := by
  let := F.canonicalTopologicalData.topology
  rintro f ⟨ℓ, hf⟩
  obtain ⟨L, -, hM⟩ :=
    hc.exists_coefficientModel_extension F hη (inverseStandardCharacter ψ n) ℓ
  exact ⟨L, hM hf⟩

/-- Existing ordered gamma factors coincide for actual components of smooth
ambient representations. The component certificate supplies nonzero functionals. -/
theorem IsPadicPairGammaFactor.eq_of_components
    (hξ : letI := F.canonicalTopologicalData.topology; IsSmooth ξ)
    (hη : letI := F.canonicalTopologicalData.topology; IsSmooth η)
    (hc : IsIrreducibleComponent ξ π) (hd : IsIrreducibleComponent η σ)
    {G H : RationalFunctions} (hG : IsPadicPairGammaFactor F ψ ν π σ G)
    (hH : IsPadicPairGammaFactor F ψ ν ξ η H) : G = H := by
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
  have h : IsPairGammaFactor F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) ν π σ G := hG
  have hnonzero : (∃ ℓ : glFunctionals ψ r π, ℓ.val ≠ 0) ∧
      (∃ ℓ' : glInverseFunctionals ψ n σ, ℓ'.val ≠ 0) := by
    by_cases hnr : n < r
    · rw [isPairGammaFactor_of_lt hnr] at h
      exact ⟨h.2.1, h.2.2.1⟩
    · by_cases hrn : r = n
      · subst r
        rw [isPairGammaFactor_self] at h
        exact ⟨h.2.1, h.2.2.1⟩
      · exact absurd h (not_isPairGammaFactor_of_lt (by omega))
  obtain ⟨⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩⟩ := hnonzero
  obtain ⟨L, hL, hM⟩ :=
    hc.exists_coefficientModel_extension F hξ (standardCharacter ψ r) ℓ
  obtain ⟨L', hL', hM'⟩ :=
    hd.exists_coefficientModel_extension F hη (inverseStandardCharacter ψ n) ℓ'
  exact IsPairGammaFactor.eq_of_model_le
    (PadicField.TopologicalData.residueCardinality_gt_one _) hℓ hℓ'
    (hL hℓ) (hL' hℓ') hM hM' h hH

/-- Inclusion of actual component coefficient functions gives inclusion of zeta
spans, hence divisibility of the normalized L-polynomials. -/
theorem IsPadicPairLPolynomial.dvd_of_components
    (hξ : letI := F.canonicalTopologicalData.topology; IsSmooth ξ)
    (hη : letI := F.canonicalTopologicalData.topology; IsSmooth η)
    (hc : IsIrreducibleComponent ξ π) (hd : IsIrreducibleComponent η σ)
    {P A : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν π σ P)
    (hA : IsPadicPairLPolynomial F ψ ν ξ η A) : P ∣ A := by
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
  obtain ⟨⟨hinv, μ, hμ⟩, hall⟩ := hP
  have hPμ := @hall hinv μ hμ
  have hAμ := @hA.2 hinv μ hμ
  by_cases hnr : n < r
  · rw [isPairLPolynomial_of_lt hnr] at hPμ hAμ
    obtain ⟨k, hr⟩ : ∃ k : ℕ, r = n + (0 + k + 1) := ⟨r - n - 1, by omega⟩
    refine (normalizedGeneratorSpanDivisibility _ _ _ _
      (hPμ 0 k hr) (hAμ 0 k hr)).mp ?_
    apply Submodule.span_mono
    subst r
    exact unequalRankValuesOf_mono _ _ _ 0 k μ _
      (hc.whittakerSet_subset hξ) (hd.inverseWhittakerSet_subset hη)
  · by_cases hrn : r = n
    · subst r
      rw [isPairLPolynomial_self] at hPμ hAμ
      refine (normalizedGeneratorSpanDivisibility _ _ _ _ hPμ hAμ).mp ?_
      exact Submodule.span_mono (equalRankValuesOf_mono _ _ _ μ
        (hc.whittakerSet_subset hξ) (hd.inverseWhittakerSet_subset hη))
    · exact absurd hPμ (not_isPairLPolynomial_of_lt (by omega))

end PadicComparison

/-- Pair-factor comparison for actual components of smooth ambient
representations, with both rank orders and independent carrier universes. -/
theorem componentFactorComparison :
    ComponentFactorComparisonStatement.{uF, uV, uW, uV₂, uW₂} := by
  intro p _ F ψ ν r n V _ _ W _ _ V₂ _ _ W₂ _ _ π σ ξ η hξ hη hc hd
  by_cases hnr : n ≤ r
  · constructor
    · intro G H hG hH
      rw [isPadicSymmetricGammaFactor_of_le hnr] at hG hH
      exact hG.eq_of_components hξ hη hc hd hH
    · intro P A hP hA
      rw [isPadicSymmetricLPolynomial_of_le hnr] at hP hA
      exact hP.dvd_of_components hξ hη hc hd hA
  · have hrn : r < n := Nat.lt_of_not_ge hnr
    constructor
    · intro G H hG hH
      rw [isPadicSymmetricGammaFactor_of_lt hrn] at hG hH
      exact hG.eq_of_components hη hξ hd hc hH
    · intro P A hP hA
      rw [isPadicSymmetricLPolynomial_of_lt hrn] at hP hA
      exact hP.dvd_of_components hη hξ hd hc hA

end Langlands.RankinSelberg
