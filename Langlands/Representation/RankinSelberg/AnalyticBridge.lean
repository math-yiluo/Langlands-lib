import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# The JPSS analytic statements and the intrinsic zeta-value sets

For a representation of Whittaker type with a specified nonzero functional, the
intrinsic zeta-value sets of `LocalFactor` coincide with the per-functional rational
values of `AnalyticStatement` once every model integral converges on a right half-plane.
Consequently each analytic conclusion, and each p-adic analytic statement, supplies the
existence proof required by the conditional L-factors. Nothing analytic is proved here.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Polynomial QuotientIntegration
open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis

universe uF uV uW

section MultiplicityOne

/-- In a complex vector space isomorphic to `ℂ`, every vector is a multiple of any
nonzero vector. -/
theorem exists_eq_smul_of_linearEquiv {M : Type*} [AddCommGroup M] [Module ℂ M]
    (e : M ≃ₗ[ℂ] ℂ) {x₀ : M} (hx₀ : x₀ ≠ 0) (x : M) : ∃ c : ℂ, x = c • x₀ := by
  have h : e x₀ ≠ 0 := (LinearEquiv.map_ne_zero_iff e).2 hx₀
  refine ⟨e x / e x₀, e.injective ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h]

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {n : ℕ} {θ : upperUnipotent (n + 1) F →* ℂˣ}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}

/-- A representation of Whittaker type has a nonzero functional. -/
theorem IsOfWhittakerType.exists_ne_zero (h : IsOfWhittakerType n θ π) :
    ∃ ℓ : functionals (upperUnipotent (n + 1) F) θ π, ℓ.val ≠ 0 := by
  obtain ⟨e⟩ := h.2.2
  refine ⟨e.symm 1, fun h0 => ?_⟩
  have h1 : e (e.symm 1) = e 0 := congrArg e (Subtype.ext h0)
  rw [LinearEquiv.apply_symm_apply, map_zero] at h1
  exact one_ne_zero h1

/-- For a representation of Whittaker type, every functional is a multiple of a
nonzero one. -/
theorem IsOfWhittakerType.eq_smul (h : IsOfWhittakerType n θ π)
    {ℓ₀ : functionals (upperUnipotent (n + 1) F) θ π} (hℓ₀ : ℓ₀.val ≠ 0)
    (ℓ : functionals (upperUnipotent (n + 1) F) θ π) : ∃ c : ℂ, ℓ = c • ℓ₀ := by
  obtain ⟨e⟩ := h.2.2
  exact exists_eq_smul_of_linearEquiv e (fun h0 => hℓ₀ (congrArg Subtype.val h0)) ℓ

end MultiplicityOne

section EqualRank

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

/-- The convergent values of two coefficient models are among their rational values. -/
theorem equalRankValuesOf_coefficientModel_subset
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) :
    equalRankValuesOf q ψ abv μ (coefficientModel π ℓ).toSubmodule
        (coefficientModel σ ℓ').toSubmodule ⊆
      equalRankRationalValues q ψ abv μ π σ ℓ ℓ' := by
  rintro R ⟨f, hf, f', hf', Φ, -, hR⟩
  exact ⟨⟨f, hf⟩, ⟨f', hf'⟩, Φ, hR⟩

/-- If every model integral converges on a right half-plane, the convergent values and
the rational values of two coefficient models coincide. -/
theorem equalRankValuesOf_coefficientModel_eq
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
    (hconv : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∀ f' : (coefficientModel σ ℓ').toSubmodule,
      ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
        ∃ a : ℝ, ∀ s : ℂ, a < s.re → EqualRankConverges ψ abv μ f.val f'.val Φ s) :
    equalRankValuesOf q ψ abv μ (coefficientModel π ℓ).toSubmodule
        (coefficientModel σ ℓ').toSubmodule =
      equalRankRationalValues q ψ abv μ π σ ℓ ℓ' := by
  refine Set.Subset.antisymm (equalRankValuesOf_coefficientModel_subset q ψ abv μ ℓ ℓ') ?_
  rintro R ⟨f, f', Φ, hR⟩
  exact ⟨f.val, f.property, f'.val, f'.property, Φ, hconv f f' Φ, hR⟩

/-- For a pair of Whittaker type with nonzero functionals whose model integrals all
converge on right half-planes, the intrinsic zeta values are the rational values of
the models of these functionals. -/
theorem equalRankZetaValues_eq_rationalValues
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hconv : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∀ f' : (coefficientModel σ ℓ').toSubmodule,
      ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
        ∃ a : ℝ, ∀ s : ℂ, a < s.re → EqualRankConverges ψ abv μ f.val f'.val Φ s) :
    equalRankZetaValues q ψ abv μ π σ = equalRankRationalValues q ψ abv μ π σ ℓ ℓ' := by
  rw [equalRankZetaValues_eq_model q ψ abv μ ℓ ℓ' (hπ.eq_smul hℓ) (hσ.eq_smul hℓ')]
  exact equalRankValuesOf_coefficientModel_eq q ψ abv μ ℓ ℓ' hconv

variable {q ψ abv μ}

/-- Under the equal-rank analytic conclusion, the zeta values are the rational values. -/
theorem EqualRankAnalyticConclusion.zetaValues_eq
    {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
    (h : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    equalRankZetaValues q ψ abv μ π σ = equalRankRationalValues q ψ abv μ π σ ℓ ℓ' :=
  equalRankZetaValues_eq_rationalValues q ψ abv μ hπ hσ hℓ hℓ' h.1

/-- The equal-rank analytic conclusion gives the zeta values a common denominator. -/
theorem EqualRankAnalyticConclusion.hasCommonDenominator
    {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
    (h : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    HasCommonDenominator (equalRankZetaValues q ψ abv μ π σ) := by
  rw [h.zetaValues_eq hπ hσ hℓ hℓ']
  exact h.2.2.1

/-- The equal-rank analytic conclusion supplies the existence proof required by
`equalRankLFactor`. -/
theorem EqualRankAnalyticConclusion.normalizedGeneratorExists
    {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
    (h : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    NormalizedGeneratorExists (equalRankZetaValues q ψ abv μ π σ) := by
  rw [h.zetaValues_eq hπ hσ hℓ hℓ']
  exact h.2.2.2

/-- Under the equal-rank analytic conclusion, the L-polynomial of the pair is the
normalized generator of the rational values of the specified models. -/
theorem EqualRankAnalyticConclusion.isEqualRankLPolynomial_iff
    {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
    (h : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) (P : ℂ[X]) :
    IsEqualRankLPolynomial q ψ abv μ π σ P ↔
      IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P := by
  rw [IsEqualRankLPolynomial, h.zetaValues_eq hπ hσ hℓ hℓ']

end EqualRank

section UnequalRank

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  {n : ℕ} (j k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
  (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
  {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

/-- The unequal-rank analogue of `equalRankValuesOf_coefficientModel_subset`. -/
theorem unequalRankValuesOf_coefficientModel_subset
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ) :
    unequalRankValuesOf q ψ abv j k μ ν (coefficientModel π ℓ).toSubmodule
        (coefficientModel σ ℓ').toSubmodule ⊆
      unequalRankRationalValues j k q ψ abv μ ν π σ ℓ ℓ' := by
  rintro R ⟨f, hf, f', hf', -, hR⟩
  exact ⟨⟨f, hf⟩, ⟨f', hf'⟩, hR⟩

/-- The unequal-rank analogue of `equalRankValuesOf_coefficientModel_eq`. -/
theorem unequalRankValuesOf_coefficientModel_eq
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ)
    (hconv : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∀ f' : (coefficientModel σ ℓ').toSubmodule,
        ∃ a : ℝ, ∀ s : ℂ, a < s.re → UnequalRankConverges ψ abv j k μ ν f.val f'.val s) :
    unequalRankValuesOf q ψ abv j k μ ν (coefficientModel π ℓ).toSubmodule
        (coefficientModel σ ℓ').toSubmodule =
      unequalRankRationalValues j k q ψ abv μ ν π σ ℓ ℓ' := by
  refine Set.Subset.antisymm
    (unequalRankValuesOf_coefficientModel_subset q ψ abv j k μ ν ℓ ℓ') ?_
  rintro R ⟨f, f', hR⟩
  exact ⟨f.val, f.property, f'.val, f'.property, hconv f f', hR⟩

/-- The unequal-rank analogue of `equalRankZetaValues_eq_rationalValues`. -/
theorem unequalRankZetaValues_eq_rationalValues
    (hπ : IsOfWhittakerType (n + (j + k + 1)) (standardCharacter ψ (n + (j + k + 1))) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    {ℓ : glFunctionals ψ (n + (j + k + 1)) π} {ℓ' : glInverseFunctionals ψ n σ}
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hconv : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∀ f' : (coefficientModel σ ℓ').toSubmodule,
        ∃ a : ℝ, ∀ s : ℂ, a < s.re → UnequalRankConverges ψ abv j k μ ν f.val f'.val s) :
    unequalRankZetaValues q ψ abv j k μ ν π σ =
      unequalRankRationalValues j k q ψ abv μ ν π σ ℓ ℓ' := by
  rw [unequalRankZetaValues_eq_model q ψ abv j k μ ν ℓ ℓ' (hπ.eq_smul hℓ) (hσ.eq_smul hℓ')]
  exact unequalRankValuesOf_coefficientModel_eq q ψ abv j k μ ν ℓ ℓ' hconv

variable {q ψ abv j k μ ν}

/-- Under the unequal-rank analytic conclusion, the zeta values are the rational values. -/
theorem UnequalRankAnalyticConclusion.zetaValues_eq
    {ℓ : glFunctionals ψ (n + (j + k + 1)) π} {ℓ' : glInverseFunctionals ψ n σ}
    (h : UnequalRankAnalyticConclusion j k q ψ abv μ ν π σ ℓ ℓ')
    (hπ : IsOfWhittakerType (n + (j + k + 1)) (standardCharacter ψ (n + (j + k + 1))) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    unequalRankZetaValues q ψ abv j k μ ν π σ =
      unequalRankRationalValues j k q ψ abv μ ν π σ ℓ ℓ' :=
  unequalRankZetaValues_eq_rationalValues q ψ abv j k μ ν hπ hσ hℓ hℓ' h.1

/-- The unequal-rank analytic conclusion gives the zeta values a common denominator. -/
theorem UnequalRankAnalyticConclusion.hasCommonDenominator
    {ℓ : glFunctionals ψ (n + (j + k + 1)) π} {ℓ' : glInverseFunctionals ψ n σ}
    (h : UnequalRankAnalyticConclusion j k q ψ abv μ ν π σ ℓ ℓ')
    (hπ : IsOfWhittakerType (n + (j + k + 1)) (standardCharacter ψ (n + (j + k + 1))) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    HasCommonDenominator (unequalRankZetaValues q ψ abv j k μ ν π σ) := by
  rw [h.zetaValues_eq hπ hσ hℓ hℓ']
  exact h.2.2.1

/-- The unequal-rank analytic conclusion supplies the existence proof required by
`unequalRankLFactor`. -/
theorem UnequalRankAnalyticConclusion.normalizedGeneratorExists
    {ℓ : glFunctionals ψ (n + (j + k + 1)) π} {ℓ' : glInverseFunctionals ψ n σ}
    (h : UnequalRankAnalyticConclusion j k q ψ abv μ ν π σ ℓ ℓ')
    (hπ : IsOfWhittakerType (n + (j + k + 1)) (standardCharacter ψ (n + (j + k + 1))) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    NormalizedGeneratorExists (unequalRankZetaValues q ψ abv j k μ ν π σ) := by
  rw [h.zetaValues_eq hπ hσ hℓ hℓ']
  exact h.2.2.2

/-- Under the unequal-rank analytic conclusion, the L-polynomial for the block `j, k`
is the normalized generator of the rational values of the specified models. -/
theorem UnequalRankAnalyticConclusion.isUnequalRankLPolynomial_iff
    {ℓ : glFunctionals ψ (n + (j + k + 1)) π} {ℓ' : glInverseFunctionals ψ n σ}
    (h : UnequalRankAnalyticConclusion j k q ψ abv μ ν π σ ℓ ℓ')
    (hπ : IsOfWhittakerType (n + (j + k + 1)) (standardCharacter ψ (n + (j + k + 1))) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) (P : ℂ[X]) :
    IsUnequalRankLPolynomial q ψ abv j k μ ν π σ P ↔
      IsNormalizedGenerator (unequalRankRationalValues j k q ψ abv μ ν π σ ℓ ℓ') P := by
  rw [IsUnequalRankLPolynomial, h.zetaValues_eq hπ hσ hℓ hℓ']

end UnequalRank

section PadicStatements

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The p-adic equal-rank analytic statement supplies, for every pair of Whittaker
type, the existence proof required by `equalRankLFactor`, with the residue cardinality,
the normalized absolute value and any compatible quotient measure. -/
theorem EqualRankAnalyticStatement.normalizedGeneratorExists {n : ℕ}
    (h : EqualRankAnalyticStatement.{uF, uV, uW} F T n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
        IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
        ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
        ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
          IsOfWhittakerType n (standardCharacter ψ n) π →
          IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
          NormalizedGeneratorExists (equalRankZetaValues T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ π σ) := by
  let _ : TopologicalSpace F.Carrier := T.topology
  let _ : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  intro ψ _ μ hμ V _ _ W _ _ π σ hπ hσ
  obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
  obtain ⟨ℓ', hℓ'⟩ := hσ.exists_ne_zero
  exact (h ψ μ hμ V W π σ hπ hσ ℓ ℓ' hℓ hℓ').normalizedGeneratorExists hπ hσ hℓ hℓ'

/-- The p-adic unequal-rank analytic statement supplies, for every pair of Whittaker
type, the existence proof required by `unequalRankLFactor` for the block `j, k`, with
the rectangular product of any additive Haar measure. -/
theorem UnequalRankAnalyticStatement.normalizedGeneratorExists {n j k : ℕ}
    (h : UnequalRankAnalyticStatement.{uF, uV, uW} F T n j k) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
        IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
        ∀ ν : AdditiveHaarMeasure F.Carrier,
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
        ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
        ∀ (π : Representation ℂ
            (Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier) V)
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
          IsOfWhittakerType (n + (j + k + 1)) (standardCharacter ψ (n + (j + k + 1))) π →
          IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
          NormalizedGeneratorExists (unequalRankZetaValues T.residueCardinality ψ
            (normalizedAbsoluteValue T) j k μ (rectangularMeasure ν j (n + 1)) π σ) := by
  let _ : TopologicalSpace F.Carrier := T.topology
  let _ : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  let _ : MeasurableSpace F.Carrier := borel _
  intro ψ _ μ hμ ν V _ _ W _ _ π σ hπ hσ
  obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
  obtain ⟨ℓ', hℓ'⟩ := hσ.exists_ne_zero
  exact (h ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ').normalizedGeneratorExists hπ hσ hℓ hℓ'

end PadicStatements

end Langlands.RankinSelberg
