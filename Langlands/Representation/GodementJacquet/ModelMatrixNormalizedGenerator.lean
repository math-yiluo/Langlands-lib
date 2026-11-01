import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.GodementJacquet.WhittakerModelComparisonProof
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonProof
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof

/-!
# Normalized matrix generators on actual Whittaker coefficient models

Transport the published rank-one pair L-polynomial through `I₁ = I₃ = I₂`.
The carrier is the actual coefficient image, with no irreducibility premise.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

section CharacterGenerator

variable {K : Type uF} [Field K] [TopologicalSpace K] [MeasurableSpace K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  [MeasurableSpace (LeftUnipotentQuotient 0 K)]

omit [TopologicalSpace K] [MeasurableSpace K]
  [MeasurableSpace (LeftUnipotentQuotient 0 K)] in
private theorem rankCast_eq_comp_reindex {a b : ℕ} (h : a = b)
    (σ : Representation ℂ (Langlands.GeneralLinear (b + 1) K) V) :
    (h.symm ▸ σ) =
      σ.comp (reindex (finCongr (congrArg (· + 1) h))).toMonoidHom := by
  subst b
  apply MonoidHom.ext
  intro g
  congr 1

private theorem unequalRankZetaValuesAt_zero_eq_rankCast {m r : ℕ}
    (hr : r = 0 + (0 + m + 1)) (q : ℕ) (ψ : UnitaryAdditiveCharacter K)
    (abv : AbsoluteValue K ℝ) (μ : Measure (LeftUnipotentQuotient 0 K))
    (ν : AdditiveHaarMeasure K)
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) K) V)
    (χ : Kˣ →* ℂˣ) :
    unequalRankZetaValuesAt 0 m hr q ψ abv μ (rectangularMeasure ν 0 1)
        σ (rankOneCharacter χ) =
      unequalRankZetaValues q ψ abv 0 m μ (rectangularMeasure ν 0 1)
        (hr ▸ σ) (rankOneCharacter χ) := by
  subst r
  rfl

/-- The rank-one character family is the zero-row block of the full pair
family, with exactly its unit point mass. -/
theorem IsPairLPolynomial.isCharacterLPolynomial {q : ℕ}
    {ψ : UnitaryAdditiveCharacter K} {abv : AbsoluteValue K ℝ}
    {μ : Measure (LeftUnipotentQuotient 0 K)} {ν : AdditiveHaarMeasure K}
    {n : ℕ} {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V}
    {χ : Kˣ →* ℂˣ} {P : Polynomial ℂ}
    (hP : IsPairLPolynomial q ψ abv μ ν σ (rankOneCharacter χ) P) :
    IsCharacterLPolynomial q ψ abv μ χ σ P := by
  cases n with
  | zero => exact isPairLPolynomial_self.1 hP
  | succ m =>
    have hN : 0 + (0 + m + 1) = m + 1 := by omega
    have h := (isPairLPolynomial_of_lt (by omega)).1 hP 0 m hN.symm
    rw [unequalRankZetaValuesAt_zero_eq_rankCast, rectangularMeasure_zero_rows,
      rankCast_eq_comp_reindex hN] at h
    have he : (Matrix.instMeasurableSpace :
        MeasurableSpace (Matrix (Fin 0) (Fin (0 + 1)) K)) = ⊤ := by
      ext s
      exact iff_of_true Subsingleton.measurableSet (by trivial)
    rw [he] at h
    exact h

end CharacterGenerator

end Langlands.RankinSelberg

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration RankinSelberg

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)

local instance (ℓ : glFunctionals ψ n σ) :
    AddCommGroup (glCoefficientModel ψ n σ ℓ).toSubmodule :=
  (glCoefficientModel ψ n σ ℓ).toSubmodule.addCommGroup

/-- A character L-generator is the ordinary matrix generator on every
nonzero coefficient model, by the two published ideal comparisons. -/
theorem isMatrixNormalizedGenerator_model_of_character
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0)
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier 0)]
    (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))
    (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier 0) (unipotentHaar F.Carrier 0) μ)
    {P : Polynomial ℂ}
    (hP : IsCharacterLPolynomial F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ 1 σ P) :
    IsMatrixNormalizedGenerator F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) P := by
  have h13 := rankOneMatrixWhittakerComparison p F ψ n V σ hσ ℓ hℓ μ hμ
  have h23 := GodementJacquet.whittakerModelComparison p F ψ n σ hσ ℓ hℓ
  exact (isNormalizedGenerator_congr (h13.trans h23.symm) P).1 hP

/-- One full symmetric pair certificate supplies the ordinary normalized
matrix generator on every nonzero actual coefficient model. -/
theorem isMatrixNormalizedGenerator_model_of_pair
    (ν : AdditiveHaarMeasure F.Carrier)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    {P : Polynomial ℂ}
    (hP : IsPadicSymmetricLPolynomial F ψ ν σ (rankOneCharacter 1) P)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0) :
    IsMatrixNormalizedGenerator F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) P := by
  have hp := (isPadicSymmetricLPolynomial_of_le (Nat.zero_le n)).1 hP
  obtain ⟨⟨hinv, μ, hμ⟩, hgen⟩ := hp
  let := hinv
  exact isMatrixNormalizedGenerator_model_of_character F ψ σ hσ ℓ hℓ μ hμ
    ((hgen μ hμ).isCharacterLPolynomial)

/-- Existence retains the complete symmetric L-certificate and gives a
single polynomial for all nonzero functionals on the original carrier. -/
theorem exists_modelMatrixNormalizedGenerator
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ P : Polynomial ℂ,
      IsPadicSymmetricLPolynomial F ψ ν.val σ (rankOneCharacter 1) P ∧
      ∀ ℓ : glFunctionals ψ n σ, ℓ.val ≠ 0 →
        IsMatrixNormalizedGenerator F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
          (glModelRepresentation ψ n σ ℓ) P := by
  have h1 := rankOneCharacter_isOfWhittakerType p F ψ (1 : Quasicharacter F.Carrier)
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists p F ψ ν n 0 V ℂ σ
    (rankOneCharacter 1) hσ h1
  exact ⟨P, hP, fun ℓ hℓ => isMatrixNormalizedGenerator_model_of_pair F ψ σ ν.val hσ hP ℓ hℓ⟩

/-- The ordinary matrix polynomial chosen from the full pair L-existence
theorem. Its generator property concerns the actual coefficient models. -/
def modelMatrixLPolynomial
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) : Polynomial ℂ :=
  (exists_modelMatrixNormalizedGenerator F ψ σ ν hσ).choose

/-- The chosen polynomial retains the full supplied-measure pair certificate. -/
theorem modelMatrixLPolynomial_pair
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    IsPadicSymmetricLPolynomial F ψ ν.val σ (rankOneCharacter 1)
      (modelMatrixLPolynomial F ψ σ ν hσ) :=
  (exists_modelMatrixNormalizedGenerator F ψ σ ν hσ).choose_spec.1

/-- The chosen polynomial generates the ordinary matrix values on each
actual nonzero coefficient model of the original representation. -/
theorem modelMatrixLPolynomial_normalized
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0) :
    IsMatrixNormalizedGenerator F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ)
      (modelMatrixLPolynomial F ψ σ ν hσ) :=
  (exists_modelMatrixNormalizedGenerator F ψ σ ν hσ).choose_spec.2 ℓ hℓ

end Langlands.GodementJacquet.Padic
