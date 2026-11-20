import Langlands.Representation.RankinSelberg.NormalizedZetaEvaluation
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.RankinSelberg.UnipotentQuotient

/-! # Pointwise nonvanishing of ordinary normalized p-adic tests -/

noncomputable section

set_option autoImplicit false

universe u uV uW

namespace Langlands.RankinSelberg

open HarmonicAnalysis MeasureTheory Polynomial QuotientIntegration Whittaker

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField
local instance : MeasurableSpace K.Carrier := borel K.Carrier
local instance : BorelSpace K.Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) K.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace
    (GeneralLinear.upperUnipotent (n + 1) K.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n K.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩

local notation "qK" => K.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue K.canonicalTopologicalData
local notation "μ" n => unipotentQuotientHaar K.Carrier n

variable (ψ : UnitaryAdditiveCharacter K.Carrier)
  {n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The equal-rank rational values for the canonical quotient measure. -/
def padicOrdinaryEqualZetaValues
    (π : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V)
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) W) : Set RationalFunctions :=
  equalRankZetaValues qK ψ abv (μ n) π σ

/-- The ordinary block-zero rational values for the canonical quotient measure. -/
def padicOrdinaryUnequalZetaValues (ν : AdditiveHaarMeasure K.Carrier) (k : ℕ)
    (π : Representation ℂ (GeneralLinear (n + (0 + k + 1) + 1) K.Carrier) V)
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) W) : Set RationalFunctions :=
  unequalRankZetaValues qK ψ abv 0 k (μ n) (rectangularMeasure ν 0 (n + 1)) π σ

section Equal

variable {K ψ} {ν : AdditiveHaarMeasure K.Carrier}
  {π : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V}
  {σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) W} {P : ℂ[X]}

/-- The equal-rank p-adic certificate normalizes the ordinary equal-rank values. -/
theorem IsPadicPairLPolynomial.normalizedGenerator_ordinaryEqual
    (hP : IsPadicPairLPolynomial K ψ ν π σ P) :
    IsNormalizedGenerator (padicOrdinaryEqualZetaValues K ψ π σ) P := by
  have hCompat := unipotentQuotientHaar_isCompatible K.Carrier n
  exact isPairLPolynomial_self.mp (hP.2 (μ n) hCompat)

/-- At any specified spectral parameter, there is an ordinary equal-rank local
test with a nonzero entire normalization. Its integral converges and matches the
normalized factor times the L-factor on a right half-plane. -/
theorem IsPadicPairLPolynomial.exists_normalizedTest_ordinaryEqual
    (hP : IsPadicPairLPolynomial K ψ ν π σ P) (s₀ : ℂ) :
    ∃ W₁ ∈ whittakerSet ψ n π, ∃ W₂ ∈ inverseWhittakerSet ψ n σ,
      ∃ Φ : SchwartzBruhat (Fin (n + 1) → K.Carrier), ∃ N : ℂ → ℂ,
      AnalyticOnNhd ℂ N Set.univ ∧ N s₀ ≠ 0 ∧
      ∃ b : ℝ, ∀ s : ℂ, b < s.re → EqualRankConverges ψ abv (μ n) W₁ W₂ Φ s ∧
        equalRankIntegral ψ abv (μ n) W₁ W₂ Φ s = N s * (P.eval (spectralPoint qK s))⁻¹ := by
  have hGen := hP.normalizedGenerator_ordinaryEqual
  have hq := K.canonicalTopologicalData.residueCardinality_gt_one
  obtain ⟨R, hR⟩ := hGen.exists_laurentEval_normalizedLaurent_ne_zero
    (spectralUnit (Nat.zero_lt_one.trans hq) s₀)
  obtain ⟨W₁, hW₁, W₂, hW₂, Φ, ⟨a, ha⟩, hf⟩ := R.property
  let aR := hGen.normalizedLaurent ⟨R, mem_zetaSpan R.property⟩
  obtain ⟨b, hb⟩ := hGen.exists_eq_spectralNormalization_mul_L hq ⟨R, mem_zetaSpan R.property⟩ hf
  exact ⟨W₁, hW₁, W₂, hW₂, Φ, fun s => laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) s) aR,
    fun s _ => analyticAt_laurentEval_spectralUnit hq aR s, hR, max a b, fun s hs =>
    ⟨ha s ((le_max_left a b).trans_lt hs), hb s ((le_max_right a b).trans_lt hs)⟩⟩

end Equal

section Unequal

variable {K ψ} {ν : AdditiveHaarMeasure K.Carrier} {k : ℕ}
  {π : Representation ℂ (GeneralLinear (n + (0 + k + 1) + 1) K.Carrier) V}
  {σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) W} {P : ℂ[X]}

/-- The unequal-rank p-adic certificate normalizes the ordinary block-zero values. -/
theorem IsPadicPairLPolynomial.normalizedGenerator_ordinaryUnequal
    (hP : IsPadicPairLPolynomial K ψ ν π σ P) :
    IsNormalizedGenerator (padicOrdinaryUnequalZetaValues K ψ ν k π σ) P := by
  have hCompat := unipotentQuotientHaar_isCompatible K.Carrier n
  have hlt : n < n + (0 + k + 1) := by omega
  exact (isPairLPolynomial_of_lt hlt).mp (hP.2 (μ n) hCompat) 0 k rfl

/-- At any specified spectral parameter, there is an ordinary unequal-rank local
test with a nonzero entire normalization. Its integral converges and matches the
normalized factor times the L-factor on a right half-plane. -/
theorem IsPadicPairLPolynomial.exists_normalizedTest_ordinaryUnequal
    (hP : IsPadicPairLPolynomial K ψ ν π σ P) (s₀ : ℂ) :
    ∃ W₁ ∈ whittakerSet ψ (n + (0 + k + 1)) π, ∃ W₂ ∈ inverseWhittakerSet ψ n σ,
      ∃ N : ℂ → ℂ, AnalyticOnNhd ℂ N Set.univ ∧ N s₀ ≠ 0 ∧
      ∃ b : ℝ, ∀ s : ℂ, b < s.re →
        UnequalRankConverges ψ abv 0 k (μ n) (rectangularMeasure ν 0 (n + 1)) W₁ W₂ s ∧
        unequalRankIntegral ψ abv 0 k (μ n) (rectangularMeasure ν 0 (n + 1)) W₁ W₂ s =
          N s * (P.eval (spectralPoint qK s))⁻¹ := by
  have hGen := hP.normalizedGenerator_ordinaryUnequal
  have hq := K.canonicalTopologicalData.residueCardinality_gt_one
  obtain ⟨R, hR⟩ := hGen.exists_laurentEval_normalizedLaurent_ne_zero
    (spectralUnit (Nat.zero_lt_one.trans hq) s₀)
  obtain ⟨W₁, hW₁, W₂, hW₂, ⟨a, ha⟩, hf⟩ := R.property
  let aR := hGen.normalizedLaurent ⟨R, mem_zetaSpan R.property⟩
  obtain ⟨b, hb⟩ := hGen.exists_eq_spectralNormalization_mul_L hq ⟨R, mem_zetaSpan R.property⟩ hf
  exact ⟨W₁, hW₁, W₂, hW₂, fun s => laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) s) aR,
    fun s _ => analyticAt_laurentEval_spectralUnit hq aR s, hR, max a b, fun s hs =>
    ⟨ha s ((le_max_left a b).trans_lt hs), hb s ((le_max_right a b).trans_lt hs)⟩⟩

end Unequal

end Langlands.RankinSelberg
