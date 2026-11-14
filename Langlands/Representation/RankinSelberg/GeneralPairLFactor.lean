import Langlands.Representation.RankinSelberg.GeneralPairGamma

/-!
# L-polynomials of pairs over general nonarchimedean local fields

The L-polynomial analogue of `GeneralPairGamma`: the published pair relation
`IsPairLPolynomial` with the Borel measurable structures, quantified over every
compatible quotient measure, and its larger-rank-first extension. These are the
general-field forms of `IsPadicPairLPolynomial` and `IsPadicSymmetricLPolynomial`.
No polynomial is selected and no existence is assumed.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW uV₂ uW₂

section General

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- `P` is the L-polynomial of the pair `(π, σ)`, `π` on `GL_(r+1)(F)` and `σ` on
`GL_(n+1)(F)`, over a general nonarchimedean local field with the Borel structures:
a compatible quotient measure exists, and for every compatible quotient measure `μ`,
`P` is the published pair L-polynomial `IsPairLPolynomial q ψ abv μ ν π σ P`. The
residue cardinality `q`, absolute value `abv` and additive Haar measure `ν` are
explicit inputs. -/
def IsGeneralPairLPolynomial (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ν : letI := borel F; AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (P : ℂ[X]) : Prop :=
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  (∃ _ : Measure.IsMulRightInvariant (unipotentHaar F n),
    CompatibleMeasureExists (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n)) ∧
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) μ →
      IsPairLPolynomial q ψ abv μ ν π σ P

/-- `L(s, π × σ) = 1 / P(q^(-s))` for either positive-rank order, with the larger
rank first; equal ranks retain the given order. This is the convention of JPSS
(2.12) for L-factors. -/
def IsGeneralSymmetricLPolynomial (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ν : letI := borel F; AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (P : ℂ[X]) : Prop :=
  if n ≤ r then IsGeneralPairLPolynomial q ψ abv ν π σ P
  else IsGeneralPairLPolynomial q ψ abv ν σ π P

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : letI := borel F; AdditiveHaarMeasure F}
  {r n : ℕ} {V : Type uV} {W : Type uW} {V₂ : Type uV₂} {W₂ : Type uW₂}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
  {P P' : ℂ[X]}

/-- Uniqueness is inherited from the published pair relation at one compatible
quotient measure. -/
theorem IsGeneralPairLPolynomial.unique (h : IsGeneralPairLPolynomial q ψ abv ν π σ P)
    (h' : IsGeneralPairLPolynomial q ψ abv ν π σ P') : P = P' := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  obtain ⟨⟨_, μ, hμ⟩, hP⟩ := h
  exact (hP μ hμ).unique (h'.2 μ hμ)

/-- Representation equivalences may change both carrier universes. -/
theorem IsGeneralPairLPolynomial.congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    IsGeneralPairLPolynomial q ψ abv ν π σ P ↔
      IsGeneralPairLPolynomial q ψ abv ν π₂ σ₂ P := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun μ => ?_)
  exact imp_congr_right fun _ => isPairLPolynomial_congr_equiv φ φ'

theorem isGeneralSymmetricLPolynomial_of_le (h : n ≤ r) :
    IsGeneralSymmetricLPolynomial q ψ abv ν π σ P ↔
      IsGeneralPairLPolynomial q ψ abv ν π σ P := by
  simp only [IsGeneralSymmetricLPolynomial, h, ↓reduceIte]

theorem isGeneralSymmetricLPolynomial_of_lt (h : r < n) :
    IsGeneralSymmetricLPolynomial q ψ abv ν π σ P ↔
      IsGeneralPairLPolynomial q ψ abv ν σ π P := by
  simp only [IsGeneralSymmetricLPolynomial, Nat.not_le.mpr h, ↓reduceIte]

/-- The larger-rank-first relation has at most one polynomial witness. -/
theorem IsGeneralSymmetricLPolynomial.unique
    (h : IsGeneralSymmetricLPolynomial q ψ abv ν π σ P)
    (h' : IsGeneralSymmetricLPolynomial q ψ abv ν π σ P') : P = P' := by
  unfold IsGeneralSymmetricLPolynomial at h h'
  split_ifs at h h'
  · exact h.unique h'
  · exact h.unique h'

theorem IsGeneralSymmetricLPolynomial.congr_equiv (φ : π.Equiv π₂)
    (φ' : σ.Equiv σ₂) :
    IsGeneralSymmetricLPolynomial q ψ abv ν π σ P ↔
      IsGeneralSymmetricLPolynomial q ψ abv ν π₂ σ₂ P := by
  unfold IsGeneralSymmetricLPolynomial
  split_ifs
  · exact IsGeneralPairLPolynomial.congr_equiv φ φ'
  · exact IsGeneralPairLPolynomial.congr_equiv φ' φ

end General

section Padic

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p)
  (ψ : letI := K.canonicalTopologicalData.topology; UnitaryAdditiveCharacter K.Carrier)
  (ν : letI := K.canonicalTopologicalData.topology; letI := borel K.Carrier
    AdditiveHaarMeasure K.Carrier)
  {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) W)
  (P : ℂ[X])

/-- At the canonical p-adic data, the general pair relation is the published
p-adic relation, by definitional equality. -/
theorem isGeneralPairLPolynomial_padic :
    (letI := K.canonicalTopologicalData.topology
     letI := K.canonicalTopologicalData.valuativeRel
     letI := K.canonicalTopologicalData.localField
     IsGeneralPairLPolynomial K.canonicalTopologicalData.residueCardinality ψ
       (normalizedAbsoluteValue K.canonicalTopologicalData) ν π σ P) ↔
      IsPadicPairLPolynomial K ψ ν π σ P :=
  Iff.rfl

/-- Both rank branches specialize to the published p-adic symmetric relation. -/
theorem isGeneralSymmetricLPolynomial_padic :
    (letI := K.canonicalTopologicalData.topology
     letI := K.canonicalTopologicalData.valuativeRel
     letI := K.canonicalTopologicalData.localField
     IsGeneralSymmetricLPolynomial K.canonicalTopologicalData.residueCardinality ψ
       (normalizedAbsoluteValue K.canonicalTopologicalData) ν π σ P) ↔
      IsPadicSymmetricLPolynomial K ψ ν π σ P :=
  Iff.rfl

end Padic

end Langlands.RankinSelberg
