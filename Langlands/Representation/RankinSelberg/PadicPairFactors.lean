import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.RankinSelberg.LocalConverseStatement
import Langlands.Representation.RankinSelberg.PairLFactor

/-!
# Pair factors of actual p-adic representations

Uniqueness and equivalence invariance of the epsilon-factor relation
`IsPadicPairEpsilonFactor` of a p-adic field with its canonical topological
data; the L-polynomial relation `IsPadicPairLPolynomial` over the published
`IsPairLPolynomial`, quantified over every compatible quotient measure; and the
gamma, epsilon and L relations `IsPadicSymmetricGammaFactor`,
`IsPadicSymmetricEpsilonFactor`, `IsPadicSymmetricLPolynomial` for pairs of
either rank order, with the
convention of JPSS (2.12) (printed page 403) that the pair is read with the
larger rank first.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW uV₂ uW₂

variable {p : ℕ} [Fact p.Prime]

/-- The p-adic epsilon factor of a pair is unique. -/
theorem IsPadicPairEpsilonFactor.unique {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {e e' : ℂˣ × ℤ} (h : IsPadicPairEpsilonFactor F ψ ν π σ e)
    (h' : IsPadicPairEpsilonFactor F ψ ν π σ e') : e = e' := by
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
  exact IsPairEpsilonFactor.unique (PadicField.TopologicalData.residueCardinality_gt_one _) h h'

/-- The p-adic epsilon-factor relation is invariant under representation
equivalences. -/
theorem IsPadicPairEpsilonFactor.congr_equiv {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {r n : ℕ} {V : Type uV} {W : Type uW} {V₂ : Type uV₂} {W₂ : Type uW₂}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) {e : ℂˣ × ℤ} :
    IsPadicPairEpsilonFactor F ψ ν π σ e ↔ IsPadicPairEpsilonFactor F ψ ν π₂ σ₂ e := by
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
  exact IsPairEpsilonFactor.congr_equiv φ φ'

/-- `P` is the L-polynomial of the pair `(π, σ)` of actual representations of
`GL_(r+1)(F)` and `GL_(n+1)(F)` over a p-adic field with its canonical
topological data: a compatible quotient measure exists, and for every compatible
quotient measure `P` is the published pair L-polynomial `IsPairLPolynomial`,
with `q` the residue cardinality and the normalized absolute value. -/
def IsPadicPairLPolynomial (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (P : ℂ[X]) : Prop :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  (∃ _ : Measure.IsMulRightInvariant (unipotentHaar F.Carrier n),
    CompatibleMeasureExists (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n)) ∧
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
        (unipotentHaar F.Carrier n) μ →
      IsPairLPolynomial F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μ ν π σ P

/-- The p-adic L-polynomial of a pair is unique. -/
theorem IsPadicPairLPolynomial.unique {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {P P' : ℂ[X]} (h : IsPadicPairLPolynomial F ψ ν π σ P)
    (h' : IsPadicPairLPolynomial F ψ ν π σ P') : P = P' := by
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
  obtain ⟨⟨_, μ, hμ⟩, hP⟩ := h
  exact (hP μ hμ).unique (h'.2 μ hμ)


/-- The p-adic L-polynomial relation is invariant under representation
equivalences. -/
theorem IsPadicPairLPolynomial.congr_equiv {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {r n : ℕ} {V : Type uV} {W : Type uW} {V₂ : Type uV₂} {W₂ : Type uW₂}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) {P : ℂ[X]} :
    IsPadicPairLPolynomial F ψ ν π σ P ↔ IsPadicPairLPolynomial F ψ ν π₂ σ₂ P := by
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
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun μ => ?_)
  exact imp_congr_right fun _ => isPairLPolynomial_congr_equiv φ φ'

/-- `γ(s, π × σ, ψ) = G(q^(-s))` for actual representations `π` of `GL_(r+1)(F)`
and `σ` of `GL_(n+1)(F)` of either rank order. When `n ≤ r` it is the pair
relation `IsPadicPairGammaFactor` for `(π, σ)`; when `r < n` it is the pair
relation for `(σ, π)`. This is the convention of JPSS (2.12), printed page 403:
a pair is read with the larger rank first. -/
def IsPadicSymmetricGammaFactor (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (G : RationalFunctions) : Prop :=
  if n ≤ r then IsPadicPairGammaFactor F ψ ν π σ G else IsPadicPairGammaFactor F ψ ν σ π G

/-- `ε(s, π × σ, ψ) = c q^(-ms)`, `e = (c, m)`, for actual representations `π`
of `GL_(r+1)(F)` and `σ` of `GL_(n+1)(F)` of either rank order, with the same
convention as `IsPadicSymmetricGammaFactor`. -/
def IsPadicSymmetricEpsilonFactor (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (e : ℂˣ × ℤ) : Prop :=
  if n ≤ r then IsPadicPairEpsilonFactor F ψ ν π σ e else IsPadicPairEpsilonFactor F ψ ν σ π e

/-- `L(s, π × σ) = 1 / P(q^(-s))` for actual representations `π` of
`GL_(r+1)(F)` and `σ` of `GL_(n+1)(F)` of either rank order, with the same
convention as `IsPadicSymmetricGammaFactor`. -/
def IsPadicSymmetricLPolynomial (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (P : ℂ[X]) : Prop :=
  if n ≤ r then IsPadicPairLPolynomial F ψ ν π σ P else IsPadicPairLPolynomial F ψ ν σ π P

section Symmetric

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r n : ℕ} {V : Type uV} {W : Type uW} {V₂ : Type uV₂} {W₂ : Type uW₂}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂}

theorem isPadicSymmetricGammaFactor_of_le (h : n ≤ r) {G : RationalFunctions} :
    IsPadicSymmetricGammaFactor F ψ ν π σ G ↔ IsPadicPairGammaFactor F ψ ν π σ G := by
  simp only [IsPadicSymmetricGammaFactor, h, ↓reduceIte]

theorem isPadicSymmetricGammaFactor_of_lt (h : r < n) {G : RationalFunctions} :
    IsPadicSymmetricGammaFactor F ψ ν π σ G ↔ IsPadicPairGammaFactor F ψ ν σ π G := by
  simp only [IsPadicSymmetricGammaFactor, Nat.not_le.mpr h, ↓reduceIte]

/-- The gamma factor of a pair of either rank order is unique. -/
theorem IsPadicSymmetricGammaFactor.unique {G G' : RationalFunctions}
    (h : IsPadicSymmetricGammaFactor F ψ ν π σ G)
    (h' : IsPadicSymmetricGammaFactor F ψ ν π σ G') : G = G' := by
  unfold IsPadicSymmetricGammaFactor at h h'
  split_ifs at h h'
  · exact h.unique h'
  · exact h.unique h'

/-- The gamma relation for either rank order is invariant under representation
equivalences. -/
theorem IsPadicSymmetricGammaFactor.congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    {G : RationalFunctions} :
    IsPadicSymmetricGammaFactor F ψ ν π σ G ↔ IsPadicSymmetricGammaFactor F ψ ν π₂ σ₂ G := by
  unfold IsPadicSymmetricGammaFactor
  split_ifs
  · exact IsPadicPairGammaFactor.congr_equiv φ φ'
  · exact IsPadicPairGammaFactor.congr_equiv φ' φ

theorem isPadicSymmetricEpsilonFactor_of_le (h : n ≤ r) {e : ℂˣ × ℤ} :
    IsPadicSymmetricEpsilonFactor F ψ ν π σ e ↔ IsPadicPairEpsilonFactor F ψ ν π σ e := by
  simp only [IsPadicSymmetricEpsilonFactor, h, ↓reduceIte]

theorem isPadicSymmetricEpsilonFactor_of_lt (h : r < n) {e : ℂˣ × ℤ} :
    IsPadicSymmetricEpsilonFactor F ψ ν π σ e ↔ IsPadicPairEpsilonFactor F ψ ν σ π e := by
  simp only [IsPadicSymmetricEpsilonFactor, Nat.not_le.mpr h, ↓reduceIte]

/-- The epsilon factor of a pair of either rank order is unique. -/
theorem IsPadicSymmetricEpsilonFactor.unique {e e' : ℂˣ × ℤ}
    (h : IsPadicSymmetricEpsilonFactor F ψ ν π σ e)
    (h' : IsPadicSymmetricEpsilonFactor F ψ ν π σ e') : e = e' := by
  unfold IsPadicSymmetricEpsilonFactor at h h'
  split_ifs at h h'
  · exact h.unique h'
  · exact h.unique h'

/-- The epsilon relation for either rank order is invariant under representation
equivalences. -/
theorem IsPadicSymmetricEpsilonFactor.congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    {e : ℂˣ × ℤ} :
    IsPadicSymmetricEpsilonFactor F ψ ν π σ e ↔
      IsPadicSymmetricEpsilonFactor F ψ ν π₂ σ₂ e := by
  unfold IsPadicSymmetricEpsilonFactor
  split_ifs
  · exact IsPadicPairEpsilonFactor.congr_equiv φ φ'
  · exact IsPadicPairEpsilonFactor.congr_equiv φ' φ

theorem isPadicSymmetricLPolynomial_of_le (h : n ≤ r) {P : ℂ[X]} :
    IsPadicSymmetricLPolynomial F ψ ν π σ P ↔ IsPadicPairLPolynomial F ψ ν π σ P := by
  simp only [IsPadicSymmetricLPolynomial, h, ↓reduceIte]

theorem isPadicSymmetricLPolynomial_of_lt (h : r < n) {P : ℂ[X]} :
    IsPadicSymmetricLPolynomial F ψ ν π σ P ↔ IsPadicPairLPolynomial F ψ ν σ π P := by
  simp only [IsPadicSymmetricLPolynomial, Nat.not_le.mpr h, ↓reduceIte]

/-- The L-polynomial of a pair of either rank order is unique. -/
theorem IsPadicSymmetricLPolynomial.unique {P P' : ℂ[X]}
    (h : IsPadicSymmetricLPolynomial F ψ ν π σ P)
    (h' : IsPadicSymmetricLPolynomial F ψ ν π σ P') : P = P' := by
  unfold IsPadicSymmetricLPolynomial at h h'
  split_ifs at h h'
  · exact h.unique h'
  · exact h.unique h'

/-- The L relation for either rank order is invariant under representation
equivalences. -/
theorem IsPadicSymmetricLPolynomial.congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    {P : ℂ[X]} :
    IsPadicSymmetricLPolynomial F ψ ν π σ P ↔ IsPadicSymmetricLPolynomial F ψ ν π₂ σ₂ P := by
  unfold IsPadicSymmetricLPolynomial
  split_ifs
  · exact IsPadicPairLPolynomial.congr_equiv φ φ'
  · exact IsPadicPairLPolynomial.congr_equiv φ' φ

end Symmetric

end Langlands.RankinSelberg
