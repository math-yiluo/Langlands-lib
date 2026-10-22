import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Classification.LanglandsData

/-!
# L-factors of pairs through the Langlands classification

JPSS 1983, (9.4) and (9.5), printed pages 458-463. Proposition (9.4)(3): for
induced representations `ξ` and `η` of Langlands' type (tempered blocks twisted
by strictly decreasing real exponents), `L(s, ξ × η)` is the product of the
L-factors of the pairs of twisted blocks. (9.4)(4): for generic irreducible
quotients `π` of `ξ` and `σ` of `η`, `L(s, ξ × η) = L(s, π × σ)`; JPSS take
this as the definition of `L(s, π × σ)` for every pair of irreducible admissible
representations, recorded here by the relation `IsLanglandsPairLPolynomial`.
Theorem (9.5): this L-factor is biadditive for the Langlands sum, stated here in
the equivalent product form over the essentially square-integrable data of the
two representations (Henniart 2002, 2.8).
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- `L(s, π × σ) = 1 / P(q^(-s))` for representations `π` of `GL_n(F)` and `σ` of
`GL_t(F)` of arbitrary rank: the relation `IsPadicSymmetricLPolynomial` when both
ranks are positive, and `False` when one of them is zero. It applies the factor
relations to the blocks of the Library's block shapes, whose sizes are not
syntactically successors. -/
def IsPadicRankLPolynomial (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n t : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W)
    (P : ℂ[X]) : Prop :=
  match n, t, π, σ with
  | _ + 1, _ + 1, π, σ => IsPadicSymmetricLPolynomial F ψ ν π σ P
  | _, _, _, _ => False

section Rank

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isPadicRankLPolynomial_succ {r k : ℕ}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (k + 1) F.Carrier) W} {P : ℂ[X]} :
    IsPadicRankLPolynomial F ψ ν π σ P ↔ IsPadicSymmetricLPolynomial F ψ ν π σ P :=
  Iff.rfl

/-- The L-polynomial of a pair of arbitrary ranks is unique. -/
theorem IsPadicRankLPolynomial.unique {n t : ℕ}
    {π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W} {P P' : ℂ[X]}
    (h : IsPadicRankLPolynomial F ψ ν π σ P) (h' : IsPadicRankLPolynomial F ψ ν π σ P') :
    P = P' := by
  match n, t, π, σ, h, h' with
  | _ + 1, _ + 1, _, _, h, h' => exact IsPadicSymmetricLPolynomial.unique h h'

end Rank

/-- JPSS 1983, (9.4), printed page 458: `L(s, π × σ)` for irreducible
representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)`, defined through
the Langlands classification. `π` is a quotient of the standard module `ξ` of
some tempered Langlands datum, `σ` one of the standard module `η` of another,
and for every such pair of data the standard modules satisfy
`L(s, ξ × η) = 1 / P(q^(-s))`. -/
def IsLanglandsPairLPolynomial (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r t : ℕ}
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier))
    (P : ℂ[X]) : Prop :=
  (∃ d : PadicField.TopologicalData.TemperedLanglandsDatum.{uV, uF}
      F.canonicalTopologicalData (r + 1), d.IsLanglandsQuotient π) ∧
    (∃ e : PadicField.TopologicalData.TemperedLanglandsDatum.{uW, uF}
      F.canonicalTopologicalData (t + 1), e.IsLanglandsQuotient σ) ∧
    ∀ (d : PadicField.TopologicalData.TemperedLanglandsDatum.{uV, uF}
        F.canonicalTopologicalData (r + 1))
      (e : PadicField.TopologicalData.TemperedLanglandsDatum.{uW, uF}
        F.canonicalTopologicalData (t + 1)),
      d.IsLanglandsQuotient π → e.IsLanglandsQuotient σ →
        letI := F.canonicalTopologicalData.topology
        IsPadicSymmetricLPolynomial F ψ ν d.standardModule.representation
          e.standardModule.representation P

/-- The L-polynomial defined through the Langlands classification is unique. -/
theorem IsLanglandsPairLPolynomial.unique {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {r t : ℕ}
    {π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)}
    {σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)}
    {P P' : ℂ[X]} (h : IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P)
    (h' : IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P') : P = P' := by
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩, hP⟩ := h
  exact (hP d e hd he).unique (h'.2.2 d e hd he)

/-- JPSS 1983, Proposition (9.4), display (3), printed page 458. Let
`ξ = Ind(π_1, …, π_m)` be the standard module of a tempered Langlands datum of
`GL_(r+1)(F)`: irreducible tempered `π_(i,0)`, real `u_1 > ⋯ > u_m`,
`π_i = π_(i,0) ⊗ α^(u_i)`, normalized induction from the standard upper block
parabolic. Let `η = Ind(σ_1, …, σ_n)` be one of `GL_(t+1)(F)`. Then
`L(s, ξ × η) = ∏_(i,j) L(s, π_i × σ_j)`. -/
def LanglandsTypeLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ)
    (d : PadicField.TopologicalData.TemperedLanglandsDatum.{uV, uF}
      F.canonicalTopologicalData (r + 1))
    (e : PadicField.TopologicalData.TemperedLanglandsDatum.{uW, uF}
      F.canonicalTopologicalData (t + 1)),
    ∃ (P : ℂ[X]) (Q : Fin d.shape.length → Fin e.shape.length → ℂ[X]),
      (letI := F.canonicalTopologicalData.topology;
        IsPadicSymmetricLPolynomial F ψ ν.val d.standardModule.representation
          e.standardModule.representation P) ∧
      (∀ i j, letI := F.canonicalTopologicalData.topology;
        IsPadicRankLPolynomial F ψ ν.val
          (F.canonicalTopologicalData.twistedBlocks d.shape d.blocks d.exponent i).representation
          (F.canonicalTopologicalData.twistedBlocks e.shape e.blocks e.exponent j).representation
          (Q i j)) ∧
      P = ∏ i, ∏ j, Q i j

/-- JPSS 1983, (9.4), display (4), printed page 458. If `π` is a generic
irreducible quotient of the standard module `ξ` of a tempered Langlands datum of
`GL_(r+1)(F)`, and `σ` a generic irreducible quotient of the standard module `η`
of one of `GL_(t+1)(F)`, then `L(s, ξ × η) = L(s, π × σ)`. -/
def GenericLanglandsQuotientLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ)
    (d : PadicField.TopologicalData.TemperedLanglandsDatum.{uV, uF}
      F.canonicalTopologicalData (r + 1))
    (e : PadicField.TopologicalData.TemperedLanglandsDatum.{uW, uF}
      F.canonicalTopologicalData (t + 1))
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)),
    d.IsLanglandsQuotient π → e.IsLanglandsQuotient σ →
    (letI := F.canonicalTopologicalData.topology; IsGeneric ψ r π.representation) →
    (letI := F.canonicalTopologicalData.topology; IsGeneric ψ t σ.representation) →
    ∃ P : ℂ[X], letI := F.canonicalTopologicalData.topology
      IsPadicSymmetricLPolynomial F ψ ν.val d.standardModule.representation
          e.standardModule.representation P ∧
        IsPadicSymmetricLPolynomial F ψ ν.val π.representation σ.representation P

/-- JPSS 1983, (9.4), printed page 458: every irreducible admissible
representation is the quotient of a representation of Langlands' type, uniquely,
so (4) defines `L(s, π × σ)` for every pair of irreducible admissible
representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)`. -/
def LanglandsPairLFactorExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ)
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)),
    (letI := F.canonicalTopologicalData.topology;
      Representation.IsIrreducible π.representation) →
    (letI := F.canonicalTopologicalData.topology; π.IsAdmissible) →
    (letI := F.canonicalTopologicalData.topology;
      Representation.IsIrreducible σ.representation) →
    (letI := F.canonicalTopologicalData.topology; σ.IsAdmissible) →
    ∃ P : ℂ[X], IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π σ P

/-- JPSS 1983, Theorem (9.5), printed pages 462-463, in product form (Henniart
2002, 2.8, printed page 596). Let `π` be an irreducible quotient of
`i(τ_1, …, τ_p)` for essentially square-integrable irreducible `τ_i` of
`GL_(r_i)(F)` with decreasing exponents, and `σ` one of `i(μ_1, …, μ_q)` on
`GL_(t+1)(F)`. Then `L(s, π × σ) = ∏_(i,j) L(s, τ_i × μ_j)`, with the left side
defined through the Langlands classification. -/
def SquareIntegrableDataLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ)
    (d : PadicField.TopologicalData.SquareIntegrableLanglandsDatum.{uV, uF}
      F.canonicalTopologicalData (r + 1))
    (e : PadicField.TopologicalData.SquareIntegrableLanglandsDatum.{uW, uF}
      F.canonicalTopologicalData (t + 1))
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)),
    d.IsLanglandsQuotient π → e.IsLanglandsQuotient σ →
    ∃ (P : ℂ[X]) (Q : Fin d.shape.length → Fin e.shape.length → ℂ[X]),
      IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π σ P ∧
      (∀ i j, letI := F.canonicalTopologicalData.topology;
        IsPadicRankLPolynomial F ψ ν.val (d.blocks i).representation
          (e.blocks j).representation (Q i j)) ∧
      P = ∏ i, ∏ j, Q i j

/-- The L-factor statements of JPSS 1983, Section 9: Proposition (9.4) with
displays (3) and (4), the definition of the L-factor for all irreducible
admissible pairs, and Theorem (9.5) in product form. -/
def LanglandsQuotientLFactorStatement : Prop :=
  LanglandsTypeLFactorStatement.{uF, uV, uW} ∧
    GenericLanglandsQuotientLFactorStatement.{uF, uV, uW} ∧
    LanglandsPairLFactorExistenceStatement.{uF, uV, uW} ∧
    SquareIntegrableDataLFactorStatement.{uF, uV, uW}

end Langlands.RankinSelberg
