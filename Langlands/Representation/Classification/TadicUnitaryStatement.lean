import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Unitary.Basic

/-!
# Actual Speh blocks and Tadic's unitary-dual exhaustion

The centered decreasing standard module and complementary products use actual
normalized upper-block induction. Speh representations are specified by a
quotient relation with uniqueness, without a chosen quotient or an existence
assumption. All classification assertions below are proposition definitions.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Raw parameters for a Speh representation: the positive rank of the actual
square-integrable candidate, the positive Speh length, and that candidate.
Its analytic and representation-theoretic conditions are a separate predicate. -/
structure SpehDatum where
  rank : ℕ
  rank_pos : 0 < rank
  length : ℕ
  length_pos : 0 < length
  delta : letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear rank F.Carrier)

namespace SpehDatum

variable {F T} (d : SpehDatum.{uF, uV} F T)

/-- The rank `k r` of `u(delta,k)`, retaining both source parameters. -/
abbrev degree : ℕ := d.length * d.rank

/-- The decreasing centered exponents `(k-1)/2-i`, for `0 ≤ i < k`.
Subtraction is in `ℝ`, so the negative endpoint is retained. -/
def exponent (i : Fin d.length) : ℝ :=
  ((d.length : ℝ) - 1) / 2 - (i : ℕ)

/-- The source condition `delta ∈ D^u`: actual irreducibility, an invariant
positive definite Hermitian form, and analytic square-integrability modulo
the actual center. -/
def IsDiscreteSeries : Prop :=
  letI := T.topology
  Representation.IsIrreducible d.delta.representation ∧
    IsUnitarizable d.delta.representation ∧ T.IsSquareIntegrable d.delta.representation

/-- The actual decreasing centered product
`nu^((k-1)/2) delta × ... × nu^(-(k-1)/2) delta` on `GL_(k r)`.
It is constructed for raw parameters; no quotient is chosen. -/
def centeredInduced :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier) :=
  T.twistedProductInduced (BlockShape.uniform d.length d.rank d.rank_pos)
    (fun _ => d.delta) d.exponent

/-- `pi` represents `u(delta,k)`: it is an actual irreducible quotient of the
centered decreasing induction, and every irreducible smooth quotient is
isomorphic to it. This relation asserts no existence for arbitrary parameters. -/
def IsSpeh
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier)) : Prop :=
  letI := T.topology
  d.IsDiscreteSeries ∧
    IsIrreducibleQuotient d.centeredInduced.representation π.representation ∧
      ∀ π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier),
        IsIrreducibleQuotient d.centeredInduced.representation π'.representation →
          Nonempty (π' ≅ π)

/-- The actual binary upper-normalized product `nu^alpha S × nu^(-alpha) S`.
Both factors use the very same supplied representation `S` of rank `k r`.
The Speh relation and the complementary interval are imposed separately. -/
def complementaryInduced
    (S : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
    (α : ℝ) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (2 * d.degree) F.Carrier) :=
  T.twistedProductInduced
    (BlockShape.uniform 2 d.degree (Nat.mul_pos d.length_pos d.rank_pos))
    (fun _ => S) (fun i => if (i : ℕ) = 0 then α else -α)

end SpehDatum

/-- Separate existence and uniqueness assertion for the Speh quotient.
Uniqueness is part of `IsSpeh`, quantified over all irreducible smooth quotients;
this is a statement target, not an assumed quotient constructor. -/
def SpehExistenceUniqueness : Prop :=
  letI := T.topology
  ∀ d : SpehDatum.{uF, uV} F T, d.IsDiscreteSeries →
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier),
      d.IsSpeh π

/-- Elementary length-one comparison, with the rank transport displayed.
For discrete-series data of length one, `IsSpeh` is exactly being isomorphic
to the original square-integrable block. -/
def SpehLengthOneComparison : Prop :=
  letI := T.topology
  ∀ (d : SpehDatum.{uF, uV} F T) (h : d.degree = d.rank)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier)),
    d.length = 1 → d.IsDiscreteSeries →
      (d.IsSpeh π ↔ Nonempty ((h ▸ π) ≅ d.delta))

/-- An actual Tadic building block of rank `n`: either a Speh representation,
or the entire complementary induction of opposite twists of one Speh
representation, with `0 < alpha < 1/2`. Witnesses retain the square-integrable
rank, Speh length, candidate Speh representation, and total-rank equality. -/
def IsTadicBuildingBlock {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  (∃ (d : SpehDatum.{uF, uV} F T)
      (S : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
      (h : d.degree = n),
      d.IsSpeh S ∧ Nonempty ((h ▸ S) ≅ π)) ∨
    (∃ (d : SpehDatum.{uF, uV} F T)
      (S : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
      (α : ℝ) (h : 2 * d.degree = n),
      d.IsSpeh S ∧ 0 < α ∧ α < (1 / 2 : ℝ) ∧
        Nonempty ((h ▸ d.complementaryInduced S α) ≅ π))

/-- Tadic 1986 Theorem D(ii), exhaustion clause: every actual irreducible
unitarizable representation of positive rank is isomorphic to the entire
normalized upper-block induction of a finite family of Tadic building blocks.
There is no genericity, Hermitian matching, or classification premise. -/
def TadicUnitaryDualExhaustion : Prop :=
  letI := T.topology
  ∀ (n : ℕ)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
    Representation.IsIrreducible π.representation → IsUnitarizable π.representation →
      ∃ (B : BlockShape (n + 1))
        (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
        (∀ i, IsTadicBuildingBlock F T (σ i)) ∧
          Nonempty (π ≅ (T.normalizedProductInductionFunctor B).obj σ)

/-- The focused Speh and generic-free exhaustion statement interface.
This does not assert the separate construction or parameter-uniqueness
directions of the full unitary-dual classification. -/
def TadicUnitaryDualStatements : Prop :=
  SpehExistenceUniqueness.{uF, uV} F T ∧
    SpehLengthOneComparison.{uF, uV} F T ∧
    TadicUnitaryDualExhaustion.{uF, uV} F T

/-- The interface over arbitrary independent field and representation universes,
for every finite p-adic extension and every compatible topology. -/
def PadicTadicUnitaryDualStatements : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    TadicUnitaryDualStatements.{uF, uV} F T

end Langlands.Classification
