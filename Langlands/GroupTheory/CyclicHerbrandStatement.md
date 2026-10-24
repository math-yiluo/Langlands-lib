# Cyclic Herbrand calculus statements

This module states the Herbrand calculus for Mathlib's actual ordinary
`groupCohomology` in degrees 1 and 2. Every declaration is a `def : Prop` in
`Langlands.GroupTheory`. These are proof targets; this module contains no proofs
of them. `CyclicHerbrandCalculus` is the conjunction of the three statements below.

## Scope and universes

The representation statements quantify over a commutative ring `k : Type u`,
a group `G : Type u` with `Finite G` and `IsCyclic G`, and objects of
`Rep.{u} k G`. The universe `u` is arbitrary. The shared universe follows the
pinned Mathlib ordinary group-cohomology interface. In particular, taking
`u = v`, `k = Langlands.NormalizedTwoCocycle.CoefficientScalars.{v}` and
`G = (E ≃ₐ[F] E)` for a field `E : Type v` is permitted; the base field may
live in an independent universe. No statement assumes `Nontrivial G`, chooses
a generator, or excludes the trivial cyclic group.

Write `H¹(V) = groupCohomology V 1`, `H²(V) = groupCohomology V 2`, and
`hᵢ(V) = Nat.card (groupCohomology V i)`. Finiteness is part of each statement,
not a convention inferred from a cardinality equality. In Lean, `Nat.card`
is zero for an infinite type; every use below comes with hypotheses and
conclusions that make the relevant cohomology groups finite. These additive
cohomology groups are nonempty, so their finite cardinalities are positive.

## Short exact sequences

`CyclicHerbrandShortExact` quantifies over
`S : ShortComplex (Rep.{u} k G)` with `S.ShortExact`, whose terms and maps form
`0 → S.X₁ → S.X₂ → S.X₃ → 0`. It is a conjunction of three implications:

1. Finiteness of `H¹` and `H²` for `S.X₁` and `S.X₃` implies finiteness of
   both groups for `S.X₂` and the equality below.
2. Finiteness of `H¹` and `H²` for `S.X₂` and `S.X₃` implies finiteness of
   both groups for `S.X₁` and the same equality.
3. Finiteness of `H¹` and `H²` for `S.X₁` and `S.X₂` implies finiteness of
   both groups for `S.X₃` and the same equality.

Each implication concludes the following equality in natural numbers:

`h₂(S.X₂) * h₁(S.X₁) * h₁(S.X₃) = h₁(S.X₂) * h₂(S.X₁) * h₂(S.X₃)`.

Thus the quotient convention is `h(V) = |H²(V)| / |H¹(V)|`, and this is the
multiplication-only form of `h(S.X₂) = h(S.X₁) * h(S.X₃)`. None of the three
cases assumes finiteness of the cohomology of the remaining term.

## Finite coefficients

`CyclicHerbrandFiniteCoefficients` quantifies over a representation `V` whose
underlying carrier has `Finite V`. It asserts that `H¹(V)` and `H²(V)` are
finite and `h₂(V) = h₁(V)`. This says that the Herbrand quotient is defined and
equal to one. The hypothesis concerns cardinal finiteness of the carrier,
not finite generation or finite dimension over `k`.

## Trivial integers

`CyclicHerbrandTrivialIntegers` uses the published
`Langlands.Tate.integralTrivial G`, namely
`Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)`. It asserts:

- `H¹(G, ℤ)` is a subsingleton;
- `H²(G, ℤ)` is finite;
- `Nat.card H²(G, ℤ) = Nat.card G`.

Since `H¹` is an additive group, the subsingleton assertion means it is trivial;
in particular it is finite and has cardinality one. The formula therefore gives
`h(G, ℤ) = |G|`. The lifted integer ring is definitionally the same carrier as
`Langlands.NormalizedTwoCocycle.CoefficientScalars.{u}` and the Library's
`IntegerScalars.{u}`. The existing scalar equivalence
`Langlands.Tate.integralScalarEquiv` identifies it with ordinary integers. For
the trivial group the asserted second-cohomology cardinality is one as well.
Although the coefficient alias comes from `Tate.ZeroDefinitions`, all
cohomology objects in this statement are ordinary `groupCohomology` objects.

## Original source and derivation

Source: Emil Artin and John Tate, *Class Field Theory* (2009), registered as
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The relevant original pages were read in text and rendered form:

- Preliminaries §3, printed p.5 (PDF p.14): the finite-index definition of the
  Herbrand quotient and its cyclic identification with the ratio `|H²|/|H¹|`.
- Preliminaries §3, Theorems q.1 and q.2, printed p.6 (PDF p.15):
  multiplicativity with all three two-out-of-three cases and quotient one for
  finite coefficients.
- Chapter V §1, Properties 1–3, printed p.11 (PDF p.20): the cyclic versions,
  including the value `|G|` on trivial integers.

Provenance is derived. The general coefficient-ring formulation retains the
underlying abelian group and its action. Multiplying the finite positive
cohomology orders turns Theorem q.1 into the displayed natural-number identity.
The stronger individual integer conclusions follow from the cyclic descriptions
on printed p.5: for a generator acting trivially, the difference endomorphism
is zero and the norm is multiplication by `|G|`. Its kernel on the integers is
zero and its cokernel is `ℤ / |G|ℤ`. This explains the stronger statement beyond
Property 3's quotient alone; it is not an additional claim quoted from that
property. No source erratum affecting these passages was found in the project's
source-specific errata notes.

## Existing implementation and exact proof follow-up

The published module `Langlands.Cohomology.HerbrandQuotient` supplies the matching
implementation in namespace `Langlands.Cohomology.Herbrand`:

- `natCard_of_shortExact_mid`, `natCard_of_shortExact_left`, and
  `natCard_of_shortExact_right` match the three short-exact clauses;
- `natCard_two_eq_natCard_one_of_finite` matches finite coefficients;
- `groupCohomology_trivialIntegers` matches the integer statement using the
  same published `integralTrivial` representation.

A subsequent exact proof unit can assemble these into
`Langlands.GroupTheory.CyclicHerbrandCalculus.{u}`, with its three components
available by conjunction projection. The existing core already supplies the
compatible-endomorphism exact hexagon and the periodic-resolution comparison;
these do not need to be duplicated in this statement module. Neither these
statements nor their intended adapter use an idele-class vanishing theorem,
an idele-class order theorem, or an unproved global arithmetic conclusion.
