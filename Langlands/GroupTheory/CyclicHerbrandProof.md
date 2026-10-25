# Proof of the cyclic Herbrand calculus for ordinary group cohomology

This module proves the published proposition
`Langlands.GroupTheory.CyclicHerbrandCalculus.{u}` from
`Langlands.GroupTheory.CyclicHerbrandStatement`, for an arbitrary universe `u`.
The statement module and its imports are unchanged. All cohomology objects are
Mathlib's actual ordinary `groupCohomology` objects, as in the statement.

## Declarations

All theorems are in namespace `Langlands.GroupTheory` and have the single
universe parameter `u`.

- `cyclicHerbrandShortExact : CyclicHerbrandShortExact.{u}` proves all three
  two-out-of-three cases for a short exact sequence `S` in `Rep.{u} k G`. Each
  case gives finiteness of `H¹` and `H²` of the remaining term together with
  the division-free identity
  `h₂(S.X₂) * h₁(S.X₁) * h₁(S.X₃) = h₁(S.X₂) * h₂(S.X₁) * h₂(S.X₃)`, where
  `hᵢ(V) = Nat.card (groupCohomology V i)`.
- `cyclicHerbrandFiniteCoefficients : CyclicHerbrandFiniteCoefficients.{u}`
  proves that a representation with finite carrier has finite `H¹` and `H²`
  of equal cardinality.
- `cyclicHerbrandTrivialIntegers : CyclicHerbrandTrivialIntegers.{u}` proves
  that for `Langlands.Tate.integralTrivial G`, `H¹` is a subsingleton and `H²`
  is finite of cardinality `Nat.card G`.
- `cyclicHerbrandCalculus : CyclicHerbrandCalculus.{u}` is the exact proof
  target. Its type is the bundled statement itself.

The three component theorems let consumers use one clause without projecting
from the conjunction. Like the statement, none of them assumes `Nontrivial G`
or chooses a generator, so the trivial cyclic group is included.

## Implemented proof

The proof adapts the published generic core
`Langlands.Cohomology.HerbrandQuotient`, namespace
`Langlands.Cohomology.Herbrand`. That module constructs the exact hexagon of
the compatible endomorphisms `ρ(g) - 1` and the norm, and identifies its
subquotients with ordinary cohomology in degrees 1 and 2. This proof does not
repeat that construction.

- Short exact sequences. After introducing `k`, `G`, their instances, `S` and
  `hS : S.ShortExact`, the proof splits the conjunction into its three
  implications. In each case it introduces the four finiteness premises and
  adds each one to the local context as an instance (`have := h₁`, and so on),
  because the core theorems take these premises as instance arguments. It then
  applies `natCard_of_shortExact_mid hS`, `natCard_of_shortExact_left hS` or
  `natCard_of_shortExact_right hS`. The conclusions of these theorems are
  syntactically the conclusions of the three clauses.
- Finite coefficients. After introducing `V` and its `Finite V` instance, the
  proof applies `natCard_two_eq_natCard_one_of_finite V`.
- Trivial integers. After introducing `G` and its instances, the proof applies
  `groupCohomology_trivialIntegers`. This core theorem is stated for the same
  published representation `Langlands.Tate.integralTrivial G`.
- The bundled target is the anonymous-constructor triple of the three
  component theorems.

The core theorems use `k G : Type u` with the same shared universe as the
statement, so no universe transport is needed. The proof introduces no new
mathematical input. In particular, no idele-class vanishing theorem,
idele-class order calculation, fundamental-class theorem or other arithmetic
conclusion enters it. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Source

The mathematics is that of Emil Artin and John Tate, *Class Field Theory*
(2009), registered as `artin-tate-2009-class-field-theory`: Preliminaries §3,
Theorems q.1 and q.2 (printed pp.5–6), and Chapter V §1, Properties 1–3
(printed p.11). The statement module's Markdown explains how the
multiplication-only identity and the stronger trivial-integer conclusions are
derived from these passages. The Lean proof here follows the route of the
published core described above, not the source's text.
