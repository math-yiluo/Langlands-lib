# Upper cuspidal Jacquet counts from the associated filtration

Author: Worker 500.

`Langlands.GLUpperCuspidalJacquetMultiplicityFromFiltrationStatement` is a
focused algebraic adapter for the upper clause of
`GLCuspidalJacquetMultiplicityPrerequisitesStatement`. It is a proposition
definition and proves no theorem. The complete associated-filtration
proposition is an explicit premise for the given field, compatible
topological data and rank.

For every prime, every actual finite extension of its p-adic field and every
rank `n`, assume `AssociatedJacquetFiltrationTheorem F T n`. For ordered
block shapes `B, C` with associated embedded Levis and every irreducible
admissible cuspidal representation `ρ` of the actual product Levi of `B`,
let `Ju` be the actual normalized upper Jacquet module at `C` of normalized
upper induction from `B`. The conclusion supplies a composition series of
`Ju` of length

```
Nat.card (MinimalConjugatingPermutations B C).
```

For every target representation `τ` and every natural number `m`, it also
asserts

```
HasJordanHolderMultiplicity Ju (Rep.of τ) m
  ↔ m = Nat.card (AssociatingPermutations B C ρ τ).
```

These are the existing actual finite permutation subtypes. The
multiplicity counts matching minimal-permutation indices separately,
including repeated isomorphic factors. The biconditional asserts existence
with the indicated multiplicity and rules out every other multiplicity.
It uses the existing predicates for genuine finite zero-to-full
filtrations with irreducible graded quotients.

The field, source carrier and target carrier have independent universes
`uF`, `uV`, and `uW`. The induced and Jacquet carriers live in
`max uF uV`. The target representation need not be irreducible: the
irreducibility of the filtration factors determines which target
representations can match. The adapter also includes rank zero because its
input theorem already covers every rank. The eventual positive-rank
consumer can retain its target-irreducibility and rank hypotheses.

## Constructions and derivation

The upper module is exactly
`CuspidalJacquetMultiplicity.upperJacquet T C
  (CuspidalJacquetMultiplicity.induced T B (Rep.of ρ))`.
It uses the existing upper normalized induction and upper Jacquet actions;
no action, modulus or normalization is changed. Admissible cuspidality
supplies the smoothness and quasicuspidality needed to apply the filtration
premise. That premise supplies one actual graded quotient for each
`MinimalConjugatingPermutations B C` index, equivalent to the inverse
whole-Levi conjugation transport of `ρ`.

The intended proof specializes finite-family filtration counting to this
actual family of transports. Irreducibility under the existing actual
Weyl transport makes the supplied filtration a composition series.
Counting the matching indices gives definitionally
`AssociatingPermutations B C ρ τ`, and Jordan–Hölder independence excludes
all other counts. The functor object in the filtration premise and the
bundled `Ju` share definitionally identical representations. No separate
filtration or finite-length assumption is added to the conclusion.

This is an internal derived interface obtained by specializing the current
Library's `AssociatedJacquetFiltrationTheorem`, actual bundled upper
constructions and Jordan–Hölder predicates. It is not a new translation of
an original source. The geometric filtration remains the explicit input;
the statement neither proves it nor restates the opposite clause. The
full cuspidal Jacquet multiplicity theorem still requires that geometric
proof and the separate opposite-filtration transfer.
