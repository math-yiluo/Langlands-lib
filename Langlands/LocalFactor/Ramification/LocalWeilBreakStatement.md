# Finite upper breaks and intrinsic Weil breaks over local fields

`Langlands.Ramification.Local.WeilBreakComparisonStatement` is the conjunction
of fourteen propositions about upper-break multiplicities, conductors and the
intrinsic last break. It quantifies over every Mathlib nonarchimedean local
field `K` of any characteristic and every specified separable closure `Ω`.
The propositions are stated here; the Library does not prove them.

## Objects and conventions

The finite statements use actual finite Galois subfields of `Ω` over `K` and
their canonical realizations `SepClosed.finiteTopologicalData K Ω`. A finite
inertia presentation `P` records its subfield and a kernel inclusion for the
restriction of the given Weil action to inertia. Each descended action
`P.representation hP` takes a separately quantified proof `hP` of surjectivity
of the Weil inertia restriction at `P.extension`. This applies separately to
each field in a refinement or comparison. The companion
[inertia statements](LocalInertiaPresentationStatement.md) state the
surjectivity and presentation existence properties.

At a finite level the lower group at real index `u` uses `ceil u`, and the
upper group at `r` uses the lower group at `ψ(r)`. Write `φ` for the inverse of
`ψ`. If `dᵢ` is the dimension fixed by the lower group `Gᵢ`, the coefficient
at `φ(i)` for `i > 0` is `dᵢ₊₁ − dᵢ`. The coefficient at zero is `d₁`, the
whole wild-inertia-fixed dimension, including tame and unramified parts. It
contributes zero to the weighted Swan sum. The group at upper index zero is all
inertia. At a positive break `b` of an irreducible action the left-continuous
convention gives zero fixed space at `b` and full fixed space at indices
strictly greater than `b`.

The intrinsic data use the Weil projection to the absolute Galois group of
`K` in `Ω`. The upper group is the preimage of the absolute upper group.
`trivialityThresholds` consists of nonnegative indices at which this group
acts as the identity, and `lastBreak` is its real infimum. All representations
are finite-dimensional over `ℂ`. The Weil clauses use `FiniteRepresentation`.
The universes `uK`, `uΩ`, `uV` and `uW` are independent, with `uW` used for
the second carrier in `PresentationUpperBreakEquivalence`.

## Statements and provenance

The first two columns give names in `Langlands.Ramification.Local` and
`Langlands.Ramification.Padic`, respectively. Each component in the first column
takes `K` and `Ω` with their field, local-field and separable-closure instances.
The general class comparison uses a class and a representative in the same
carrier universe. The source locations use printed pages.

| General statement | P-adic counterpart | Assertion | Source |
| --- | --- | --- | --- |
| `FiniteUpperBreakInflation K Ω` | `FiniteUpperBreakInflation F` | For `L ≤ M`, precomposing a finite inertia action at `L` with inertia restriction from `M` preserves the entire multiplicity function and its support. | Derived from Serre IV §3 Proposition 14, pp. 74–75. Every upper-group image gives the same fixed space after inflation. |
| `PresentationUpperBreakRefinement K Ω` | `PresentationUpperBreakRefinement F` | Refining a presentation at a larger finite Galois subfield preserves the multiplicity function of the descended action. | Derived from Serre IV §3 Proposition 14, pp. 74–75, using descent at both fields. |
| `PresentationUpperBreakIndependence K Ω` | `PresentationUpperBreakIndependence F` | Any two finite inertia presentations of the same Weil action have equal multiplicity functions and support. | Derived from Serre IV §3 Proposition 14, pp. 74–75, by comparing both in their compositum. |
| `PresentationUpperBreakEquivalence K Ω` | `PresentationUpperBreakEquivalence F` | Equivalent Weil actions have equal multiplicity functions and support at any pair of presentations. | Derived from the same quotient comparison and invariance of fixed-space dimensions under an intertwining isomorphism. Serre IV §3 Proposition 14, pp. 74–75. |
| `FiniteUpperBreakWeightedSwan K Ω` | `FiniteUpperBreakWeightedSwan F` | The rational finite inertia Swan conductor, coerced to `ℝ`, equals `∑ r ∈ support, r * multiplicity(r)`. | Derived by finite summation by parts from Serre VI §2 Proposition 2 and Corollary 1′, pp. 100–101, and the increments of `φ` in IV §3 Proposition 12, p. 73. |
| `FiniteUpperBreakArtinIdentity K Ω` | `FiniteUpperBreakArtinIdentity F` | The rational finite inertia Artin conductor equals Swan plus the codimension of invariants under the whole inertia group. | Serre VI §2 Proposition 2 and Corollary 1′, pp. 100–101, with the `i = 0` term. Deligne–Henniart §0.5, p. 92. |
| `PresentationUpperFixedComparison K Ω` | `PresentationUpperFixedComparison F` | For every `r ≥ 0`, the intrinsic Weil upper fixed space equals the upper fixed space of the descended action at the presentation. | Derived from upper-group images in Serre IV §3 Proposition 14 and Remark 1, pp. 74–75, and Deligne–Henniart §0.4, pp. 91–92. |
| `WeilTrivialityThresholdsNonempty K Ω` | `WeilTrivialityThresholdsNonempty F` | Each continuous Weil action is trivial at some nonnegative upper index. | Derived from finite inertia image in Deligne–Henniart §0.5, p. 92, and eventual triviality at each finite level in Serre IV §3, p. 74. |
| `WeilLastBreakFiniteMaximum K Ω` | `WeilLastBreakFiniteMaximum F` | A continuous positive-rank Weil action has nonempty support at every finite presentation, and the maximum of that support equals its intrinsic last break. | Derived from the fixed-space jumps and their endpoints in Serre IV §3, pp. 73–75, and Deligne–Henniart §§0.4–0.6, pp. 91–92. |
| `WeilIrreducibleUpperBreak K Ω` | `WeilIrreducibleUpperBreak F` | For a continuous Weil-irreducible action of rank `d` and last break `b`, every presentation has multiplicity function `Finsupp.single b d` and support `{b}`. | Deligne–Henniart §0.6, p. 92, expressed in finite-presentation terms using the upper-group image in §0.4. |
| `WeilIrreducibleSwanBreak K Ω` | `WeilIrreducibleSwanBreak F` | For a continuous Weil-irreducible action the Swan conductor at every presentation, coerced to `ℝ`, equals rank times the intrinsic last break. | Deligne–Henniart §0.6, p. 92. The finite-presentation expression also follows from the single break and the weighted Swan formula. |
| `WeilIrreduciblePositiveThresholds K Ω` | `WeilIrreduciblePositiveThresholds F` | For a continuous Weil-irreducible action with last break `b` and `r > 0`, `r ≤ b` exactly when the fixed space is zero, and `b < r` exactly when it is the full space. | Deligne–Henniart §§0.4 and 0.6, pp. 91–92. The printed lower comparison on p. 92 includes equality. |
| `WeilLastBreakZero K Ω` | `WeilLastBreakZero F` | For any continuous Weil action, last break zero is equivalent to trivial action by every positive upper group. | Derived from the decreasing filtration of Deligne–Henniart §0.4, pp. 91–92, and nonempty thresholds. The tame character convention appears in §0.7, p. 93. |
| `WeilClassBreakComparison K Ω` | `WeilClassBreakComparison F` | For each continuous irreducible Weil basis class, any representative with the specified Weil isomorphism class has nonempty thresholds, last break and rank given by the class, both positive-threshold equivalences and the zero-label criterion. At every finite presentation its multiplicity function and support have the single class label, with multiplicity the class rank, and its Swan conductor is rank times that label. | Internal packaging of the irreducible formulas of Deligne–Henniart §0.6, p. 92, transported along Weil representation equivalence. |
| `WeilBreakComparisonStatement` | `WeilBreakComparisonStatement` | Conjunction of the fourteen clauses for all `K` and `Ω`. The p-adic aggregate quantifies over all primes and p-adic fields. | Internal organization of the propositions. |

Continuity guarantees eventual triviality on upper groups by finite inertia
descent. With positive rank, the jump to the full fixed space identifies the
maximum of the finite support. Normality of the Weil upper groups makes their
fixed spaces Weil-stable, so Weil irreducibility forces each to be zero or
the full space. The threshold statements use the infimum of the actual
triviality set. The zero-break clause also applies to reducible and rank-zero
actions, and its triviality criterion concerns positive indices.

## Relation to the p-adic statements

Take `K = F.Carrier` with the instances of `F.canonicalTopologicalData` and
`Ω = AlgebraicClosure F.Carrier`. The algebraic closure is a separable closure
in this characteristic-zero specialization. The Weil group, its inertia and
the irreducible Weil basis agree by unfolding the corresponding wrappers.

The finite and absolute upper filtrations in these propositions use spectral
base `K` with the local norm of `K`. The p-adic counterparts use spectral base
`Padic p`. Both valuations on each finite level `L` extend the valuation of
`F.Carrier` up to normalization. Their integer rings are the same subring of
`L`, the integral closure of the integers of `F` in `L`. This comparison uses
equality of valuation rings and hence is at the level of propositions.
See Serre II §2 Proposition 3, pp. 28–29 (PDF pp. 36–37), and the Library's
[finite](Herbrand/GeneralFinite.md) and [absolute](Herbrand/LocalAbsoluteStatement.md)
filtration descriptions.

The common integer rings identify the residue actions, finite inertia and
restriction maps, so they identify the presentations and their descended
actions. Their maximal ideal powers identify the lower groups. The same
group orders give the same Herbrand functions and hence the same upper groups,
fixed-space jumps and conductor sums. This gives the finite comparisons in the
first six rows of the table. The same upper groups at every finite level
identify the absolute upper groups by intersection, and their Weil preimages
identify the intrinsic fixed spaces, triviality thresholds, infima and class
labels. These comparisons give the remaining eight components, with the same
quantifiers after specialization. The p-adic aggregate then uses those
componentwise comparisons at each `F`.

## Original literature

- Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
  Springer, 1979. II §2 Proposition 3, pp. 28–29 (PDF pp. 36–37), identifies
  the valuation ring on a finite extension. IV §1, pp. 61–63 (PDF pp. 68–70),
  gives the integer-ring lower groups. IV §3, pp. 73–76 (PDF pp. 80–83),
  gives Herbrand reindexing, upper-group termination, quotient images and
  inverse limits. VI §2 Proposition 2 and Corollary 1′, pp. 100–101
  (PDF pp. 107–108), give the fixed-space conductor sums. The residue
  extensions of the local fields here are separable because their residue
  fields are finite. Registered source `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
  [Springer edition](https://link.springer.com/book/10.1007/978-1-4757-5673-9)
- Pierre Deligne and Guy Henniart, *Sur la variation, par torsion, des
  constantes locales d'équations fonctionnelles de fonctions L*,
  Inventiones Mathematicae 64 (1981), §§0.4–0.7, pp. 91–93 (PDF pp. 3–5),
  gives the left-continuous Weil upper filtration, finite inertia action,
  the Artin–Swan identity, and the irreducible last break and Swan formula.
  Registered source `deligne-henniart-1981-variation`, SHA256
  `54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.
  [Author's copy](https://publications.ias.edu/sites/default/files/Number43.pdf)
