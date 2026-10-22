# Finite upper-break and intrinsic Weil-break comparison targets

This module defines fourteen arithmetic comparison propositions and their
conjunction, `WeilBreakComparisonStatement`, in
`Langlands.Ramification.Padic`. It states the comparison results; it does not
prove them. It imports the published `Ramification.Breaks`,
`Ramification.InertiaPresentation`, and
`VirtualRepresentation.Weil.Ramification` constructions by their Lean names.

Every component is a `Prop`-valued definition with outer parameters
`{p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)`. The aggregate quantifies over
every prime and actual p-adic field. Finite extensions are actual finite Galois
intermediate fields of its algebraic closure. Representation carrier universes
`v` and `w` are independent of `u` and of each other; the equivalence component
uses both carriers, while each other component uses `v`.

`FiniteUpperBreakInflation` asserts equality of actual upper-break
multiplicities and supports after precomposing a genuine finite-inertia
representation with `finiteInertiaRestriction F h`, where `h : L ≤ M`.
`PresentationUpperBreakRefinement` states the descended-representation form.
`PresentationUpperBreakIndependence` compares any two presentations of the
same representation; `PresentationUpperBreakEquivalence` compares presentations
of equivalent Weil representations, allowing separate carrier universes.
Every occurrence of `P.representation` has separately quantified surjectivity
evidence for that exact Weil inertia restriction. None of these targets assumes
upper quotient compatibility, conductor independence, or break equality.
The universal surjectivity and presentation-existence statements belong to
task 1c3e2c0d and are not duplicated here.

`FiniteUpperBreakWeightedSwan` equates the actual rational Swan conductor,
coerced to `ℝ`, with the sum of `r * multiplicity(r)` over the actual finite
support. The zero multiplicity is the full wild-inertia-fixed dimension,
including tame and unramified vectors; its contribution to this sum is zero.
`FiniteUpperBreakArtinIdentity` records the actual rational Artin conductor
as Swan plus the codimension of invariants under all finite inertia.

`PresentationUpperFixedComparison` equates submodules on the same carrier:
the fixed vectors under the preimage of `absoluteUpperRamificationGroup F r`
under `localProjection F`, and the actual `inertiaUpperFixedVectors` of the
presentation, for every `r ≥ 0`. This equality includes zero. By contrast,
the extremum characterizations require positive indices: at zero,
the upper group is all inertia while the zero-break coefficient includes
the entire wild-inertia-fixed subspace.

The internal comparison route is to use the finite and absolute upper-image
arithmetic theorems, then restriction/descent evaluation and invariance of
fixed-space dimension under equivalence. Common composita compare arbitrary
presentations. Finite summation by parts and the actual Herbrand increments
give the weighted Swan formula. These are future proof routes, not hypotheses
or proofs included in this statement artifact.

`WeilTrivialityThresholdsNonempty` states that the actual set of nonnegative
indices at which every upper-group element acts as the identity is nonempty
for every continuous finite-dimensional Weil representation. Nonemptiness is
a conclusion, not a premise. `WeilLastBreakFiniteMaximum` states that for such
a representation of positive rank and every genuine presentation with its
separate surjectivity evidence, the finite support is nonempty and its maximum
is `lastBreak F A`. The existential nonempty witness is part of this conclusion;
the maximum is never used without that witness.

`WeilIrreducibleUpperBreak` adds actual Weil irreducibility to continuity and
states that the entire finite multiplicity function is
`Finsupp.single (lastBreak F A) A.rank`, and its support is the singleton
`{lastBreak F A}`. This implies both the asserted unique break and total
multiplicity equal to rank. Inertia irreducibility is not assumed.
`WeilIrreducibleSwanBreak` separately states that the actual presentation's
rational Swan conductor, coerced to the reals, equals rank times the intrinsic
label. The label is the existing threshold infimum, not a Swan/rank definition.

`WeilIrreduciblePositiveThresholds` gives both fixed-space equivalences for a
continuous Weil-irreducible representation: for `a > 0`,
`a ≤ lastBreak F A` if and only if `upperFixedSpace F A a = ⊥`; for `b > 0`,
`lastBreak F A < b` if and only if `upperFixedSpace F A b = ⊤`. At a positive break
itself the left-continuous convention retains the nontrivial upper action.
`WeilLastBreakZero` states, for every continuous representation, that the label
is zero if and only if every positive actual upper group acts trivially.
This clause includes reducible and rank-zero representations, and retains
both tame and unramified cases. It does not assert triviality under all inertia
at index zero. The `sInf` construction alone proves neither the nonemptiness
nor the one-break conclusion stated here.

`WeilClassBreakComparison` quantifies over each genuine continuous irreducible
class `b : VirtualRepresentation.LocalWeil.Basis F` and each representative
`A` whose actual `FiniteRepresentation.classOf A` is `underlyingClass b`.
That class equality encodes a genuine Weil isomorphism class; its continuity,
irreducibility, and positive rank are not newly postulated assumptions. The
conclusions are nonempty thresholds, `lastBreak F A = breakLabel F b`,
`A.rank = (b.1 : ℕ)`, the two positive-threshold equivalences, the zero-label
characterization, and, at every genuine finite presentation, the singleton
multiplicity function of coefficient `(b.1 : ℕ)`, singleton support, and actual
Swan equal to `(b.1 : ℕ)` times the label. The class and representative in this
clause share universe `v`; equivalence invariance between independently sized
carriers is supplied by `PresentationUpperBreakEquivalence` and the imported
intrinsic `lastBreak_equiv`.

For the Weil-side proof route, the fixed-space comparison and continuity would
first give eventual triviality. Finite support then identifies its threshold
infimum with the final break, including zero. Normality of actual Weil upper
groups makes their fixed spaces Weil-stable; Weil irreducibility would force
each to be zero or the whole carrier. This gives the single-break and boundary
comparisons. The weighted Swan identity gives rank times that label, and
actual representation equivalence transports these conclusions to each
irreducible class. These are explanations of the internal comparison route,
not additional hypotheses or implemented proofs.

## Original-source correspondence

This is an internal comparison family, derived from the following originals,
read directly by Worker 38. There was no source-specific errata file in the
published notes at the task's base.

- Serre, *Local Fields* (Greenberg translation, 1979), IV.1, printed pp.61–63
  (PDF pp.68–70): actual integer-ring lower groups, inertia at zero, and
  termination. IV.3, printed pp.73–76 (PDF pp.80–83): ceiling convention for
  real lower numbering, genuine Herbrand functions, upper quotient
  compatibility, and inverse limits and left continuity. VI.2, Proposition 2
  and Corollary 1', printed pp.100–101 (PDF pp.107–108): conductor sums from
  actual fixed-space codimensions. Registered source `serre-1979-local-fields`,
  `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
- Deligne–Henniart, *Sur la variation, par torsion, des constantes locales
  d'équations fonctionnelles de fonctions L* (1981), §§0.4–0.6, printed
  pp.91–93 (PDF pp.3–5): left-continuous upper groups, finite inertia action,
  continuous complex representations, the Artin–Swan identity, irreducible
  final breaks, and genuine constituent extrema. Registered source
  `deligne-henniart-1981-variation`,
  `/home/taskhub/central-library/Deligne-Henniart--Sur la variation, par torsion, des constantes locales d'equations fonctionnelles de fonctions L--1981.pdf`,
  SHA256 `54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.

The original image of DH81 printed p.92 was checked: its minimum comparison
uses `≥`, whose equality stroke is missing from the OCR, and its maximum
comparison uses `<`. Thus at positive `a`, the intended conclusion is
`a ≤ label ↔ fixedVectors(W^a) = ⊥`; at positive `b`, it is
`label < b ↔ fixedVectors(W^b) = ⊤`.

There are no multiplicities on exact K0, no identification of virtual Weil
support with cancelled inertia support, and no epsilon or DH81 stability
statement in this unit.
