# Upper breaks and Swan conductors of local Weil representations

`Langlands.Ramification.Local.weilBreakComparison` proves
`WeilBreakComparisonStatement` and exports each of its fourteen component
theorems. The base field `K`, its specified separable closure `Ω` and the
two complex representation carriers have independent universes. The proof
applies in either characteristic. [Statement and conventions](LocalWeilBreakStatement.md)

## Upper fixed spaces and presentation comparison

For a finite inertia action, `sum_upperBreakSupport_lt` identifies the
sum of multiplicities at breaks strictly below each positive index `r`
with the dimension of the upper fixed space at `r`. To recover the
individual coefficients from these sums, the proof works on the union of
the two finite supports. The sum just past a support point minus the sum
strictly below it gives its coefficient. Nonnegative support makes the
sum strictly below zero vanish, so this recovers the zero coefficient as
well. [Finite breaks](Breaks.md)

The nonnegative absolute upper groups lie in absolute inertia by
`absoluteUpperInertia` and antitonicity. The finite-image theorem
`Wintenberger.localAbsoluteUpperFiniteImage` gives the image of each
such group in every finite inertia group. The commuting restriction
square then shows that finite inertia restriction maps the upper group
at a larger field onto the upper group at the smaller field. Fixed vectors
of an inflated action are fixed vectors under that image, giving
`finiteUpperBreakInflation`. [Absolute inertia](Herbrand/LocalAbsoluteInertiaProof.md)
[Finite images](Wintenberger/Absolute.md)

Absolute inertia enters the Weil group by the degree-zero inclusion. Its
absolute upper subgroup maps onto the intrinsic Weil upper subgroup, since
the Weil projection is injective and every element of the intrinsic subgroup
projects into absolute inertia. A presentation intertwines this action with
the action through the finite restriction. This proves
`presentationUpperFixedComparison`, including at zero. For equivalent
Weil actions an intertwiner restricts to an isomorphism of the intrinsic
upper fixed spaces. The dimension comparison recovers the finite
multiplicities and support at any presentations. Taking the identity
equivalence gives presentation independence, which also applies to a
presentation and its refinement. [Inertia presentations](InertiaPresentation.md)

## Swan and Artin formulas

Write `d_i` for the dimension of the lower fixed space, `D` for the rank,
`m_i` for the lower multiplicity and `φ_i` for the value of Herbrand's
function at the integer `i`. The width `φ_(i+1) − φ_i` is
`|G_(i+1)| / |G_0|`, by the polygon formula for Herbrand's function. This
is also the weight in the Swan summand for `G_(i+1)`, since each such
lower group lies in inertia. The real cast of the finite rational Swan
sum is thus a sum of these widths times `D − d_(i+1)`.

The Lean induction for summation by parts proves the identity

\[
\sum_{i=0}^{n-1}(\varphi_{i+1}-\varphi_i)(D-d_{i+1})
  = \sum_{i=0}^{n}\varphi_i m_i + \varphi_n(D-d_{n+1}).
\]

Here `m_0 = d_1` and `φ_0 = 0`. At positive indices
`m_i = d_(i+1) − d_i`. At the ramification cutoff, the last codimension
vanishes and every lower multiplicity beyond the cutoff is zero. Mapping
the lower support through `i ↦ φ_i` gives
`finiteUpperBreakWeightedSwan`. For `finiteUpperBreakArtinIdentity`, the
existing decomposition of the Artin sum supplies the index-zero term,
which is the codimension of the full inertia fixed space.
[Finite Herbrand functions](Herbrand/GeneralFinite.md)
[Finite inertia conductors](LocalGalois.md)

## Intrinsic break and irreducible actions

A continuous Weil action admits a finite inertia presentation, and the
published inertia restriction theorem supplies surjectivity there. A
full upper fixed space is equivalent to trivial action. For a presentation
with positive rank, the finite fixed-space formula makes the positive
triviality indices exactly those strictly greater than the support maximum.
If the support is empty, the rank is zero and every positive index is a
triviality index. Hence the triviality set is nonempty in both cases.
Its infimum is the corresponding bound, using monotonicity to test any
threshold at arbitrarily close larger positive indices. This yields
`weilLastBreakFiniteMaximum` and the criterion `weilLastBreakZero`.
[Finite presentation existence](LocalInertiaPresentationProof.md)

An upper group is normal in the Weil group because it is the preimage of a
normal absolute upper group. Its fixed space is a Weil subrepresentation,
so irreducibility forces that space to be zero or full. At positive
indices the space is zero through the last break and full strictly above
it. If the last break is positive, the zero fixed space at that index
forces the minimum of the finite support to equal its maximum. If the
last break is zero, the nonnegativity of the support gives the same
equality. The total multiplicity is the rank, yielding the singleton
formula and then the Swan formula by evaluating the weighted sum. For a
basis class, an isomorphism from its quotient representative transports
continuity and irreducibility. The class rank and class last-break
equalities identify the parameters in all the formulas for the supplied
representative.

## Sources

- Jean-Pierre Serre, *Local Fields*, Springer, 1979. Chapter IV §1,
  Proposition 1, pp. 61–62 (PDF pp. 68–69) gives the lower filtration.
  Chapter IV §3, Propositions 12 and 14 and Remark 1, pp. 73–75
  (PDF pp. 80–82) give the Herbrand widths and the finite and inverse-limit
  quotient comparisons. Chapter VI §2, Proposition 2 and Corollary 1′,
  pp. 100–101 (PDF pp. 107–108) give the conductor sum from which the
  finite weighted formula is derived. Registered source
  `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
  [Springer edition](https://link.springer.com/book/10.1007/978-1-4757-5673-9)
- Pierre Deligne and Guy Henniart, *Sur la variation, par torsion, des
  constantes locales d'équations fonctionnelles de fonctions L*, Inventiones
  Mathematicae 64 (1981), §§0.4–0.7, pp. 91–93 (PDF pp. 3–5). These sections
  give the Weil upper filtration and its endpoint convention, the finite
  inertia action, the Artin–Swan identity and the irreducible break formulas.
  Registered source `deligne-henniart-1981-variation`, SHA256
  `54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.
  [Author's copy](https://publications.ias.edu/sites/default/files/Number43.pdf)
