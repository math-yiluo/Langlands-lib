# The canonical compact-induction normal-coinvariant map

Worker 182 constructs `Langlands.Induction.compactNormalCoinvariantsMap`.
This is an actual intertwining linear map. Its bijectivity and the full
`CompactInductionNormalCoinvariants` proposition remain separate proof obligations.

Let G be any topological group, let H and N be subgroups, and suppose N is
normal in G and N is contained in H. Let sigma be a representation of H on any
complex module V. The group and coefficient universes are independent. The
construction needs neither closedness of H or N, a compact-open basis,
Hausdorffness, nor smoothness of sigma. It also imposes no topology, norm,
completeness, dimension, admissibility or finite-length condition on V.
These weaker hypotheses concern only construction of the map and its identities;
they make no assertion about bijectivity under weaker assumptions.

The map has source `(compactInduced H sigma).toCoinvariants N` and target
`compactInduced H (sigma.toCoinvariants (N.subgroupOf H))`. All spaces, quotient
relations, actions and maps are the existing Library and Mathlib constructions.
The actual compactly induced functions have compact projected nonzero support,
and their action is right translation. No alternative function or quotient model
is introduced.

First postcompose each compactly induced function with
`sigma.toCoinvariantsMkQ (N.subgroupOf H)` using the actual `compactInducedMap`.
Its existing construction proves smoothness and preservation of compact support.
For n in N and x in G, normality gives x n x^-1 in N, and containment puts this
element in H. Covariance identifies f(x n) with sigma(x n x^-1) f(x).
Mathlib's `Coinvariants.mk_self_apply` identifies their coefficient quotient
classes. This proves invariance under the restricted N-action on the whole
function. `Coinvariants.lift` therefore descends this postcomposition map.
The descended ambient G-equivariance is checked on quotient representatives
using `Coinvariants.hom_ext`; right translation commutes with postcomposition.

The public identities are:

- `compactNormalCoinvariantsMap_mk`: on the class of f, the map is exactly
  `compactInducedMap H (sigma.toCoinvariantsMkQ (N.subgroupOf H)) f`.
- `compactNormalCoinvariantsMap_eval`: evaluating that result at x is exactly
  the coefficient coinvariant class of f(x).
- `compactNormalCoinvariantsMap_natural`: for every actual intertwiner T
  between H-representations, the map commutes with the actual coinvariant map
  of `compactInducedMap H T` and the actual `compactInducedMap` of
  `normalCoinvariantsMap (N.subgroupOf H) T`. Source and target coefficient
  universes are independent. Specialization to morphisms in the full smooth
  representation category therefore gives the naturality required by the parent
  proposition.

The first two identities are definitional equalities. Naturality is proved by
coinvariant induction; both composites on a representative are definitionally
the class of the pointwise image under T. No injectivity, surjectivity, exactness,
lifting, averaging or comparison-equivalence assertion is assumed or proved by
this construction.

## Provenance

This is an internal construction from the published induction and coinvariant
operations, implementing the pointwise map specified by the published
`NormalCoinvariantStatement`. Its motivation is Bernstein and Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), section 5.16,
printed pages 465–466, PDF pages 26–27. Worker 182 read the whole section,
including the reduction diagram, and visually checked both pages. The source
uses that the normal subgroup acts trivially on the coset space, then localization
of compactly supported sections to obtain its comparison. The present map and its
formal descent identities are not separately printed in this notation. The
source's complement restriction and normalization are outside this construction.

Registered source: `bernstein-zelevinsky-1977-induced-i`.
SHA256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Retained original:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
All imported Lean/Markdown pairs are preserved unchanged.
