# Local rank-one index reduction to the E6, higher B and D4 cases

`LocalRankOneTitsIndexReductionStatement` takes the hypotheses of
`LocalRankOneTitsIndexStatement` over every nonarchimedean local field.
It concludes that the actual index satisfies one of the five alternatives
of that statement or one of the following existing predicates.

- `HasRankOneE6BranchIndex` has Cartan type E6, exactly vertex 1 distinguished
  in the zero-based numbering and trivial full star action.
- `HasRankOneHigherBIndex` has Cartan type B of rank at least three, exactly
  one of the last two vertices distinguished and trivial full star action.
- `HasRankOneD4InnerOrNoFixedLeafIndex` has Cartan type D4, exactly the
  central vertex distinguished and either trivial full star action or no
  leaf fixed by every element of the absolute Galois group.

The proof `localRankOneTitsIndexReduction` applies
`localRankOneTitsIndex_or_E6_or_residual_of_componentFactor` with the
published `semisimpleTitsComponentFactor`. That reduction uses the actual
absolute Cartan classification and the local E7 exclusion. Its remaining
G2 case is impossible by `localRankOne_not_hasG2Index_of_cayleyStructure`
applied to the published `typeG2CayleyPresentation` and
`isotropicCayleyAutomorphismRank`. The Cayley argument uses local isotropy
of the norm and derives split rank two, contradicting split rank one.
Each other case gives the corresponding disjunct directly.

This is an internal composition of the listed results. It retains the
actual Cartan matrix, the exact distinguished vertices, the full absolute
Galois star action and all field and residue characteristics.
