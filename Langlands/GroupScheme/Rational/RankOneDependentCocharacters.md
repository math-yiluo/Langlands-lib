# Dynamic parabolics on a dependent root line

This internal development supplies the cocharacter comparison needed by the
derived formulation of Milne's rank-one Borel geometry. It proves no Borel
classification. The dynamic comparison holds for every smooth connected affine
group over any field, with any split torus map whose actual relative roots are
each integrally dependent with a specified character. Maximality and
reductivity are unnecessary for this comparison.

For two dependent characters `a` and `b` and any cocharacters `ν` and `eta`,
`latticePairing_cross_difference_eq_zero_of_dependent` proves

```
⟨b, ⟨a,ν⟩ eta - ⟨a,eta⟩ ν⟩ = 0.
```

The proof argues contrapositively. If this determinant were nonzero, pairing
an integral relation `m a + n b = 0` with the two cocharacters and eliminating
each coefficient would force both `m` and `n` to vanish. This would make the
two characters linearly independent. No cyclic generator of the integral
root set is chosen or assumed.

`IsSplitTorus.finrank_relativeRootSpan_eq_one_of_rankOne` identifies the exact
pairwise integral dependence hypothesis, together with one actual root, with
rational root span of dimension one in the forward direction needed here.
It uses the published singleton-span theorem and injectivity of the split
torus character lattice into its rationalization. Separately,
`IsSplitTorus.isRegularCocharacter_of_rankOne` uses the published dependent-pair
nonvanishing theorem: a cocharacter nonorthogonal to one actual root is
nonorthogonal to every actual root. Neither result assumes a reduced root
system.

`RelativeRoot.isCentral_cross_difference_of_dependent_relativeRoots` applies
the determinant identity to every actual relative root. The published
`rootAnnihilatorCentrality` theorem then gives actual centrality of the
cross difference on every scheme test.

`RelativeRoot.parabolic_eq_of_dependent_pairings_pos` follows the integral
central-shift and positive-scaling argument in the published
`RelativeRoot.rankOneParabolic_eq_of_pairings_pos`, replacing its cyclic-root
assumption by the determinant argument. Adding the central cross difference
identifies positive integral multiples of the original cocharacters;
positive scaling leaves their dynamic parabolic functors unchanged.
The negative-pairing version applies this result to the negative character.

Finally,
`RelativeRoot.parabolic_pair_eq_or_swap_of_dependent_pairings_ne_zero` splits
the two nonzero pairings into their four sign cases. The ordered pair of
dynamic parabolics for `±eta` equals that for `±ν`, possibly after interchange.
These are equalities of subgroup functors, so they include every test scheme
and transfer any supplied representation by a fixed subgroup embedding.
`RelativeRoot.signedParabolicPairIdentification` packages this result as
actual identification data: a Boolean recording whether to interchange
the signs, together with the two subgroup-functor equalities.

The provenance is internal and derived: these are algebraic consequences of
the published lattice-pairing, rational root-span, root-annihilator centrality,
central-shift and positive-scaling results. They address the arbitrary
nonorthogonal-cocharacter comparison in the rank-one Borel task without
retaining a primitive-generator hypothesis. The geometric assertion that
every prescribed Borel represents one of the two parabolics remains a
separate proof obligation.
