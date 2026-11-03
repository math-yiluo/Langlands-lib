# Rank-one minimality among arbitrary ground-field pseudo-parabolics

This derived unit works over an arbitrary field and universe. The ambient
group is smooth, connected and affine. Its chosen actual maximal split torus
has every nonzero relative Lie root equal to an integral multiple of one
specified character `a`. The cocharacter `ν` pairs positively with `a`,
and its actual dynamic parabolic is proper. No primitivity of `a` is assumed.

The larger parabolic has an explicit closed representative `j : P → G`
that is smooth and connected. Smooth maximal-split-torus conjugacy is an
explicit proposition hypothesis. Cocharacter factorization through a maximal
split torus is supplied by the published `cocharacterMaximalSplitTorus` proof.

`RelativeRoot.rankOne_dynamicParabolic_eq_of_le_of_conjugacy` proves that
every smaller dynamic parabolic, for any ground-field cocharacter `χ`,
equals the larger parabolic on every scheme test. The published common-torus
reduction supplies a rational point `g` of the larger parabolic conjugating
`χ` to a cocharacter `eta` of the chosen torus. Pullback by inner
conjugation preserves containment and fixes the larger parabolic.
Same-torus rank-one minimality identifies the parabolic of `eta` with it;
the same pullback invariance then gives the asserted equality for `χ`.
Only the common-torus theorem from `GenericMinimalParabolicReduction` is
used, not its generic minimality theorem with root-negation and sign inputs.

`rankOneParabolicIsoOfLEOfConjugacy` constructs the canonical group-scheme
isomorphism from any representative of the smaller parabolic to `P`.
Its `_hom_comp` theorem identifies the composite with the actual ambient
inclusion. The construction reuses uniqueness of subgroup representatives
after the all-test functor equality.

`isMinimalPseudoParabolic_of_rankOne_dynamicParabolic` assumes that `j`
is pseudo-parabolic and proves minimality among all ground-field
pseudo-parabolic subgroups. Any smaller pseudo-parabolic contains the
dynamic parabolic of some cocharacter. The preceding equality makes that
dynamic parabolic equal to the image of `j`, forcing equality of the two
pseudo-parabolic images. This argument does not require the radical to be
trivial.

For a smooth connected affine group with trivial ground-field unipotent
radical, `Dynamic.isPseudoParabolicSubgroup_of_trivialUnipotentRadical`
supplies the pseudo-parabolic presentation of any closed representative
of a dynamic parabolic. The identity subgroup represents the radical,
and the represented dynamic parabolic equals its fppf-local product
with that trivial subgroup. Thus
`isMinimalPseudoParabolic_of_rankOne_of_trivialUnipotentRadical` combines
this presentation with the preceding minimality proof.

All statements concern the actual group schemes, integral lattices and
subgroup functors on every relative scheme test. The unit is an internal
deduction from the cited Library APIs and the included same-torus
rank-one comparison. It does not prove the supplied conjugacy statement,
connectedness of the parabolic representative, properness, cyclicity of
the roots, or reflection existence.
