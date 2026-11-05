# Actual central additive subgroups and a split-radical quotient reduction

`CentralAdditiveClosedSubgroup Q` bundles an actual group scheme, its
inclusion into `Q`, closedness, centrality, and its natural
one-dimensional vector-group coordinates. This is an internal data
interface for the existential condition in the published
`UnipotentWoundCriterionStatement`, not a new source assertion.
`CentralAdditiveClosedSubgroup.nonempty_iff` proves the exact
correspondence with that existential condition. No subgroup, lift,
section, or woundness proof is supplied as an extra premise to the
exclusion result below.

This internal unit proves that a supplied smooth connected affine fppf
quotient by a represented split radical has no central closed additive
subgroup. When the source is unipotent, the existing exact
`UnipotentWoundCriterionStatement` implies that this quotient has only
constant affine-line maps. That criterion remains an explicit premise
of the final conditional lemma.

The argument is the central-subgroup enlargement step behind
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Theorem B.3.4, printed pp.573–574 / one-based PDF pp.599–600.
The registered source is `conrad-gabber-prasad-2015-pseudo-reductive`,
SHA-256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`,
readable at
`/home/taskhub/central-library/Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`.
Appendix B treats positive characteristic. The implemented reduction is
valid over every field and uses only published all-field pullback,
kernel, split-series and representation-theoretic unipotence results.
It is not a direct transcription of the source's dimension induction.

`SubgroupPreimage.isSplitUnipotent_of_fppfQuotient` takes a supplied
closed smooth connected split kernel, an actual fppf quotient with that
full kernel, and a supplied closed split subgroup of the quotient.
The actual inverse image is an extension of the subgroup by the same
kernel. The published kernel comparison identifies its projection
kernel with the original kernel and then with its supplied representative.
These isomorphisms transport the finite split series. The published
extension theorem gives a finite split series on the inverse image.
Flatness, surjectivity, local finite presentation and quasi-compactness
of its projection are obtained by base change. All kernel comparisons
use the full subgroup functors on every relative scheme test.

`IsSplitUnipotentRadical.not_exists_central_additive_closed_subgroup`
applies this construction to an assumed central closed one-dimensional
vector subgroup of the quotient. Its inverse image is closed, smooth,
connected, split, and normal in the source. Unipotence follows from its
finite split series in the existing coefficient-representation sense.
Greatestness of the supplied split radical therefore puts that inverse
image back into the original kernel. The published pullback argument
then makes the additive subgroup's range trivial. This contradicts
closedness of its inclusion and the existence of a nonidentity rational
point of a one-dimensional vector group.
`isEmpty_centralAdditiveClosedSubgroup` expresses the same exclusion for
the actual bundled data.

`hasConstantAffineLineMaps_quotient_of_criterion` uses the exact central
criterion on the quotient, whose unipotence follows from unipotence of
the source and the supplied fppf quotient.

The unconditional central-subgroup exclusion does not itself prove
affine-line constancy. This unit also does not identify the split radical
of the ordinary radical with the ambient group's split radical.
That identification requires the additional ambient stability argument.
Consequently the exact `SplitRadicalWoundQuotientStatement` remains a
separate proof obligation. No characteristic, perfectness or infinitude
restriction is imposed here.
