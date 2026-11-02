# Rank-one reflection for actual module stalks

This internal construction works with schemes in an arbitrary universe `u`,
actual module sheaves, their actual stalks, and the canonical local-ring actions.
It imposes no noetherian condition.

`finitePresentation_stalk` proves that every actual stalk of a locally
finitely presented module sheaf is finitely presented over its actual local
ring. It chooses a spectrum chart with finitely presented actual sections,
uses the affine stalk theorem, restricts scalars along the canonical
isomorphism of local rings, and transports along the actual linear
restriction-stalk equivalence.

`stalkRankOneEquivOfMem` starts with membership in the rank-one locus.
It chooses an actual trivialization on an open neighbourhood, applies its
linear stalk equivalence and the unit-stalk comparison, then transports
back across the open immersion. It does not assert that this choice is
canonical.

For `stalkRankOneEquivOfFiberwiseFlatPullback`, let `q : Y ⟶ S` be locally
of finite presentation and let `M` be locally finitely presented on `Y`
and flat over `S` in the actual relative-stalk sense. Let `p : X ⟶ Y`
and `x : X`. Choose pullback squares defining the fibres of `p ≫ q` and
`q` over `Spec κ(q(p(x)))`. A map between these fibres must commute with
both projections and must be flat. Given an equivalence from the actual
stalk of the ordinary pullback `p* M` at `x` to the actual local ring of
`X` at `x`, the construction returns an equivalence from the original
stalk of `M` at `p(x)` to the actual local ring of `Y` at `p(x)`.
Both equivalences are linear over their respective actual local rings.

The implemented argument installs the algebra structures of the actual
stalk maps. Essential finite presentation of the first local-ring map
comes from `stalkEssFinitePresentation`, and finite presentation of the
module stalk comes from the first lemma above. Relative stalk flatness
supplies flatness over the base local ring. `flat_fiber_stalk` converts
the geometric fibre-map flatness into flatness of the inclusion from the
original residue tensor ring to its scalar extension. The ordinary
pullback-stalk tensor comparison converts the supplied equivalence into
the input for `linearEquivOfFiberwiseFlatBaseChange`, which gives the
claimed original-stalk equivalence.

The provenance is the composition of these existing actual-stalk,
finite-presentation, fibre-flatness and local-algebra interfaces. No new
literature assertion is introduced. No compatibility with the input
basis is asserted. This construction leaves the verification of
fibre-map flatness in an arbitrary cartesian base change, the resulting
rank-one-locus equality, and the Picard atlas theorem as separate obligations.
