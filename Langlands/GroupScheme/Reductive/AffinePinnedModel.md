# Affine pinned models and arbitrary-scheme comparisons

This is an internal bundle of the published affine split-reductive and pinning
interfaces. It introduces no existence assertion. The fields are the same
mathematical data used in `AffinePinnedIsomorphismTheoremStatement`: a reductive
group over a commutative ring, a closed coordinate split maximal torus, a finite
full reduced root datum realized on every field-valued fibre, free rank-one root
Lie spaces, a base, and trivializations of the simple-root Lie spaces. The
fibrewise-root-datum field supplies reducedness. The ring may be the zero ring.

`AffinePinnedModel` includes the ring and both finite index types so that models
on different affine charts can be compared. `base` is the original spectrum.
`groupOver f` is the actual group pulled back along any scheme morphism `f` to
that spectrum. `inclusionOver f` normalizes the pullback of the chosen torus to
the coordinate split torus over the new base, using the published
`splitTorus.baseChangeIso`. `cocharacterOver f` is the actual cocharacter of the
sum of positive coroots for the chosen base, with that normalized inclusion.
These definitions use `BasedBorelTransport.baseChangeInclusion` and
`BasedBorelTransport.cocharacter` unchanged.

`Comparison f g` means an actual group-scheme isomorphism between the two
pullbacks to the same arbitrary scheme. The models need not have the same
original ring, coordinate index type, or root index type. No connectedness or
affineness is required of the common scheme.

`pullComparison e q` pulls an actual comparison back along `q` and composes with
the published `baseChangeCompIso` on each endpoint. Its source and target are the
direct pullbacks along the composite maps. The three accompanying identities
state that this construction preserves identity comparisons, composition, and
inverse comparisons. The proofs use functoriality of base change and cancel the
endpoint comparison isomorphisms.

The provenance is internal: the model merely bundles the hypotheses of existing
Library statements, and the comparison construction is a composite of published
base-change isomorphisms. It neither chooses a comparison nor constructs a
pinning, an outer automorphism, a descent datum, or a quasi-split inner form.
