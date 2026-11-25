# Structural inputs to reductive Kottwitz descent

This companion to `ReductiveMapExistenceReduction` develops parts of
the structural reduction for the existence and z-extension independence of the
reductive Kottwitz map. It does not assert the unconditional
`ReductiveKottwitzExistenceStatement`. The provenance is the factorization
argument of Kaletha–Prasad (2023), Lemma 11.5.1, printed p. 430 / PDF p. 461,
source `kaletha-prasad-2023-bruhat-tits-new-approach`, together with internal
consequences of the existing Library definitions.

`hasSimplyConnectedDerivedGroup_of_commutative` uses the published actual
trivial derived-cover construction for a commutative connected reductive
group. Its derived representative is the identity subgroup and its source
is the actual trivial simply connected group.

`fundamentalGroupMap_zero_of_mapStatement` assumes the algebraic
fundamental-group map statement. For the trivial group-scheme morphism,
the zero torus morphism is a geometric torus factorization. The defining
representative law and surjectivity of the cocharacter quotient show that
the selected map is zero. `fundamentalInertiaMap_zero_of_statements` then
assumes the inertia-map statement, uses its law on quotient representatives,
and obtains the zero inertia map from surjectivity of the inertia projection.

`zExtension_inclusion_projection` proves that the actual central-torus
inclusion followed by the projection is trivial, using the full kernel
equality in the definition of a z-extension on every test scheme.

`zExtensionKottwitzComposite_kills_kernel` assumes the two map statements
and naturality of the simply-connected-derived Kottwitz maps. It uses the
commutative case above to apply naturality to the central torus inclusion.
Composition of inertia maps identifies the resulting composite with the
map induced by the trivial morphism. The zero-morphism law makes it vanish.
The kernel/image equivalence in the companion reduction then proves the
kernel inclusion required for descent. Thus no separate kernel-vanishing
premise is needed once these named naturality and functoriality inputs are
available. This lemma retains those inputs as explicit assumptions.

`reductiveKottwitzExistenceAt_of_naturality` supplies this proved kernel
inclusion to the companion construction. Its explicit inputs are the
algebraic fundamental-group map statement, the simply-connected-derived
Kottwitz statement, the inertia-map statement, naturality between groups
with simply connected derived subgroup, nonemptiness of z-extensions,
point and inertia surjectivity, and common domination. It concludes every
conjunct of the existence statement at a fixed group. It does not
assume a separate kernel-vanishing condition. The outstanding
inputs remain explicit assumptions of this lemma. The companion
`ReductiveMapTorusReduction` supplies several of them from published proofs,
and `ReductiveMapRemainingInputs` packages the final four-premise reduction.
