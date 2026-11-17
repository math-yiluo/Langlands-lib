# Negative simple-root cell relations with an arbitrary target

This internal derived reduction generalizes the published negative simple-root
cell argument. The source retains its genuine normalized simple-root data over
a local coefficient ring and an affine structure morphism. Target inputs are
map-level `TargetWordRelations`, common Weyl-conjugation units, exact
`TargetNegSimpleLaws`, and an arbitrary map from the same coordinate torus.
No target reductivity, torus maximality, closed inclusion, cell openness or
root-parametrization property is used.

The rank-one target fields use the source coroot and its actual cocharacter
points. The negative-simple character field uses the source root character
and its exact scalar. These requirements retain the literal scalars needed
for the two cell computations to have identical coordinates.

Common polynomial commutators for every source base give positive-good root
pairs. Their all-test identities specialize to each local test ring. Applying
the same construction to the opposite base gives transfer for arbitrary
ordered products of negative roots. These two parts reuse the published source
cell geometry and the arbitrary-target commutator reduction.

The remaining copied wrappers split off a simple positive factor, conjugate
the other factors by its opposite map, and transfer the cell relation. Target
rank-one conjugation and the unit-denominator law provide its rank-one steps;
the character field provides its torus step. All cell injectivity and ordered
product cancellation concern the source. In the nonunit branch, passing to
the residue field contradicts the source Weyl-cell geometry. No target
geometric property is introduced in that branch.

`LocalSplitTargetNegSimpleStatement` states this conditional reduction in
every universe. It also retains the source rank-one Bruhat laws and a
height-monotone positive-root enumeration. `localSplitTargetNegSimple`
proves it. Actual powered-family instantiation and ambient isogeny
construction remain separate.
