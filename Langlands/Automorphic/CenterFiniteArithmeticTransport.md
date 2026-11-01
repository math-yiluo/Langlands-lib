# Arithmetic pullback on simultaneous adelic center-finite functions

Author: Worker 2.

This internal construction takes actual number fields in independent universes,
an actual field ring isomorphism, and every natural matrix rank, including
zero. The coefficient field is complex and arithmetic pullback fixes values.
The function carriers and differential actions are the existing genuine adelic
objects.

`sliceFamilyEquiv` reindexes the whole smooth slice family along the actual
finite adelic matrix equivalence and pulls each slice back along the actual
infinite matrix map. Its inverse uses the corresponding inverse maps.
It is complex-linear, with identity, contravariant composition and inverse
laws. The actual center action intertwines through the center algebra
equivalence. Injectivity then identifies the common annihilator as the
preimage ideal along this center map.

The whole center-family orbit span is the linear image of the original
orbit span. The range description of that span, center covariance and
surjectivity of center transport prove both inclusions. Restriction gives
`centerFamilyOrbitEquiv`; its linear equivalence preserves and reflects finite
dimensionality. This treats one common orbit of the entire family, preserving
the simultaneous condition and its single common annihilator.

Extraction of all smooth slices commutes with the actual smooth adelic
pullback. Consequently the common annihilator formula and simultaneous center
finiteness equivalence apply to actual adelic functions.
`centerFiniteSmoothEquiv` restricts the existing continuous complex-linear
smooth pullback to the actual simultaneous center-finite subspaces.
Its continuity uses the inherited compact-open subspace topologies.
Evaluation and inverse evaluation are actual arithmetic substitution.
Identity, contravariant composition, inverse and finite adelic action
covariance follow from the existing smooth pullback laws.

For functions with a common open finite stabilizer, faithful extraction of
all smooth slices proves covariance of the genuine adelic enveloping and
center actions. This avoids making a choice of compatible reconstruction
stabilizers. The actual common-stabilizer inclusion commutes with pullback,
so simultaneous center finiteness is preserved and reflected here as well.
`centerFiniteFiniteSmoothEquiv` is the resulting continuous complex-linear
equivalence on the actual center-finite spaces with common finite stabilizers,
with evaluation, inverse evaluation, identity, contravariant composition and
inverse laws. It intertwines the existing restricted center-finite enveloping
action.

Provenance is internal composition of `SmoothArithmeticTransport`,
`ArchimedeanDifferentialTransport`, `CenterFinite`, `EnvelopingAction`, and
`DifferentialCenterFinite`. The range, restriction and finite-dimensionality
arguments are elementary linear algebra. No new original-literature
identification, derivative-topology continuity, growth, cuspidality, or
automorphic occurrence assertion is made.
