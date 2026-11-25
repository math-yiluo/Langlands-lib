# Closed parabolic orbits of attracted rational points

Over any commutative ring, `cocharacterParabolicOrbitMap` defines the actual
orbit morphism from the existing dynamic parabolic scheme to the acted-on
scheme. It is the composite of `parabolicHom χ` with the original action's
orbit morphism at the supplied rational section. This reusable morphism is the
one used in the closedness assertions below.

Let `k` be any field, let `H` be an affine group scheme over `Spec k`, let `X`
be an affine relative scheme, let `a` be a supplied actual action of `H` on `X`,
and let `χ : Gm → H` be an actual cocharacter. Assume that `H` and `X` are smooth
over `k`, and that the actual action relation `(h,x) ↦ (h • x,x)` is smooth.
For every rational section `x` whose actual cocharacter orbit extends over the
affine line, the range of

`(Dynamic.Affine.parabolicHom χ).hom.hom ≫ a.orbitMap x`

is closed in the underlying topological space of `X`. This is the assertion of
`isClosed_range_parabolic_orbitMap_of_isAttracted`. The acting group is the
existing actual dynamic parabolic scheme, and the orbit morphism is the original
action's orbit restricted along its actual inclusion. The corollary
`isClosed_range_parabolic_orbitMap_of_isFixed` applies this conclusion whenever
`x` is fixed by the restricted cocharacter action on all relative refinements.
The statements hold in every universe and characteristic. They impose no
algebraic-closedness, regularity or nontriviality condition on `k` or `χ`.

The helper `cocharacterAttractingAction_orbitMap_comp` works over any commutative
ring: the orbit of a rational section of the actual attracting scheme,
followed by the attracting inclusion, equals the original orbit of its included
section restricted to the actual parabolic. It follows directly from the
all-test identity for the factored action.

This is an internal consequence of the earlier actual attracting-action and
smooth-relation constructions. The all-relative-test representing property
lifts `x` to a rational section `y` of the attracting scheme. Smoothness of the
original relation transfers to the actual parabolic action relation on that
scheme. The published theorem `SchemeAction.isClosed_range_orbitMap` therefore
makes the parabolic orbit of `y` closed there. The attracting inclusion into
`X` is a closed immersion, hence maps this closed orbit to a closed subset of
`X`. The helper identity identifies that image with the stated range of the
original parabolic orbit morphism.

No external source result is newly asserted. This module proves a topological
closed-orbit conclusion under the stated smoothness and affineness hypotheses;
it does not construct an affine reductive homogeneous quotient, prove a closed
product in a general linear group, or prove `DynamicQuotientProperStatement`.
