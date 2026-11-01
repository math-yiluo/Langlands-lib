# Coefficient and support adapters for the last-entry-one expansion

Author: Worker 186.

These are internal adapters to the published coefficient model and
simple-root support statement. The support proposition is an explicit
hypothesis of the general support adapters in this module.
`rootCoefficientSpace_hasCoordinateUpperSupport` in `LastEntryOneGerms`
discharges it with the published `Whittaker.smoothSimpleRootSupport` theorem.

`torus_eq_diagonalUnits` compares the two actual diagonal homomorphisms by
equality of their underlying matrices. `continuous_torus` checks continuity
of the underlying matrix and inverse matrix using the topology on units.

`rootLiftHom` packages the cumulative-product section as a group
homomorphism. Its multiplicativity and identity laws follow from the inverse
identities in `LastEntryOneAssembly`: the product of two last-entry-one
diagonals still has last entry one, and its roots are the products of the
roots. Its continuity follows by composing the published continuous
cumulative-product coordinate map with extension by a final entry one.

`rootCoefficientMap` restricts an actual matrix coefficient to that
homomorphism and proves compatibility with right translation directly from
the representation multiplication law. `rootCoefficientSpace` is its
actual invariant image. To prove this image smooth, first pull the original
smooth representation back along the continuous diagonal homomorphism,
then pass each vector's fixing open subgroup through the coefficient map.
This uses no assertion that the original representation is isomorphic to
its coefficient image and no finite generation over the root-torus group
algebra.

`rootCoefficientMap_apply` gives the literal coefficient evaluation formula.
`rootCoefficientSpace_locallyConstant` separately proves that each image
function is locally constant: choose a preimage vector, pull smoothness back
to the root torus, apply `Hecke.orbitMap_locallyConstant`, and compose with
the algebraic functional. The carrier needs no topology. This establishes
the locally constant function interpretation as well as smoothness of the
function-space representation.

`model_finite` turns the published surjective coefficient intertwiner into a
linear map over the group algebra using Mathlib's
`IntertwiningMap.equivLinearMapAsModule`. Finite generation passes through
this surjection. There is no irreducibility requirement and the image need
not be isomorphic to the original representation.

`model_admissible` uses the published admissibility theorem for surjective
intertwiners in `Unramified.SphericalExistence`. Its compact-open-subgroup
cofinality hypothesis is supplied by that namespace's theorem for the
canonical topology of `GL_(n+1)(F)`. The coefficient map is surjective onto
its actual image, so no quotient identification is assumed.

`upper_support_of_statement` bundles the raw continuous nontrivial unit-norm
additive character and the raw entrywise equivariant functional using
`mem_glFunctionals_of_raw`. It applies the support proposition to the image
of the chosen vector, sets the integral factor to the identity, and compares
the diagonal homomorphisms. The contrapositive gives vanishing whenever a
simple root exceeds the bound. The single positive bound is chosen before
the diagonal and root index; all other diagonal entries remain unrestricted.
The supplied topology may in particular be the canonical one used by the
parent statement. Rank `n = 0` is retained, with the final root quantifier
vacuous.

`rootCoefficientSpace_upper_support` applies that raw bound to a preimage
vector of an arbitrary root coefficient function. Evaluating the bound at
`rootLift x` and using `rootHom_rootLift` yields vanishing when any coordinate
of `x` exceeds the same positive bound. The bound is chosen before both the
coordinate index and all coordinate values, and places no restrictions on
the remaining coordinates. This conclusion remains conditional on the
published support proposition.

The motivation is the upper-support and coefficient-image reduction in
JPS (1979), Proposition 2.2 and Remark 2.2.5, printed pages 181–183,
registered source `jps-1979-gl3-i`. These adapters are derived internal
constructions rather than separate claims quoted from that source. Their
mathematical dependencies are the exact published modules named above;
`LastEntryOneAsymptoticProof` applies the published function-space
decomposition after the germ and support bridges have supplied its hypotheses.
