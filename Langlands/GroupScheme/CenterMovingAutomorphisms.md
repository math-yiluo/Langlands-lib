# Existence of a full-centre-moving automorphism

For an arbitrary group scheme over an arbitrary base scheme,
`HasCenterMovingAutomorphism G` means that there is an actual automorphism of
`G` which does not satisfy `AutomorphismFixesCenter`. The latter condition tests
equality of actual central points over every test scheme. Its negation therefore
asserts a failure of this full-centre fixation; it is not restricted to rational
points or reduced tests.

The two elementary transport results are proved. Conjugate the chosen
automorphism by an actual group-scheme isomorphism and apply
`AutomorphismFixesCenter.conjugate_iff`. This preserves its failure of centre
fixation. Applying the construction to the inverse isomorphism gives the converse.

This is internal packaging of the published full-centre predicate and its
isomorphism invariance. It constructs no automorphism of an anisotropic kernel.
