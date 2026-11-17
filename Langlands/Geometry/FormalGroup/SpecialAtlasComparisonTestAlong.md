# Actual test comparisons over supplied target scalars

This internal unit transports an actual special-atlas test comparison through
coefficient extension to an independently supplied target scalar structure.
`baseChangeReAlgebraOriginalTestIso` uses the actual supplied source coefficient
chart isomorphism, the original actual test comparison on the restricted test
transported through the proved test-scalar equality, and the inverse actual
target coefficient chart isomorphism. Both integral inverse maps are retained.

`testIso_baseChangeReAlgebra` eliminates the equality of induced and supplied
base scalars and applies the previously proved coefficient-extension equation
for whole integral test isomorphisms. `baseChangeAlongOriginalTestIso` and
`testIso_baseChangeAlong` specialize this exact construction and equality to
the given algebra homomorphism. Any specified old finer comparison chart can
be used, provided it is invertible on the restricted test. It need not be the
old chart retained by the extended finer comparison.

The local field, finite-dimensional central division algebra and embedded
field hypotheses are those of the supplied actual special atlases.
Coefficient rings have universe `v`, independent of the local-field universe.
Covers may be infinite and coefficient maps may merge generators. All given
finer and outer test chart generators have their actual unit evidence. No
quotient comparison naturality, framed comparison base change or
representability is asserted here.
