# Integral-parameter rigidity for actual actions on Hopf spectra

This internal construction sends a rational specialization `ε : R →ₐ[k] k`
to the associated affine parameter point `specializationSpecMap ε`.
The grouped results concern an actual automorphic action on a commutative
Hopf spectrum whose group-like elements span its coordinate algebra.

If a parameter-valued acting point `s` becomes the identity under this
specialization, the classifying map of its natural convolution family
specializes to the identity. To prove this, equip the original coordinate
algebra with its parameter-algebra structure through `ε`. The corresponding
affine parameter map factors through the specialization point. The acting
point is therefore the identity on this test algebra. Naturality of the
convolution family identifies evaluation of its classifying map with the
identity action. The tensor evaluation agrees with `GroupLike.specialize`.

If `R` is an integral domain, the preceding algebraic rigidity theorem then
makes every member of the convolution family the identity. Transporting
through the actual affine-point equivalence proves that the pullback of `s`
acts trivially on every coefficient `R`-algebra test. All objects share one
arbitrary universe. There is no reducedness or smoothness assumption on the
target Hopf algebra and no finite-dimensionality assumption.

This unit does not yet assert triviality of every point of an arbitrary
smooth connected acting group, nor the geometric centre consequence or the
host semigroup comparison.
