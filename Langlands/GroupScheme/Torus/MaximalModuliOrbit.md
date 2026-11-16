# Normalizer orbits in supplied universal maximal-torus moduli

Worker 235.

This internal construction uses the Library's actual conjugate-family API
and the all-test universal maximal-torus property. It assumes a smooth
affine ambient group over an arbitrary base scheme. It assumes both the
supplied universal family and a fixed closed fibrewise maximal relative
torus; it does not construct either one.

`isFibrewiseMaximalTorus_conjugateFamily` pulls back maximality to the
parameter base and transports it through the conjugating inner
isomorphism. `maximalOrbit` classifies the family conjugated by the
universal point of the ambient group. Its evaluation theorem identifies
its value on every test point with the literal actual conjugate subgroup
functor. The proof uses composition of family evaluation, its dependence
only on actual subgroup range, and evaluation of conjugate families.

`maximalOrbit_fibers` identifies equality of orbit parameters on every
test scheme with membership of their right quotient in the full
normalizer subgroup functor. Evaluation injectivity for the universal
family reduces this to the published exact normalizer criterion for
conjugate families, including all refinements of the test scheme.
No scheme quotient or quasi-affineness is concluded by this unit.
