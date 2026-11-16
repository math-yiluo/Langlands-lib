# Uniqueness of supplied universal maximal-torus families

Worker 235.

This is an internal construction from the Library's actual subgroup-family
evaluation and its `IsUniversalMaximal` predicate. Its provenance is the
uniqueness argument for representing objects, applied to the all-test
universal properties already formalized in `MaximalModuliRestriction`.
It asserts no existence or quasi-affineness of a maximal-torus parameter
scheme.

`isFibrewiseMaximalTorus_familyHom` assumes the original ambient group
is smooth and affine. It transports fibrewise maximality first through
base change and then through the canonical comparison with the direct
ambient pullback.

`IsUniversalMaximal.evaluate_injective` additionally assumes the universal
family is a closed relative torus and fibrewise maximal. Given two
parameter maps with equal actual subgroup functors, universality applied
to the evaluated torus forces both maps to be its unique classifier.

`universalMaximalIso` compares two supplied families satisfying those same
conditions over the same smooth affine ambient group. Each universal
property classifies the other family. Composition of evaluation, its
invariance under equality of actual subgroup ranges, and injectivity
show that the resulting maps are inverse. The result is an isomorphism
of parameter schemes over the base.

`quasiAffineOver_of_iso` needs only an isomorphism of schemes over a base.
Above each affine open of that base it restricts the isomorphism and
uses Mathlib's preservation of quasi-affineness under affine morphisms.
The conclusion uses Mathlib's quasi-affine scheme predicate, including
its quasi-compactness convention.
