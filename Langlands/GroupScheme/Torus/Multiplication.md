# Nonzero multiplication on an arbitrary torus

`TorusMultiplicationStatement.{u}` says that for every field `k : Type u`,
every actual commutative group scheme `T` satisfying `IsTorus T.toGrp`,
and every nonzero integer `n`, the actual multiplication morphism `[n]`
is flat and surjective on underlying schemes.
`torusMultiplicationStatement` proves this proposition.
`IsTorus.flat_and_surjective_multiplication` provides its direct interface.

The statement includes nonsplit tori, imperfect fields, positive
characteristic and the rank-zero torus. It does not require that `n` be
invertible in `k`, and makes no smoothness or separability claim about
the multiplication morphism.

## Derived provenance and implemented proof

This is a derived consequence of the published split multiplication and
base-change interfaces, with no external source assertion added.
`IsTorus.splittingExtension` chooses a field extension in the same
universe over which the given actual torus is split. The extension
morphism of spectra is faithfully flat and quasi-compact by
`fieldExtension_fpqc`.

`IsSplitTorus.flat_and_surjective_multiplication` proves both properties
of multiplication on the split torus after that extension.
`multiplication_baseChange` identifies this morphism with the base
change of the original multiplication. The square supplied by
`baseChange_map_isPullback` has as its target projection a base change
of the faithfully flat, quasi-compact extension. Flatness and
surjectivity therefore descend through that square by
`MorphismProperty.of_isPullback_of_descendsAlong`.

This result supplies a geometric input to torus lifting through
central isogenies. It does not itself construct a lift or prove the
Cartan-generation theorem.
