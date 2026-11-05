# Simultaneous smooth models of a supplied closed homomorphism

This internal construction combines actual smooth affine model existence,
arithmetic extension of a supplied homomorphism, and eventual closedness of
that same extending map. All coefficient rings and schemes lie in the arbitrary
common universe `u`.

`SmoothClosedHomModels R K f` contains actual integral models of the source and
target of the supplied generic homomorphism `f`, smoothness of both structural
maps, an actual `IntegralModel.Hom` indexed by `f`, and closedness of its
underlying scheme morphism. The inherited model fields provide affineness,
flatness, local finite type and specified generic-fibre isomorphisms.
The Hom includes the compatibility equality with those same isomorphisms and
the original `f`.

For a number field `F`, two supplied smooth affine groups over `Spec F`, and a
supplied closed homomorphism between them,
`ArithmeticSpreading.exists_smooth_closedHomModels` gives these simultaneous
data over one actual finite S-integer ring. The proof first constructs smooth
models separately using `exists_smoothIntegralModel`. Their two finite sets
are replaced by their union, and `enlargeModel` pulls the models to this common
base. `smooth_enlargeModel` preserves their smoothness. Smoothness of the
target supplies the local finite presentation needed by `enlargedHomData`,
which gives a further finite enlargement and an extending Hom between the
canonical pullbacks. Finally, `enlargedClosedHomData` supplies one more finite
enlargement on which `enlargeHom` of this same Hom is closed. Smoothness
persists through both further pullbacks. These actual final models and the
specified closed extending Hom fill every field of `SmoothClosedHomModels`.

`SmoothClosedHomModelData` packages the finite set and these simultaneous
models. `smoothClosedHomModelData` chooses them from the proved existence
theorem.

`smoothClosedHomModelData_of_parabolic` applies the construction directly to
the original generic hypotheses of simultaneous reductive and parabolic
spreading. The current connected-reductive predicate supplies smoothness and
affineness of the ambient group. The current parabolic predicate supplies
smoothness of its source and closedness of the supplied inclusion. Composition
of that closed immersion with the affine ambient structural map makes the
source structural map affine. Thus no additional generic hypothesis is needed
for this smooth closed model construction.

This unit proves the simultaneous model, smoothness and closed-extension part
of the full spreading target. It establishes no reductivity of the integral
ambient group and no reductive, parabolic or connectedness condition on all
field-valued fibres. Those remain separate obligations of the unchanged
`ReductiveParabolicSpreading.ExistenceStatement`.
