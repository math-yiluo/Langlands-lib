# Maximal-torus reflection through a finite homomorphism

`Langlands.GroupScheme.IsMaximalTorus.of_finiteHom` concerns a finite
homomorphism `π : G ⟶ H` over an arbitrary field. The source is affine and
the target is smooth affine. Suppose a closed torus `j : T ⟶ G` fits in
`j ≫ π = f ≫ i`, where `i : S ⟶ H` is a maximal torus and the underlying
scheme morphism of `f : T ⟶ S` is surjective. Then `j` is maximal.
No reductivity or connectedness of either ambient group is assumed, and
the source need not be smooth. The map `f` need not be separable.

This is a derived generalization of the Library's
`finiteHomMaximalTorusReflection_of_torusImage` in
`Torus/FiniteHomMaximalityReduction.lean`. The earlier result assumes both
ambient groups are connected reductive and takes the closed-torus image
statement as a premise. The present proof uses its published proof,
`torusImageClosedTorusStatement`, and retains only the hypotheses actually
needed for the argument.

If `T` factors through a closed torus `M` in `G`, take a closed torus
factorization of `M ⟶ H`. Schematic dominance of `T ⟶ S` implies that
`S` factors through this image torus. Maximality of `S` identifies that
factor with an isomorphism. Thus `M` has a finite morphism to `S`, with
schematically dominant restriction to `T`. Integral incomparability,
implemented in
`isIso_of_closedImmersion_finite_comp_schematic`, makes `T ⟶ M`
an isomorphism. This is precisely the maximality condition.

This lemma does not construct lifts of tori or prove the isogeny
reduction or Cartan generation statements.

`FiniteHomMaximalTorusReflectionSmoothStatement` packages the assertion as
a universe-general proposition. The theorem
`finiteHomMaximalTorusReflectionSmoothStatement` proves it using
`IsMaximalTorus.of_finiteHom`.
