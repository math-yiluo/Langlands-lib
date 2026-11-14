# Cup creation and the one-cocycle class

This internal construction extends `CechCreationDescent`. It proves that its
additive homology operator depends only on the class of the creating
one-cocycle, for every natural-number degree. It does not impose a
characteristic restriction.

The generic lemma `creationHomologyMap_eq_of_homotopy` concerns two
natural-number cochain complexes `K` and `Q` in an arbitrary preadditive
category. Suppose two degree-raising families `c` and `c'` anticommute with
the differentials, as required by `creationHomologyMap`. If degree-zero
maps `h` satisfy

`c n = h n ≫ Q.d n (n + 1) - K.d n (n + 1) ≫ h (n + 1) + c' n`,

then their induced homology maps agree. Homology existence is required
only in source degree `n` and target degree `n + 1`.

The implemented proof precomposes with the epimorphism from cycles to
homology and postcomposes with the monomorphism from homology to
opcycles. Mathlib's `ShortComplex.π_homologyMap_ι` identifies the resulting
map with cycle inclusion, the middle cochain component, and projection to
opcycles. The two homotopy terms vanish because the differential kills
cycles and is killed by projection to opcycles. This argument also applies
in degree zero.

For a scheme `X` over `Spec R`, `cupZeroAddHom` packages multiplication by
an actual zero-cochain as an additive endomorphism of the ordered Čech
cochain groups. Its underlying function is the existing `cup₀`, which
multiplies the cochain by the zero-cochain restricted from the initial
vertex. The index type has an independent universe; no finiteness,
covering or affine hypothesis is needed.

The specialization `cup₁HomologyMap_eq_of_sub_eq_d` uses the same section
algebras as `CechCreationDescent`: their algebra maps are explicitly
identified with the maps induced by the structure morphism. If actual
one-cocycles `z` and `z'` satisfy `z - z' = d h` for a zero-cochain `h`,
then `cup₁HomologyMap` for `z` and `z'` agrees in every degree. The proof
applies the generic lemma with homotopy `cupZeroAddHom h`. The previously
proved Leibniz identity `d_cup₀` gives precisely the required equation on
cochain components, with both minus signs as displayed above.

The provenance is entirely internal: the construction uses the existing
Alexander–Whitney products and their Leibniz identity, and Mathlib's
short-complex homology maps. No additional literature assertion is made.
The result is equality of additive ordered Čech homology morphisms. It
constructs neither a scalar-linear map on derived sheaf cohomology nor the
geometric creation-contraction relations, exterior generation, or the host
exterior/coproduct comparison.
