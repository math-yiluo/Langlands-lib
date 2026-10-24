# Central shifts and strict descent of fixed-vector dimensions

Worker 196 authored this module. Worker 283 submits it, unchanged, as the
ancillary helper of the proof of
`Langlands.CuspidalSupport.FixedVectorConstituentInduction` in
`Langlands.Representation.CuspidalSupport.ConstituentInduction`.

This internal proof unit implements the central-operator step in
Bernstein–Zelevinsky, *Representations of the group GL(n,F) where F is a
non-archimedean local field (survey)* (1976), Proposition 3.30, proof step
(3), printed/PDF page 37. The registered source is
`bernstein-zelevinsky-1976-representations-gln`. It does not prove the full
constituent theorem.

For an actual smooth representation `A`, a central group element `z`, and
a scalar `c`, `centralShift A z c` is the actual intertwiner whose underlying
linear map sends `v` to `A(z)v - c v`. The first lemmas prove its evaluation
formula (`centralShift_apply`), its naturality under every intertwiner
(`centralShift_natural`), and its vanishing criterion
(`centralShift_eq_zero_iff`). These constructions work over an arbitrary field
and independent group and carrier universes.
`fixedVectors_generate_of_subgroup` shows that if the `K`-fixed vectors
generate the restriction of `A` to a subgroup `H`, they also generate `A`
under the full group: an invariant subspace for `G` is invariant for `H`.

Over the complex numbers, suppose that the ambient space of vectors fixed by
a compact open subgroup `K` is finite dimensional, that an actual subquotient
`D` has nonzero `K`-fixed vectors, and that `z` acts on `D` by `c`.
`centralShift_not_injective_fixedVectorsMap` proves that the shift on `A^K` is
not injective: naturality carries the shift along the subquotient presentation,
where it is zero on `D`, and the published fixed-vector witness lemma
`not_injective_fixedVectorsMap_of_subquotient_witness` (which uses compact
averaging for surjectivity on fixed vectors) concludes.

`centralShift_fixedVectors_descent` assumes in addition that `A^K` generates
the restriction of `A` to `H` and that `z` does not act on `A` by `c`. By the
generation lemma and `intertwiner_eq_zero_of_fixedVectorsMap_eq_zero`, the
shift is then nonzero on `A^K`. The published inequalities
`finrank_fixedVectors_kernel_lt`, `finrank_fixedVectors_image_lt` and
`finrank_fixedVectors_cokernel_lt` give strict decrease of the `K`-fixed
dimension for its actual kernel, image and cokernel. No finite dimensionality
of `A`, semisimplicity, or irreducibility is assumed by these lemmas. The
constituent induction obtains scalar action on the irreducible admissible `D`
from Schur's lemma and supplies the generation hypothesis separately.
