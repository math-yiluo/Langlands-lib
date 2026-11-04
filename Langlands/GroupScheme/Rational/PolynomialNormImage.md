# Nontrivial central split images of Galois norms

This internal construction combines the actual central norm with nonzero
base-field differential with the published homomorphism-image and
split-unipotent surjective-image theorems. It produces a nontrivial smooth
connected affine central split subgroup over the ground field. Every field
and characteristic is retained, including finite and imperfect fields.

## Centrality through a flat surjective map

`IsCentral.of_flat_surjective_precomp` works over any scheme base. For a
flat surjective homomorphism `p : A → H`, if `p` followed by `i : H → G` is
central, then `i` is central in the existing full-center sense.

For each test point `x : T → H`, pull back `p` along `x`. The resulting
flat surjective test cover `v : V → T` has a tautological lift `y : V → A`
satisfying `v x = y p`. Centrality of the composite puts `v x i` in the
full center. The existing `mem_center_of_flat_surjective` reflects that
membership back to `T`. Its conclusion quantifies over all refinements
of each test scheme, as required by `IsCentral`.

## The retained image

For `q : A → G` over a field, `CentralSplitImage q` retains:

- an actual image group scheme `D`, a closed inclusion `i : D → G`, and
  a projection `p : A → D` with `p i = q`;
- affineness, smoothness and connectedness of `D`;
- flatness, surjectivity, quasi-compactness and local finite presentation
  of the projection;
- full centrality of the inclusion and split unipotence of `D` in the
  existing finite represented Ga-series convention;
- an actual nonidentity identity-kernel point of `D` over `k[ε]`, and
  nontriviality of the all-test subgroup functor `range i`.

`centralSplitImageOfNonzeroDifferential` constructs this structure when
`A` is smooth, connected, affine and split unipotent, `G` is affine and
locally of finite type, `q` is central, and `Lie.targetMapLinear q k ≠ 0`.
It chooses the factorization from `HomImage.exists_image`. The preceding
centrality lemma applies to its flat surjective projection. The theorem
`IsSplitUnipotent.of_surjective_to_smooth_affine` makes the image split.

A nonzero differential has a tangent `x` on which its value is nonzero.
The image of `x` under the projection is a nonidentity tangent of `D`:
otherwise postcomposition with the inclusion would make the original
value zero. If `range i` were bottom, the underlying dual-number point
of this tangent would become the identity after inclusion. The closed
inclusion is monomorphic, so the tangent itself would be the identity,
a contradiction. This proves nontriviality on all tests rather than
assuming surjectivity on rational points.

`CentralSplitImage.dimension_pos` proves positive actual Lie dimension
of the retained image. Its smooth affine geometry gives finite
dimensionality of the actual Lie kernel, and the retained nonidentity
tangent gives a nonzero vector in that kernel. The standard finite-rank
criterion therefore yields `0 < Lie.dimension D`.

## Applying the construction to the norm

`centralSplitImageOfCentralHom` takes an affine locally finite-type group
`G/k`, a finite Galois extension `L/k`, and a central monomorphism
`f : G_a,L^n → G_L` with `n > 0`. It applies
`nonzeroNormOfCentralHom` to obtain an actual central base-field norm
`q : G_a,k^n → G` with nonzero differential. Natural coordinates on the
standard vector group supply its affine, smooth, connected and split
properties. The general construction then returns `CentralSplitImage q`.

The image need not be a vector group, and no claim that subgroups of split
unipotent groups split is used. Instead splitness comes from the actual
smooth affine surjective image of a vector group. The ambient group `G`
need not be smooth, connected or unipotent. This module does not yet
perform quotient dimension induction or prove finite-Galois descent of
split unipotence or maximal-torus conjugacy. Its provenance is the explicit
composition of the imported published constructions and the elementary
pullback, cancellation and finite-rank arguments described above.
