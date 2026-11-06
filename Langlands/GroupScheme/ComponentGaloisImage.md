# The finite coefficient image on actual scheme components

Author: Worker 1107.

This is an internal derived construction over the published
`AlgebraicallyClosedComponents` module. Its group carrier is the actual space of
connected components of the underlying scheme, with the existing quotient
topology. No external structural theorem is used.

For a group scheme `H` over a field `k : Type u`,
`allComponentTopologicalSpace` inherits the existing connected-component quotient
topology on the published type synonym. `allComponentT1Space` proves
that this topology is T1: the inverse image of a singleton under the
quotient map is a connected component, which is closed. If `k` is algebraically
closed and `H` is smooth affine, published finiteness then makes that same
topology discrete. No replacement topology on the component carrier is chosen.
`componentPointRepresentative` chooses an actual rational section in each
component using the published surjectivity theorem, and its component formula
is proved.

Let `k` be any field, `L` an algebraically closed extension in the same arbitrary
universe, and `H` smooth affine over `k`. The extension may have any
characteristic and is not required to be algebraic, separable or normal.
`componentGaloisKernel` is the kernel of the published homomorphism from
`Aut_k(L)` to automorphisms of the full component group of `H_L`.
Its membership theorem identifies it with those automorphisms whose actual
semilinear scheme-component maps fix every component. An equivalent finite
family of tests uses the actual coefficient conjugates of the chosen rational
representatives; equality of components, rather than equality of sections,
is required.

`ComponentGaloisImage` is the actual range of this homomorphism. It is finite
because its elements inject into functions from the finite component carrier to
itself. This new image carrier is equipped with the discrete topology.
`componentGaloisProjection` is the canonical surjective group homomorphism to
the image, and `componentGaloisImageAction` is its faithful inclusion into group
automorphisms. Composing these two maps gives the original coefficient action.
On every actual component its value is exactly `coefficientComponents`, so the
factorization retains the published comparison with actual semilinear scheme
maps.

`componentGaloisQuotientEquiv` is Mathlib's first-isomorphism equivalence between
the ordinary abstract quotient `Aut_k(L)/componentGaloisKernel` and this finite
image. Its formula on quotient classes is the image projection. Consequently
the quotient is finite and the normal kernel has finite index.
`componentGaloisQuotientAction` is the corresponding faithful action of this
ordinary finite quotient. The published full fixed subgroup consists precisely
of those components fixed by all elements of the finite image.

These are intrinsic laws of the finite image, kernel and quotient constructions.
This module asserts no Krull continuity or openness of the kernel, and identifies
no intermediate field or finite Galois splitting extension. The ordinary group
quotient is not assigned a topology here. No fixed-component descent,
component-group scheme or sheaf quotient is constructed. In particular, finite
index alone is not used to infer openness in a profinite group.
