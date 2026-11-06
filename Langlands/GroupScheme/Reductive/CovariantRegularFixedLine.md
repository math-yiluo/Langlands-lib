# Fixed lines in the actual finite regular representation

This internal derived construction transfers the fixed-function result in
`CovariantCellFixedLine` to the existing actual
`Chevalley.affineRegularRepresentation`. Let `G` be affine over a field
`k : Type u`, and supply a regular subspace `V` of its coordinate algebra,
a finite basis `b`, and stability under every coalgebra right action.
No external theorem is invoked.

`affineRegularCoordinateMap` sends a vector to its basis combination in
the actual coordinate algebra. It is an injective linear map with image
in `V`. The evaluation formula
`pointAlgebraHom_affineRegularCoordinateMap_mul` expands evaluation
after right multiplication into the existing regular representation
matrix acting on the scalar-extended vector. The proof expands the
finite basis formula, interchanges finite sums and collects the matrix
coefficients.

`affineRegularCoordinateMap_mem_rightInvariant_of_fixedVector` shows
that a vector fixed by the representation restricted through an actual
morphism `j : U → G` gives a function invariant under right multiplication
through `j`, on every original relative scheme test. It applies the
evaluation formula to the fixed-vector equation. The source `U` need
not be affine or unipotent.

For `affineRegularRepresentation_fixedSubmodule_eq_span`, additionally
supply a morphism `i : H → G` from an affine group, a coordinate `χ` on
`H`, and containment of `V` in the entire left-covariant subspace.
Supply a nonzerodivisor cell coordinate `q` and an actual factorization
`g = i(a) j(u)` whenever `q(g)` is a unit on any relative scheme.
Finally supply a vector `v` fixed through `j` whose represented
coordinate has counit one.

Every fixed vector then gives an invariant covariant coordinate. The
geometric uniqueness theorem makes that coordinate a scalar multiple
of the coordinate represented by `v`. Injectivity of the basis map
recovers the corresponding vector equality. Since `v` is itself
fixed, this identifies the entire fixed submodule with `span k {v}`.
It applies in particular when the supplied `V` is the entire covariant
space and the supplied basis is a basis of that space.

The regular subspace, its finite basis, the dense product factorization
and the normalized fixed vector remain supplied inputs. This module
does not prove finiteness of an entire covariant space, existence of
structural or Steinberg data, orbit spanning, or cofinal irreducibility.
