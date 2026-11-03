# All-test self-normalization from an open cell and geometric points

Authors: Worker 1297, with the geometric assembly direction contributed
by Worker 1346.

This internal unit gives a conditional assembly theorem for actual subgroup
functors over an arbitrary base scheme `S`. Let `iU : U → G` and `iP : P → G`
be group-scheme homomorphisms. Suppose multiplication
`m : U ×_S P → G` is an open immersion, the subgroup `range iU` meets
the all-test normalizer of `range iP` only at the identity, and every
normalizer point over an algebraically closed field, with any map from
that field's spectrum to `S`, belongs to `range iP`. Then
`(range iP).normalizer = range iP` as subgroup functors on every test scheme.
The test schemes may be non-affine and nonreduced.

## Implemented argument

`cellMultiplication`, imported from
[CellMultiplication](CellMultiplication.md), is the actual multiplication
map built from `iU` and `iP`. Its right factor lies in its topological image: use the identity
point in `U` and the given point in `P`.

For any test map `g : T → G` in the normalizer, take a point `t` of `T`
and the spectrum of the algebraic closure of its residue field. The
composite to `G` remains in the normalizer by restriction. The geometric
point hypothesis puts that composite in `range iP`; hence `g(t)` lies
in the multiplication cell. This proves
`range_subset_cell_of_geometric_mem`. It uses no finite-type or
reducedness hypothesis.

An open immersion admits a global lift for every scheme map whose
topological image lies in its image. Apply this property to `g` and
the cell to obtain `g = x y`, with `x ∈ range iU` and `y ∈ range iP`.
Since `range iP` is contained in its own all-test normalizer,
`x = g y⁻¹` is in that normalizer. The separation hypothesis forces
`x = 1`, so `g ∈ range iP`.
This is `mem_range_of_mem_normalizer_of_range_subset_cell`.
Combining the two steps gives `normalizer_eq_of_open_cell`.

If `iP` is also a monomorphism on the underlying relative schemes,
`normalizerPointsEquivOfOpenCell` constructs a multiplicative equivalence
between the normalizer points and the actual points of `P` on each
test scheme. It transports the proved subgroup equality and uses the
published point equivalence for a represented subgroup.
The accompanying `normalizerPointsEquivOfOpenCell_comp` verifies that
this equivalence sends each normalizer point to a lift along `iP`.

## Provenance and remaining scope

The argument is an internal consequence of the existing subgroup
functor definitions, Mathlib's residue-field maps and open-immersion
universal property, and the Library's represented-point equivalence.
No external structural theorem is invoked.

The hypotheses are explicit inputs. This unit does not prove opposite
open-cell existence, geometric pointwise parabolic self-normalization,
or identification of arbitrary parabolics with dynamic parabolics.
Those remain obligations when using this bridge for
`ParabolicSelfNormalizerStatement`.
