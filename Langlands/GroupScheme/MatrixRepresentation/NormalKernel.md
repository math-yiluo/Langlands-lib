# Actual representations with a prescribed normal kernel

For an algebraically closed field `k`, let `G` be an affine group scheme whose
structure morphism is locally of finite type and whose underlying scheme is
reduced. For every closed subgroup `i : H ⟶ G` with normal all-test range,
`nonempty_kernelRepresentation_of_normal_closed` constructs a finite matrix
representation of `G` whose represented kernel has exactly that range.
`normalKernelRepresentation` chooses this actual representation and its full
kernel equality. There is no smoothness or reducedness assumption on `H`.

The equality is one of subgroup functors on every scheme over `Spec k`, including
nonreduced tests. It is stronger than an equality of field-valued point kernels.
The module does not itself construct a quotient or assert its smoothness.

The proof uses the Library's actual Chevalley representation, with `H` the
unit-scalar stabilizer of a coordinate line. The coordinate vector belongs to the
character space of the line's algebraic character. The inverse-character
construction supplies a nonzero vector in another actual ambient representation.
Choosing a nonzero coordinate and dividing by it normalizes that coordinate to
one while preserving the character equation. The pure tensor of these two
vectors is fixed by `H`, since its character factors are mutually inverse.
The existing fixed-tensor construction then takes the `H`-fixed subrepresentation.
A point acting trivially there fixes this tensor and hence preserves its first
line; Chevalley's all-test stabilizer equality places the point in `H`.

Three auxiliary lemmas supply the comparisons used in this argument.
`mem_characterSpace_of_pointwise` transports the all-test character action at the
universal affine point through the relative global-sections algebra equivalence.
`coordinateLine_mem_characterSpace` applies it to the chosen coordinate vector.
`isFixedVector_tensor_of_opposite_characters` proves the pure tensor equation at
the universal affine point using the Kronecker matrix formula and the inverse
character unit, then uses the affine-model criterion to obtain fixedness on all
scheme tests. These three lemmas need only an arbitrary field and an affine group;
they impose neither reducedness nor smoothness on that group or its tests.

This module is an internal derivation from the published Chevalley line
stabilizer, rational characters, universal character spaces, and fixed-tensor
kernel construction. Its only new construction choices are the inverse-character
vector and its coordinate normalization. Reducedness, local finite type and
algebraic closedness of the ambient field are used by the inverse-character
representation helper, not by a restriction on the subgroup or test algebras.
