# A separable cubic field fixing a D4 leaf

This internal construction defines the field of definition of an individual
actual simple vertex under the full absolute Galois star action. It then proves
that this field has degree three for every leaf of a type-D4 diagram with no
globally fixed leaf. No locality, simple connectedness or split-rank assumption
is needed.

For actual `d : TitsIndexData G` over a field `K`,
`starVertexStabilizer a` is the subgroup of
`SeparableClosure K ≃ₐ[K] SeparableClosure K` consisting exactly of the
elements whose star action fixes `a`. It contains the existing `starKernel`,
which is open by the published star-action continuity theorem. The stabilizer
is consequently open and closed. The actual intermediate field
`starVertexField a` is its fixed field inside `SeparableClosure K`.

The infinite Galois correspondence gives the exact equality between the
fixing subgroup of this field and the original vertex stabilizer.
`fixes_starVertexField_iff` therefore says, for every full absolute Galois
element `σ`, that fixing the field pointwise is equivalent to
`d.star σ a = a`. `finrank_starVertexField` identifies the field's degree
with the subgroup index. Its separability follows from its inclusion in the
separable closure.

For a full type-D4 numbering `e : d.Vertex ≃ Fin 4`, the hypothesis is
absence of a leaf fixed simultaneously by every full Galois element. The
published `star_transitive_on_D4_leaves_of_no_fixed_leaf` shows that the
orbit of any leaf consists of all three leaves. The center, numbered one,
is always fixed; bijectivity of each star permutation prevents a leaf from
mapping to it. The proof supplies the actual star action as a local
`MulAction`, applies orbit–stabilizer, and counts the complement of the
center in `Fin 4`. Thus the leaf stabilizer has index three and its fixed
field has degree three. Positive finite degree supplies finite dimensionality.

`exists_cubic_leafField_of_D4_no_fixed_leaf` packages the actual intermediate
field, finite dimensionality, separability, exact degree three, and the
pointwise-fixer equivalence for the specified original leaf. It does not
assert that the cubic extension is Galois or cyclic. The field characteristic
and universe parameter are unrestricted.

The provenance is internal composition of the published full star-action
continuity, infinite Galois correspondence, and D4 leaf-orbit theorem. This
does not construct a Tits index after field extension, prove preservation
of split rank or anisotropy under this cubic extension, or exclude a local
trialitarian index. Those geometric and arithmetic steps remain necessary
for the unconditional local rank-one enumeration.
