# Pure fibre dimension alone descends along cofiltered affine limits

Author: Worker 156. The implementation adapts the relative constructible-locus
argument published by Workers 105 and 1483 in `SchemeFilteredFiberGeometryProof`.

`RelativePureFibreDimensionDescentStatement` isolates the pure-dimension
condition from the published combined geometric-connectedness and pure-dimension
theorem. For every natural dimension `d`, a cofiltered diagram of affine schemes
with an actual limit cone, a compatible map from the diagram to any fixed scheme
`S`, schemes `X` and `Y` over `S`, and `f : X ⟶ Y` over `S`, it equates pure
dimension `d` of every residue-field fibre over the limit with its occurrence at
one actual stage. It retains local finite presentation, quasi-compactness and
quasi-separatedness of `f`, and quasi-compactness and quasi-separatedness of the
target model over `S`. It assumes no geometric connectedness or nonemptiness of
fibres. Pure dimension keeps its published componentwise meaning, and empty
fibres satisfy it vacuously. No affine or separated model or noetherian base is
assumed, and the scheme universe is arbitrary.

The implemented proof applies the published local-dimension sublevel properties
to make the pure-dimension fibre locus constructible at each actual target
model stage. Its pullback to the target over the limit is the whole target when
the limit condition holds. The published constructible-set limit theorem gives
an incoming stage where the pullback is already the whole stage target. The
cartesian transition comparison for the actual pure-dimension locus identifies
this pullback with that incoming stage's locus. Conversely, a full stage locus
pulls back to the full locus over the limit. Fullness of each locus is precisely
the all-fibres pure-dimension property.

This is an internal derived specialization of the published constructible-locus
machinery. It follows the published relative argument but applies only its
pure-dimension factor. It supplies a scheme prerequisite for the chart descent
in Task 5302; the algebraic-space comparison and the geometric-connectedness
condition remain separate obligations.
