# Pure fibre dimension alone descends along cofiltered affine limits

The implementation adapts the relative constructible-locus
argument of `SchemeFilteredFiberGeometryProof`.

`RelativePureFibreDimensionDescentStatement` isolates the pure-dimension
condition from the combined geometric-connectedness and pure-dimension
theorem. For every natural dimension `d`, a cofiltered diagram of affine schemes
with an actual limit cone, a compatible map from the diagram to any fixed scheme
`S`, schemes `X` and `Y` over `S`, and `f : X ⟶ Y` over `S`, it equates pure
dimension `d` of every residue-field fibre over the limit with its occurrence at
one actual stage. It retains local finite presentation, quasi-compactness and
quasi-separatedness of `f`, and quasi-compactness and quasi-separatedness of the
target model over `S`. It assumes no geometric connectedness or nonemptiness of
fibres. Pure dimension keeps its componentwise meaning, and empty
fibres satisfy it vacuously. No affine or separated model or noetherian base is
assumed, and the scheme universe is arbitrary.

The implemented proof applies the local-dimension sublevel properties
to make the pure-dimension fibre locus constructible at each actual target
model stage. Its pullback to the target over the limit is the whole target when
the limit condition holds. The constructible-set limit theorem gives
an incoming stage where the pullback is already the whole stage target. The
cartesian transition comparison for the actual pure-dimension locus identifies
this pullback with that incoming stage's locus. Conversely, a full stage locus
pulls back to the full locus over the limit. Fullness of each locus is precisely
the all-fibres pure-dimension property.

This is an internal derived specialization of the constructible-locus
machinery. It follows the relative argument but applies only its
pure-dimension factor. It supplies a scheme prerequisite for the chart descent
of pure fibre dimension for algebraic spaces in
`AlgebraicSpace.SpaceLimitPureFibreDimensionDescent`; the algebraic-space
comparison and the geometric-connectedness condition are not treated here.
