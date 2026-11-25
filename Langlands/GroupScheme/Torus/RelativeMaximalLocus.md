# Openness of the maximal locus for relative tori

`maximalTorusOpen` is the actual open subscheme of the base where a supplied
closed relative torus in a reductive group is maximal on the residue fibre.
It imposes no restriction on the base scheme or on its residue characteristics.
This is an internal construction from the residue-fibre maximal locus and
published maximal-torus base-change and split-affine openness results.

The theorem `maximalTorusLocus_baseChange` identifies the pulled-back locus
with the inverse image of the original locus for any scheme morphism. The
ambient group is assumed smooth and affine, and the torus inclusion closed.
At a point of the new base, the map of residue fields gives an extension of
the residue field of its image. The canonical residue-field square and the
comparison of successive group-scheme pullbacks identify the two fibre maps.
Maximality ascends by the published field-extension theorem and reflects by
the published faithfully flat field-extension argument.

For a split torus over an arbitrary scheme, apply the split-affine openness
result on each affine chart and the pullback equality. Open immersions are
open maps and jointly cover the base, so their images give an open union equal
to the desired locus. For a relative torus, use its actual etale splitting
cover instead: its maps are open, the split result applies to each chart, and
the same union argument descends openness. Reductivity is preserved under
both base changes. The proofs introduce no unproved geometric prerequisite.
