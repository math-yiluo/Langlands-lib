# Regrouping a restricted tensor of block coefficient spaces

`blockRegroupEquiv` identifies the restricted tensor product of the placewise block tensors with the finite tensor product of the blockwise restricted tensor products. Both use the same finite exceptional set. At a place outside that set the reference for the block tensor is the pure tensor of the given nonzero block references.

On a finite stage, `transposeLinearEquiv` flattens the nested tensors by the published dependent regrouping equivalence and then groups the same factors by block. The formula on an array of pure factors shows that the finite-stage map commutes with the transition that adjoins reference vectors. This gives `blockRegroup` on the direct limit. Its injectivity follows because each block's stage inclusion has a linear left inverse, and their tensor gives a left inverse for the tensor of the stage inclusions. For surjectivity, the factors of a pure block tensor have representatives on a common finite stage given by the union of their stages. Transposing that stage produces a preimage.

`blockRegroup_mapWithBound` proves compatibility with the induced restricted tensor maps from blockwise linear maps. On a common stage containing the bound, both maps apply the same linear map to each place and block factor. The pure arrays there determine the maps on the entire limit.

This is an internal consequence of the direct-limit construction and finite tensor regrouping. Flath (1979), *Decomposition of representations into tensor products*, §2, pp. 180–181 (PDF 176–177), gives the construction of the restricted tensor product and the induced maps that preserve the references outside a finite set.
