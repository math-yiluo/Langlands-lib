# Transport of local integer rings under continuous field maps

`LocalFieldData.map_mem_integers_of_continuous` takes the actual valuation
rings of two nonarchimedean local fields. If `x` belongs to the source
ring, all its nonnegative powers belong to that compact ring. The
normalized absolute value of their images under a continuous ring map is
therefore bounded. These absolute values are the powers of the absolute
value of the image of `x`, which must be at most one.

`LocalFieldData.mem_integers_iff_of_continuous_ringEquiv` applies the same
argument to an equivalence and its continuous inverse. Both lemmas are
internal consequences of the Library's compactness and normalized
absolute-value laws.
