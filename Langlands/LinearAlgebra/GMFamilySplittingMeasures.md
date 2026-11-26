# Gram volumes for two subspaces

`gramVolume_sum_eq_measureFactor` relates the Gram volume of two concatenated
bases to the two individual Gram volumes and the published `measureFactor`.
The proof expresses the bases in orthonormal coordinates of the two
subspaces. The change-of-basis matrix on the direct sum is block diagonal.
After mapping out of the direct sum by addition, the change of Gram volume is
the absolute determinant of this matrix. The formula uses the dimension
condition in `measureFactor`.

`measureFactor_ne_zero_iff` uses two subspaces contained in the target space.
Their factor is nonzero exactly when they have zero intersection and their
sum is the target space. The proof tests independence of their combined
orthonormal bases by injectivity of addition and uses the dimension test to
identify the span. These are intrinsic comparisons of the definitions in
`GMFamilies`.
