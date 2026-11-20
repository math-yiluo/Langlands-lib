# Localization of compact Levi chart coordinates

The compact block diagonal embedding has image the orthogonal matrices whose off-block entries vanish. The signed orthogonal factor of a lower block frame is equivariant under right multiplication by the embedded block group.

`frameBump` is the continuous product of squared trailing minors at the block cuts of a compact matrix. It equals one on the compact block diagonal subgroup. The signed orthogonal factorization multiplies the compact factor on the left by an invertible upper triangular matrix. Invariance under this operation and under right multiplication by a compact block diagonal matrix identifies the pullback of `frameBump` with `RealLeviBump.beta` on lower coordinates.

The published gap for `beta` gives an upper bound strictly below one outside each prescribed ball about zero. A superlevel set of `frameBump` therefore gives an open neighborhood of the compact block group whose entire chart preimage has lower coordinates in that ball. This is an internal use of the trailing-minor estimates for the compact Haar chart.
