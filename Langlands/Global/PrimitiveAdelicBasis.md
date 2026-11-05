# Rational bases adapted to adelic height minima

This supporting construction turns an attained rational height minimum into a
rational change of basis of an actual adelic invertible matrix. It retains every
number field in universe `u` and every positive finite dimension.

The motivation is Springer, *Reduction theory over global fields* (1994),
§1.10, printed p.210, PDF p.4: after choosing a rational minimum, the proof
assumes the first standard vector attains that minimum. The source is registered
as `springer-1994-reduction-global-fields`, SHA256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
This module derives the corresponding change of basis for the existing maximum
coordinate height over arbitrary number fields and finite dimensions. It does
not assert the subsequent Euclidean Gauss estimate.

`firstVector` is the first standard rational vector. To put any nonzero rational
vector `v` in the first column of a rational invertible matrix, the proof first
identifies the spans of the first standard vector and `v` through their
one-dimensional scalar coordinates. Mathlib extends this linear equivalence of
subspaces to an automorphism of the full finite-dimensional vector space. The
matrix and linear automorphism equivalence then gives the required rational
invertible matrix.

The actual rational embedding of matrices commutes with matrix action on the
coordinatewise diagonal vector map. Consequently the height of `g γ v` is the
height of `g (γ v)`. An invertible rational matrix preserves nonvanishing.
`minimumRationalHeight_mul_rational` deduces that right multiplication by any
rational invertible matrix leaves the rational height minimum unchanged: the
inverse matrix carries a minimizing vector of either matrix to a nonzero
rational vector with the same height for the other matrix.

`minimumBasisChange` chooses a rational invertible matrix whose first column
is `minimumRationalVector`. `minimumAdaptedMatrix` is its image multiplied on
the right of the original adelic matrix. Its first standard vector has exactly
`minimumRationalHeight` of the original matrix and has height no larger than
that of any other nonzero rational vector.

These results prove a preparatory rational change of basis, using the earlier
attained-minimum theorem without extra coverage assumptions. They leave local
Iwasawa decomposition, norm comparisons, Gauss reduction, higher-rank induction
and the general reductive Siegel-cover theorem open.
