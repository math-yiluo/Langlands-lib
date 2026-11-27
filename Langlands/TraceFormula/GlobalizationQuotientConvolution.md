# Compact convolution on the positive rational quotient

`positiveQuotientCompactConvolution` integrates compactly supported continuous
weights against a fixed vector in the actual quotient L² space. Its linearity is
linearity of the Bochner integral. Translating the weight on the left intertwines
the original right representation by left invariance of the full-group Haar measure.

To check that a weight gives nonzero convolution, first integrate it along the
positive split center using the Haar normalization in the product decomposition.
Periodize the resulting compact norm-one test by the rational norm-one subgroup.
If the periodization has a nonzero identity value, the conjugate periodization
supplies a continuous compactly supported quotient input. At the identity its
convolution value is the integral of the squared norm of the periodization, by
Haar product disintegration and the norm-one Weil formula. This integral is
positive because quotient Haar charges every nonempty open set. The pointwise
integral represents the original L² convolution, and continuity detects its
nonzero class.
