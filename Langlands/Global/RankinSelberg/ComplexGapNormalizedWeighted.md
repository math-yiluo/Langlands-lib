# Joint convergence on the determinant-one gap chart

The normalized chart has two independent rapid weights, one in the determinant of the smaller quotient and one in the determinant of the leading group. The theorem proves joint absolute convergence for the complete split kernel, including the earlier triangular Fourier columns. Both choices of leading Fourier side are covered. The measure on the complementary rectangle can be any σ-finite measure that integrates an inverse polynomial in the matrix height.

The change of variables multiplies the quotient representative by the leading normalization scalar and multiplies the leading matrix by its inverse. The normalized leading Schwartz argument becomes the original stacked argument. The tail columns and inverse last row stay fixed. The scalar cancels in both Whittaker arguments and remains as a determinant power from the quotient integrand. The two rapid weights acquire exponential rescalings in the tail log sum.

The outer Haar density and the leftover determinant power contribute explicit real exponents of the tail log sum. Their product with the allowed multiplier is bounded by a fixed exponential in the sum of the absolute tail logs. The joint convergence theorem for the original chart then applies through the measure-preserving shear.

`quotientDetAbs_right` records the determinant change in the quotient shear.
`padGL_eq_rankInclusion` identifies the padding map with the leading block inclusion in consecutive coordinates.

`quotientDetAbs_mk` evaluates the normalized quotient determinant at any representative.

`complexGapNormalizedPowerBounds` transfers one power estimate per weight through the same shear. The positive rescalings preserve the exponents on the two determinant variables. Their contribution in the tail logs fits the exponential allowed in the alternate chart.
