# Actual bounds on the full diagonal torus

This internal derived module restricts genuine ambient integrability directly to the full diagonal torus. Its diagonal measure is exactly the product of the existing normalized local multiplicative Haar measures. No uniformizer, partition into valuation classes, or new normalization constant occurs.

`measure_diagonalUnits_preimage_principalLevel_le_one` proves that the inverse image of every principal congruence subgroup under `Iwasawa.diagonalUnits` has product Haar measure at most one. Every such diagonal matrix and its inverse have integral entries; hence each diagonal entry is an actual integral unit. The inverse image is therefore contained in the product of integral units, whose product Haar measure is one.

`integrable_diagonalUnits_of_principalFixed` applies the proved Haar restriction inequality to that diagonal group homomorphism. The ambient principal subgroup has positive measure, and its inverse image has finite measure by the preceding bound. The hypotheses are genuine ambient integrability, measurability, and pointwise right fixation by that principal subgroup.

`matrixDiagonalIntegrand` evaluates the unchanged full-matrix integrand on `Iwasawa.diagonalUnits a`. For each actual member of `biSmoothMatrixCoefficients σ`, `integrable_biSmooth_matrixDiagonalIntegrand` derives its full torus integrability from its actual ambient matrix convergence. SmoothTorusBound supplies the spectral-independent principal stabilizer and measurability. Finally `biSmooth_matrixDiagonal_convergesOnRight` retains precisely the common bound and complex shift `s + jpssShift n` supplied by the original matrix hypothesis, uniformly over all full square-matrix tests and all actual coefficients.

The statements cover every canonical p-adic field, every rank including zero, and independent arbitrary field and representation-carrier universes. They assert neither raw Whittaker convergence nor a gamma comparison. Provenance is source-free composition of actual principal entry conditions, product Haar normalization, HaarRestriction, and the stabilizer results of SmoothTorusBound.
