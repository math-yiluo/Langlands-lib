# Unfolding the adjacent-rank complex integral with a split Godement test

`ComplexAdjacentUnfoldingStatement` proves the two changes of variables in Jacquet's equation (8.3). It assumes the adjacent Godement integral formula for the larger group's restriction to the leading smaller block. It takes the smaller Whittaker factors with opposite characters and assumes absolute integrability of the final unfolded product.

For each quotient representative, right translation in the group variable replaces `h` by `h g⁻¹`. The character and determinant powers combine multiplicatively. The resulting kernel descends to the quotient since the last row is unipotent invariant and the two left characters cancel. Right translation of the quotient variable by `h` then produces the equal-rank kernel with one Whittaker factor right translated. The determinant weight at `h` acquires the exponent `s`. The quotient shear preserves the product measure, so absolute integrability transfers to the intermediate product and Fubini gives the claimed equality.

`complexAdjacentAbsoluteUnfolding` also records absolute integrability of the ordinary kernel under the same hypotheses. The ordinary kernel is a constant times the integral of the intermediate product in the group variable. Integrating an integrable product kernel along that variable gives an integrable function on the quotient.

This formulation isolates the integration step used after establishing the split Godement formula. [Jacquet, *Archimedean Rankin–Selberg integrals*, §8.3, equation (8.3)](https://doi.org/10.1090/conm/489/09547).
