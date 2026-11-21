# Functional equation for the complex square zeta integral of a standard vector

The normalized square integrals extend to entire functions for the original standard vector and its inverse-transpose dual. The group change by the longest Weyl matrix expresses the latter as an upper-Borel integral with reversed inverse characters. The common right half-plane is chosen using the two height bounds and all the real parts of the inducing exponents.

After compact Fourier covariance, the dual triangular marginal is the trace Fourier transform of the original marginal with its diagonal reversed. The proof uses the compact twist, the entry permutation preserving the product self-dual measure, and the triangular Fourier slice identity. Reversing the independent Tate variables then gives the equation by the entire scaled Tate reflection. The group constants coincide and the epsilon product is the Library's `complexEpsilon` at the negative trace sign.

This version uses evaluation of a standard vector as the coefficient. [Jacquet, *Archimedean Rankin–Selberg integrals*, §4.7, equation (4.3)](https://doi.org/10.1090/conm/489/09547).

`complexSquareStandardFunctionalEquationGrowth` gives exponential strip growth for both entire normalized functions. Each is a constant times a normalized product Tate integral on a line with slope one in every coordinate. For the ordinary witness the line shifts by the original exponents. For the dual witness it shifts by the reversed inverse exponents. The product Tate strip bound on these two lines proves the claim.
