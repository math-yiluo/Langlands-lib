# Fourier sign in the complex unequal-rank functional equation

`ComplexUnequalJacquetConventionReductionStatement` reduces the Library proposition
`ComplexLocalUnequalFunctionalEquationStatement` to
`ComplexLocalUnequalJacquetEquationStatement`. The open premise uses the Library's
Whittaker models, kernels, integrals, measures, and ordinary and dual \(L\)-factors. Its
convergence, holomorphy, and meromorphic continuation clauses are shared with the target.
In the crossed identity it uses epsilon with parameter `-a` and the coefficient
`complexCentralSign ds ^ (t + 1) * complexCentralSign es`, for the ranks `r + 1` and `t + 1`.

The proof expands the epsilon factor for one complex character. Negating `a` multiplies
the character value at `a` by its value at `-1` and preserves `‖a‖`. On all pair blocks the
multiplier is `complexCentralSign ds ^ (t + 1) * complexCentralSign es ^ (r + 1)`, since each
character in either list occurs once for each character in the other list. Both central
signs square to one. Multiplying by the sign in the premise cancels the two copies of the
first central character contribution and leaves `complexCentralSign es ^ r`. The
published `RealJacquet.EquationPackage.change_factor` applies this scalar equality directly
to the crossed identity. The file also checks that `a` and `-a` give the same self-dual
measure and that changing `a` to `-a` reflects the Fourier transform argument.

In Theorem 2.1(iii) on p. 6, the larger-gap display uses the exponent \(n'\) on the
first central character, and the gap-one display uses \(n-1=n'\). Both give the
same sign as the product immediately following (10.10) on p. 76. The negative Fourier
convention is visible in the phases on pp. 110–111, and the character-change rule on
p. 5 gives the determinant factor at `-1`. Establishing the open premise requires the
analytic theorem on the Library's carriers. [Jacquet, *Archimedean Rankin–Selberg integrals*, pp. 5–6, 76 and 110–111](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
