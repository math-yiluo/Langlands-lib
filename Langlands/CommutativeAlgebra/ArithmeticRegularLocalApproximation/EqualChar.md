# Regular local charts for complete discrete valuation rings of equal characteristic

Module `Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.EqualChar`.

This module is the equal-characteristic case of the chart construction used in the proof of
`Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximationStatement`.

## `chartConclusion_equalChar`

Let `W'` be a discrete valuation ring, complete for its maximal ideal, with irreducible element
`ϖ`, and suppose that the characteristic `ringChar (ResidueField W')` of the residue field is
zero in `W'`. Then `ChartConclusion W' C F'` (module
`Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.Chart`) holds for every finite
type `ℤ`-algebra `C` and every ring map `F' : C → Frac W'`.

Proof. Apply `chartConclusion_of_dvr` (module
`Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.Base`) with `Λ = W'`,
`ψ = id` and `F = X - ϖ`:

- every prime number is zero, a unit or a uniformizer in `W'` by `intCast_prime_cases`, since the
  residue characteristic is zero in `W'`;
- `F` is monic and `F(ϖ) = 0`;
- the constant coefficient `-ϖ` is not in `𝔪²` (`irreducible_notMem_maximalIdeal_sq`);
- every `y ∈ W'` is the value at `ϖ` of the constant polynomial `y`;
- a polynomial vanishing at `ϖ` is divisible by `X - ϖ` (`Polynomial.dvd_iff_isRoot`).
