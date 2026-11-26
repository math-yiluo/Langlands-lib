# Shahidi's coefficient identity from unfolding and the local numerator

Module `Langlands.Global.Factors.CuspidalPairEisensteinCoefficientReduction`
proves

```lean
def CuspidalPairEisensteinCoefficientReductionStatement : Prop :=
  CuspidalPairEisensteinUnfoldingStatement.{u} →
    CuspidalPairEisensteinLocalNumeratorStatement.{u, uQ} →
      CuspidalPairEisensteinCoefficientStatement.{u, uQ}

theorem cuspidalPairEisensteinCoefficientReduction :
    CuspidalPairEisensteinCoefficientReductionStatement.{u, uQ}
```

in the namespace `Langlands.Global`. The premises are
[`CuspidalPairEisensteinUnfoldingStatement`](CuspidalPairEisensteinUnfoldingStatement.md)
and
[`CuspidalPairEisensteinLocalNumeratorStatement`](CuspidalPairEisensteinLocalNumeratorStatement.md);
this module does not prove them. The conclusion is
[`CuspidalPairEisensteinCoefficientStatement`](CuspidalPairEisensteinCoefficientStatement.md)
at the same universes `u` and `uQ`. No other unproved statement is used.

## Proof

Fix the data of the coefficient statement.

1. The local numerator statement gives the enlarged set `S₀ ⊇ S`. The
   unfolding statement gives `κ > 0`, and
   `RankinSelbergGlobal.exists_partialEulerFactor_convergence`, applied to
   `P`, `P'` and `S₀`, gives `σ_L` such that for `σ_L < Re w` the family
   `‖partialEulerFactor … v w - 1‖` is summable and the product has the
   value `partialEulerProduct … w`.
2. For `s₀` with `Re s₀ = 0` the local numerator statement gives a section
   `φ`, a numerator `c` and a threshold `σ_N`, and the unfolding statement for
   this `φ` gives a threshold `σ_U`.
3. The numerator of the conclusion is `s ↦ κ c(s)`. It is meromorphic on `ℂ`,
   analytic at `s₀` and nonzero there because `κ ≠ 0`.
4. For `Re s > max σ_L (max σ_U σ_N)`, the point `w = 1 + s` has
   `Re w > σ_L`, which gives the summability and `HasProd` with value
   `Λ = partialEulerProduct … (1 + s)`. Then
   `κ c(s) = κ Λ I(φ, s) = Λ coeff ψ φ s` by the two premises.

## Source

The order of the argument is that of Shahidi, *On certain L-functions*,
Amer. J. Math. 103 (1981), proof of Theorem 5.1, pp. 351–352: the Fourier
coefficient is first written through Lemma 2.1 of Shahidi (1978), then
factored into local integrals whose unramified values are the reciprocal
Euler factors.
