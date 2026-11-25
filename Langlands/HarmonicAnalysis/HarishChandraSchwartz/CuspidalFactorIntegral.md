# The Levi integral of the cuspidal-split factors

This internal module combines the cancellation and constant-term bounds
into an estimate for the Levi integral in the VIII.3.1 open-cell split.
It retains the relevant analytic assumptions and does not assert their
closed actual-point versions.

`UnipotentFactorDecayBound` states that the norm of the second split
factor is at most
`c ΞM(m) (1 + σM(m))^(-d)` for every real `d`, uniformly in the
conjugator and all Levi points. The truncation assigned to the
conjugator is arbitrary. The theorem
`unipotentFactorDecayBound_of_constantTermEstimate` proves this from a
conjugation modulus, the full constant-term estimate, positive ambient
Xi, nonnegative ambient height and finite Schwartz seminorms of the
function. Bound the restricted Bochner integral by its nonnegative norm
integral over the whole radical and apply
`ConstantTermEstimate.lintegral_mul_right_le`.

`lintegral_cuspidalFactors_le_of_tail` assumes the first factor's
`CuspidalFactorTailBound`, the second factor's
`UnipotentFactorDecayBound`, and `ConvolutionWeights` for the Levi Xi
and height. It also assumes right compact invariance of that height;
the convolution-weight structure itself provides only left compact
invariance. The measure is explicitly left and right invariant and
`SFinite`, and the Levi group is second countable.

For every nonnegative tail exponent `p`, the theorem gives

```text
∫_M |φ₁(a, a m a⁻¹)| |φ₂(a,m)| dm
  ≤ c δU(a)^(-1) t(a)^(-p) ΞM(a)^2
```

uniformly for `a` in the specified set. In Lean this is a bound on the
nonnegative lower integral of the product of extended norms.

The proof chooses the first factor's bound at Levi exponent zero and
the second factor's bound at the natural exponent from the weighted
Levi Xi-square estimate. Their product is bounded by a constant times
`ΞM(a m a⁻¹) ΞM(m) (1 + σM(m))^(-d₀)`.
Define the multiplier
`W(m) = ENNReal.ofReal (ΞM(m) (1 + σM(m))^(-d₀))`.
The proof establishes measurability and compact bi-invariance of `W`.
It applies `lintegral_xi_mul_mul` with `x = a` and `y = a⁻¹` to the
integral of `ENNReal.ofReal (ΞM(a m a⁻¹)) * W(m)`.
The averaging identity and inverse symmetry of Xi express this integral
as `ΞM(a)^2` times the finite weighted Xi-square integral.
All resulting constants are finite.

Replacing the squared Levi Xi by the source modulus and powers of the
conjugator height requires additional chamber Xi and cutoff estimates.
Those are separate from the factor-integral bound proved here.
