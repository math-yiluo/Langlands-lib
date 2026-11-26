# Quantitative compact approximate identities for real Whittaker intertwiners

## Statement

`RealWhittakerApproximateIdentityStatement`: let `cs` be a list of real character data, put
`ds = cs.map RealBlock.character`, and let `B` be a linear map from the `O(r+1)`-finite
standard module `Automorphic.realStandardKFinite (r + 1) ds` to functions on
`GL_{r+1}(ℝ)` with `IsRealWhittakerIntertwiner r ds a B`. Then there are `C ≥ 1` and `P`
such that for every `0 < ε ≤ 1` there is a linear endomorphism `A` of the standard module
with

1. `A` commutes with right translation by every orthogonal matrix
   (`realStandardRep (r + 1) ds k`);
2. `CompactBound f R → CompactBound (A f) (C R)`;
3. `CompactBound f R → CompactRightDifferenceBound f D → CompactBound (f - A f) (C ε (R + D))`
   for `D ≥ 0`;
4. `CompactBound f R → ‖B (A f) 1‖ ≤ C R ε^(-P)`.

`CompactBound` and `CompactRightDifferenceBound` are the compact value and first right
difference bounds of `RealCompactProbeBounds`. `realWhittakerApproximateIdentity` proves the
statement.

## Proof

Take `M`, `H`, `E` from `realCompactProbeBounds` for `ds`, and a sample vector `f₀` from
`realOppositeNonzero` with nonzero opposite-cell mass and integrable moment of order `M + 1`;
this is where the restriction to character lists enters. Let `W(u) = (1 + ‖u - 1‖)^(M+1)` and
`J = ∫ W(u) |f₀(uᵀ)| du`. The operator `A` is the normalized compact average of
`realNormalizedCompactAverage` for `f₀` and `ε`.

1. Commutation with compact translations follows from the compact average formula and the left
   invariance of the Haar measure of `O(n)` applied to the inverse weight.
2. At an orthogonal point, `(A f)(x)` is `(oppositeMass f₀)⁻¹` times the integral of
   `f₀(uᵀ) · dualSection f x ((contraction u)ᵀ)`. The contraction does not increase the
   coordinate norm for `ε ≤ 1` (it scales the entry `(i, j)` by `ε^(j - i)`), so the probe value
   estimate bounds the integrand by `H R W(u) |f₀(uᵀ)|`; hence `‖(A f)(x)‖ ≤ ‖mass⁻¹‖ H J R`.
3. Since the mass normalizes the integral, `f(x) - (A f)(x)` is `mass⁻¹` times the integral of
   `f₀(uᵀ) (f(x) - dualSection f x ((contraction u)ᵀ))`. The probe error estimate bounds the
   second factor by `E (R + D) ‖z‖ (1 + ‖z‖)^M` at the contracted coordinates `z`, and
   `‖z‖ ≤ ε ‖u - 1‖` absorbs one more factor into `W`, giving `‖mass⁻¹‖ E J ε (R + D)`.
4. The Whittaker formula of the normalized average and `realCompactAverageGrowth` give the
   sampling bound.

`C` is the maximum of `1`, the sampling constant and the two constants above. This is the real
counterpart of the Library's `ComplexWhittakerApproximateIdentity`, used to prove the finite
order of Whittaker evaluation in `RealWhittakerFiniteOrder`.
