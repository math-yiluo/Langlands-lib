# Shahidi's boundary nonvanishing from the generic coefficient

`Langlands.Global.CuspidalPairEisensteinDerivationStatement.{u,uQ}` is the
implication from the **coefficient identity**
(`CuspidalPairEisensteinCoefficientStatement.{u,uQ}`) and the **continuation
and imaginary-axis holomorphy of the coefficient**
(`CuspidalPairEisensteinHolomorphyStatement.{u}`) to the unchanged
`CuspidalPairBoundaryNonvanishingStatement.{u,uQ}`. The number field and the
spaces used in the spectral presentations retain their independent universes.
`cuspidalPairEisensteinDerivation` proves this implication, not either premise.

## Lean proof

For the given field, cuspidal realizations, spectral presentations and omitted
set `S`, the proof uses `RankinSelbergGlobal.EqualAnalytic.standardCharacter`.
This is the complex-valued form of the Library's circle-valued adelic
character. Its continuity and triviality on principal adeles follow from
`continuous_standardCharacter` and `standardCharacter_algebraMap`;
unitarity follows from the circle norm and nontriviality from
`Automorphic.CuspidalWhittaker.exists_adelicCharacter_ne_one`.

The coefficient identity gives one finite enlargement `S₀` of `S`, then for
each `s₀` of real part zero gives a section `φ` and meromorphic numerator `c`
analytic and nonzero at `s₀`. On a right half-plane it gives absolute product
convergence outside `S₀` and `c(s) = Λ(s) · coeff ψ φ s`, where `Λ(s)` is the
value of the partial pair Euler product at `1 + s`. The holomorphy input is
applied to the **same** character and section. It gives a meromorphic `Ec`
that is analytic at `s₀ = s₀.im · I` and agrees with `coeff ψ φ` on a right
half-plane. Neither the two half-plane thresholds nor the sections at different
points need to be the same.

`cuspidalPairBoundaryNonvanishingEnlarged_of_eisenstein` packages these data in
`EulerProductCoefficientData.CoefficientData` and applies
`EulerProductCoefficientData.enlarged_of_coefficientData`. That theorem
constructs one representative for the Euler product outside `S₀`, with local
orders computed using `c / Ec` in the shifted variable. At each `s₀` the
numerator has order zero and the continued coefficient has finite nonnegative
order, so their quotient has nonpositive order. Finally
`cuspidalPairBoundaryNonvanishingReduction` puts back the factors at the finitely
many places in `S₀ \ S` and transfers the order bound to every representative
for `S` by the meromorphic identity theorem. In particular, the proof gives the
existence conjunct as well; it does not assume a separate meromorphic
continuation theorem for the partial L-function.

## Provenance

This derived Library implication isolates the last step of F. Shahidi,
*On certain L-functions*, Amer. J. Math. **103** (1981), Theorem 5.1 proof,
pp. 351–352, and Theorem 5.2, p. 353 (registered `shahidi-1981-certain-l`, PDF
pp. 56–58). Here `s` is the normalized coefficient variable for the
upper two-block parabolic: `s = (r+t+2) z` in the notation of the source's
coefficient formula with parameter `z`, so the Euler product is evaluated at
`1 + s`. The two automorphic premises use the actual normalized induced
section and the actual generic Fourier coefficient of the Eisenstein series,
not independent scalar functions standing in for them. The companion files
[CuspidalPairEisensteinCoefficientStatement.md](CuspidalPairEisensteinCoefficientStatement.md)
and [CuspidalPairEisensteinHolomorphyStatement.md](CuspidalPairEisensteinHolomorphyStatement.md)
record the local factorization and analytic inputs; the proof here starts
with those propositions as hypotheses.
