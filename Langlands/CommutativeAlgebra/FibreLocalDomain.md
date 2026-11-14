# Regular elements of fibre local rings from a domain fibre

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.CommutativeAlgebra.FibreLocalDomain`. Let `R` be an `A`-algebra, `P` a prime
of `R` and `p = P ∩ A`.

- `exists_fiber_prime`: the prime `q` of the fibre ring `p.Fiber R = κ(p) ⊗_A R` that corresponds
  to `P` (Mathlib's `PrimeSpectrum.primesOverOrderIsoFiber`).
- `isSMulRegular_of_isDomain_fiber`: if the fibre ring `κ(p) ⊗_A R` is a domain and `1 ⊗ s ≠ 0`
  in it, then the image of `s` is a nonzerodivisor of `R_P ⧸ p R_P`. The proof identifies
  `R_P ⧸ p R_P` with the localization of the fibre ring at `q` (Mathlib's
  `Ideal.Fiber`/`algEquivAux` machinery) and uses that a localization of a domain is a domain.

## Use

This supplies the fibre hypothesis of `FibrewiseRegular.regular_and_flat_quotient` in the two
places where fibres are domains: affine pieces of geometrically integral fibres
(`FibreRegularSection`) and symmetric algebras of projective modules (`LineChartFlat`).
