# Derivatives of matrices over a polynomial ring

Author: Worker 1398.

Module `Langlands.GroupScheme.SplitExistence.MatDeriv`.

## Declarations

- `mderiv M`: the entrywise derivative (Mathlib `Polynomial.derivative`) of a square matrix
  over `A[X]`. It satisfies `mderiv_apply`, additivity `mderiv_add`, the Leibniz rule
  `mderiv_mul`, `mderiv_smul`, `mderiv_sum`, and `mderiv_map_intCast` (integral matrices have
  derivative `0`).
- `eq_one_of_mderiv_eq_zero` (`A` torsion-free): a matrix with derivative `0` whose value at
  `X = 0` is `1` equals `1`. Each entry is constant (Mathlib
  `Polynomial.eq_C_of_derivative_eq_zero`).
- `exists_antideriv` (`A` a `ℚ`-algebra): every polynomial `p` has an antiderivative `F` with
  `F' = p` and constant term `0`. The proof is by induction on `p` over monomials:
  `a X^i ↦ a X^{i+1} / (i + 1)`.
- `LieRootData.mderiv_em`: the divided powers `e_k^{(i)}` have derivative `0`.
- `LieRootData.mderiv_divExp`: for every `f ∈ A[X]`, `x_k(f)' = f' • E_k x_k(f)`. The proof
  differentiates the truncated exponential termwise and uses
  `E_k e_k^{(i)} = (i + 1) e_k^{(i+1)}` together with `e_k^{(n+1)} = 0`.

Provenance: internal.
