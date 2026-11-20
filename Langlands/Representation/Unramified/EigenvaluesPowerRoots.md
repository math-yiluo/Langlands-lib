# Powers of a spectrum with an induced Euler polynomial

Worker 5130 wrote this module for Task 7784. Weak induction (Harris 1998, Definition 1.3(b))
prescribes the Euler polynomial at an unramified place `v` as a product
`∏_w (1 - c_w X^{f_w})` over the places `w` above `v`. Weak base change prescribes `N`-th
powers of spectra (`Eigenvalues.power`). Comparing the two needs the spectrum of `N`-th
powers of a spectrum with such an Euler polynomial.

## Statements

In namespace `Langlands.Unramified.Eigenvalues`:

- `roots_one_sub_C_mul_X_pow`: for `c ≠ 0` in `ℂ`, the roots of `1 - c X^f` are the `f`-th
  roots of `c⁻¹` (`Polynomial.nthRoots f c⁻¹`), with multiplicity. The proof writes
  `1 - c X^f = -c (X^f - c⁻¹)`.
- `map_pow_nthRoots`: for `0 < f` and `f ∣ N`, the `N`-th powers of the `f`-th roots of
  `a ∈ ℂ` are `f` copies of `a ^ (N / f)`. There are `f` roots, by
  `IsPrimitiveRoot.card_nthRoots` for the primitive root `exp(2πi/f)` and since `ℂ` is
  algebraically closed. Each root `x` satisfies `x^N = (x^f)^(N/f)`.
- `coe_power_eq_sum_replicate`: let `A` be an unordered spectrum of `n` nonzero complex
  numbers, `c : ι → ℂˣ` and `f : ι → ℕ` a finite family with `0 < f i ∣ N`. If
  `A.eulerPolynomial = ∏ i, (1 - c i X^{f i})`, then the multiset of `N`-th powers of
  `A` is `∑ i, replicate (f i) (c i ^ (N / f i))`.

The last proof compares roots. The roots of the Euler polynomial of `A` are the inverses of
its elements (the published `Eigenvalues.eulerPolynomial_roots`). The roots of the product
are the sum of the roots of the factors (`Polynomial.roots_prod`), and each factor has
`f i` roots, each of `f i`-th power `(c i)⁻¹`. Taking `N`-th powers on both sides and
using injectivity of `z ↦ z⁻¹` on `ℂˣ` gives the identity.

## Provenance

Elementary algebra; internal to the project.
