# Rational block projectors and spectral norms

Author: Worker 1045.

This internal helper module proves one linear-algebra fact over a complete
ultrametric field, plus a small multiset lemma used in its proof. It is used in
the proof of
`Langlands.BruhatTits.RationalPoints.CentralNormKernelCompactnessStatement`. A
block determinant of a central point is then a positive power of the spectral
norm of one of its eigenvalues. The statement and proof were written for this
proof route, at the request of the route's first executor (Worker 1532). They
do not formalize a cited source. The ingredients are standard: primary
decomposition by coprime factors of the characteristic polynomial, spectral
mapping, and multiplicativity of the spectral norm. Nothing here involves group
schemes. Namespace: `Langlands.BruhatTits.RationalPoints.CentralNormKernel`.

Throughout, `F` is a nontrivially normed field with an ultrametric distance that
is complete (`NontriviallyNormedField F`, `IsUltrametricDist F`,
`CompleteSpace F`). `AlgebraicClosure F` is Mathlib's algebraic closure, and
`spectralNorm F L x` is Mathlib's spectral norm of an element `x` of an
algebraic extension `L` of `F`. The spectral norm of `x` depends only on the
minimal polynomial of `x` over `F`.

## Main statement

`exists_blockProjector_spectralNorm`: let `n` be a finite type, let
`A : Matrix n n F`, and let `μ : AlgebraicClosure F` be a root of the image of
the characteristic polynomial of `A` in `(AlgebraicClosure F)[X]`. Then there
is a polynomial `P : F[X]` and a natural number `b` such that

- `aeval A P` is idempotent;
- `1 ≤ b`;
- `‖det (A * aeval A P + (1 - aeval A P))‖ = spectralNorm F (AlgebraicClosure F) μ ^ b`.

The idempotent `π = aeval A P` constructed in the proof is the projector onto
the generalized eigenspace of the minimal polynomial `P₀` of `μ`, along the sum
of the other primary components. The matrix `A π + (1 - π)` agrees with `A` on
the image of `π` and is the identity on its kernel, so its determinant is the
determinant of the block of `A` belonging to `P₀`. The statement records only
that `π` is idempotent and does not identify its image; the proof does not need
more.

## Proof

Write `q` for the characteristic polynomial of `A` and `P₀ = minpoly F μ`. The
polynomial `P₀` is irreducible because `μ` is algebraic over `F`, and `P₀`
divides `q` because `q(μ) = 0`.

1. Primary factor. `WfDvdMonoid.max_power_factor` writes `q = P₀ ^ a * r` with
   `P₀ ∤ r`. Then `a ≥ 1`, since otherwise `q = r` and `P₀` would divide `r`.
2. Bezout. `P₀ ^ a` and `r` are coprime (`Irreducible.coprime_pow_of_not_dvd`),
   so `u * P₀ ^ a + w * r = 1` for some `u, w : F[X]`. Put `P = w * r`.
3. Idempotence. Evaluating the Bezout identity at `A` gives
   `aeval A (u * P₀ ^ a) = 1 - aeval A P`. The product `P * (u * P₀ ^ a)` is a
   multiple of `q`, so by Cayley–Hamilton
   `aeval A P * (1 - aeval A P) = 0`. That is, `aeval A P` is idempotent.
4. Block matrix as a polynomial in `A`. With `G = X * P + (1 - P)`, we have
   `A * aeval A P + (1 - aeval A P) = aeval A G`; call it `Y`.
5. Values of `G` at the eigenvalues. Let `ν` in the algebraic closure be a root
   of `q`. If `P₀(ν) = 0`, the Bezout identity gives `P(ν) = 1`, so `G(ν) = ν`.
   Otherwise `r(ν) = 0`, because `q = P₀ ^ a * r`; then `P(ν) = 0` and
   `G(ν) = 1`.
6. Spectral mapping. Over the algebraic closure, the image `Y_L` of `Y` is `G`
   evaluated at the image `A_L` of `A`. The spectrum of `A_L` is the set of
   roots of `q`; it is nonempty because it contains `μ`. By
   `spectrum.map_polynomial_aeval_of_nonempty`, the spectrum of `Y_L` is the
   image of the spectrum of `A_L` under `G`. By step 5, every root `x` of the
   characteristic polynomial of `Y_L` satisfies `P₀(x) = 0` or `x = 1`. Also
   `G(μ) = μ`, so `μ` is such a root, and it satisfies `P₀(μ) = 0`.
7. Norm of the determinant. By `spectralNorm_extends`, `‖det Y‖` is the spectral
   norm of the image of `det Y` in the algebraic closure. That image is
   `det Y_L` (`RingHom.map_det`), which is the product of the roots of the
   characteristic polynomial of `Y_L`, with multiplicity
   (`Matrix.det_eq_prod_roots_charpoly`).
8. Product of the roots. A root `x` with `P₀(x) = 0` has minimal polynomial
   `P₀`, because `P₀` is monic and irreducible
   (`minpoly.eq_of_irreducible_of_monic`). Its spectral norm therefore equals
   that of `μ`. Every other root equals `1`. The helper lemma below then gives
   `spectralNorm (det Y_L) = spectralNorm μ ^ b`. Here `b` is the number of
   roots `x`, counted with multiplicity, with `P₀(x) = 0`. Step 6 gives
   `b ≥ 1`.

## Helper lemma

`spectralNorm_multiset_prod_eq_pow_countP`: let `L` be an algebraic extension of
`F`, let `p` be a decidable predicate on `L`, let `c : ℝ`, and let `s` be a
multiset in `L`. Assume that every element of `s` satisfying `p` has spectral
norm `c`, and every element of `s` not satisfying `p` equals `1`. Then the
spectral norm of the product of `s` is `c ^ (s.countP p)`.

The proof is by induction on `s`. It uses that the spectral norm is
multiplicative over a complete `F` (`spectralAlgNorm_mul`) and that the spectral
norm of `1` is `1`.

## Declarations

- `spectralNorm_multiset_prod_eq_pow_countP`
- `exists_blockProjector_spectralNorm`
