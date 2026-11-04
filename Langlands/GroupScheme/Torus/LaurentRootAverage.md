# Constant Laurent coefficients as integral combinations of evaluations

This module proves one averaging lemma for Laurent polynomials. It is used in
`Absolute/TriangularTorusLift` for the proof of Milne 2017, Theorem 16.26(a)
(`Absolute/TriangularSplitExtension`). It lives in the namespace
`Langlands.GroupScheme.splitTorus`.

## Setting

Let `k` be a field, `I` a finite type, and `A` a `k`-algebra. Write
`A[I → ℤ]` for the Laurent polynomials `AddMonoidAlgebra A (I → ℤ)` in the
variables indexed by `I`.

- `laurentEval ζ : A[I → ℤ] →ₐ[k] A` evaluates at a point `ζ : I → kˣ`. It
  sends the monomial of exponent `m` to the image in `A` of the published
  character value `exponentValue I ζ m = ∏ ζ_i ^ m_i`. `laurentEval_apply`
  gives the explicit formula.
- `sum_exponentValue_pow`: let `ω` be a primitive `ℓ`-th root of unity and
  let `|m_i| < ℓ` for all `i`. Then the sum of the character `m` over the
  `ℓ`-torsion points `(ω^{x_i})_i`, `x : I → Fin ℓ`, is `ℓ^|I|` if `m = 0`
  and `0` otherwise. The proof factors the sum over the coordinates and uses
  the geometric sum.
- `sum_laurentEval`: if every exponent occurring in `f` has all coordinates
  of absolute value below `ℓ`, then the sum of the evaluations of `f` at the
  `ℓ`-torsion points is `ℓ^|I| • f.coeff 0`.
- `natCast_ne_zero_of_prime`: a prime `ℓ` larger than `ringChar k` is
  nonzero in `k`.

## Main result

`map_coeff_zero_mem k I S M hM`: let `k` be algebraically closed. Let `S` be
an additive subgroup of the matrices `Matrix m n A`, and let `M` be a matrix
of Laurent polynomials such that `M.map φ ∈ S` for every `k`-algebra map
`φ : A[I → ℤ] →ₐ[k] A`. Then the matrix of constant coefficients
`M.map (fun f => f.coeff 0)` lies in `S`.

Proof. Choose a bound `B` on the absolute values of all exponent coordinates
occurring in `M`. Choose two distinct primes `ℓ₁, ℓ₂` larger than `B` and
`ringChar k`. Since `k` is algebraically closed, it contains primitive `ℓ`-th
roots of unity (`HasEnoughRootsOfUnity`). By `sum_laurentEval`,
`ℓ^|I| • M.map coeff₀` is a sum of evaluations of `M`, so it lies in `S`, for
both primes. The two multiples `ℓ₁^|I|` and `ℓ₂^|I|` are coprime, so a Bezout
combination with integer coefficients gives `M.map coeff₀ ∈ S`.

## Provenance

This is an internal lemma. In the proof of Theorem 16.26(a) it plays the role
of Milne 2017, Theorem 15.34(d): over an algebraically closed field, an
extension of a group of multiplicative type by an algebraic subgroup `U` of
`G_a`, with action restricted from a linear action on `G_a`, splits
(`Ext¹(G, U) = 0`). It lets the averaging argument handle layers whose
subgroup `S` is not a `k`-subspace, for example finite or non-reduced
subgroups of `G_a` in positive characteristic. The constant coefficient is
the torus average behind the vanishing of Hochschild cohomology with linear
coefficients (Milne 2017, Remark 15.17 and Proposition 15.31). The lemma
shows that this average is an integral combination of evaluations at torsion
points, so it stays inside every additive subgroup that contains all the
evaluations. Milne proves 15.34(d) differently, through the exact sequence
`0 → U → G_a → G_a → 0`.
