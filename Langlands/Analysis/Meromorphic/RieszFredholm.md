# Riesz theory: identity plus a compact operator is Fredholm

Module `Langlands.Analysis.Meromorphic.RieszFredholm` (namespace
`Langlands.Analysis.Meromorphic.RieszFredholm`) is a helper for the proof of
Bernstein–Lapid's Fredholm criterion
(`Langlands.Analysis.Meromorphic.FredholmCriterionProof`). It proves the
classical Riesz theory fact used in that proof: for a compact operator `K` on a
complex Banach space, `1 + K` is Fredholm, and so it is left invertible modulo
finite-rank operators. The pinned Mathlib has the Fredholm API
(`IsFredholm`, `IsFredholm.add_hasFiniteRange`, `IsFredholm.exists_isQuasiInverse`)
and the Fredholm alternative for compact operators
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`), but not this
statement.

`X` is a complex normed space throughout. `X` is assumed complete from
`isFredholm_id_add` on.

## Results

- `finiteDimensional_ker_id_add`: if `K` is compact, then `ker (1 + K)` is
  finite-dimensional. On the closed subspace `V = ker (1 + K)`, `K` acts as
  `-1`. So the identity of `V` is the restriction of the compact operator `-K`,
  hence compact, and `V` is finite-dimensional by Riesz's theorem
  (`FiniteDimensional.of_isCompactOperator_id`).
- `hasFiniteRange_smulRight`, `isCompactOperator_smulRight`: the rank-one
  operator `x ↦ f x • y`, for a continuous linear form `f` and a vector `y`, has
  finite range and is compact. It factors through `ℂ`.
- `isFredholm_id_add`: if `X` is a Banach space and `K` is compact, then
  `1 + K` is Fredholm (`IsFredholm`). The proof is by strong induction on
  `n = dim ker (1 + K)`, generalizing over `K`:
  - If `1 + K` is surjective, Mathlib's criterion
    `Function.Surjective.isFredholm_iff` applies. The map is a quotient map by
    the open mapping theorem. Its kernel is finite-dimensional, hence closed and
    complemented.
  - Otherwise pick `y` outside the range. If the kernel were `0`, then `-1`
    would not be an eigenvalue of `K`. The Fredholm alternative would then make
    `1 + K` invertible, contradicting non-surjectivity. So pick `x ≠ 0` in the
    kernel and, by Hahn–Banach (`exists_dual_vector`), a form `f` with
    `f x ≠ 0`. Set `K' = K + (x ↦ f x • y)`, which is compact.
  - Then `ker (1 + K')` is strictly smaller than `ker (1 + K)`. If
    `(1 + K') v = 0`, then `(1 + K) v = -(f v) y`. Since `y` is not in the range,
    `f v = 0`, so `v ∈ ker (1 + K)`. Also `x` is in `ker (1 + K)` but not in
    `ker (1 + K')`.
  - By induction `1 + K'` is Fredholm. So `1 + K = (1 + K') - (x ↦ f x • y)` is
    Fredholm by `IsFredholm.add_hasFiniteRange`.
- `exists_leftInverse_mod_finiteRank`: if `A : X →L[ℂ] C` and `D : C →L[ℂ] X`
  are such that `D ∘ A - 1` is compact, then there are `G : C →L[ℂ] X` and
  `F : X →L[ℂ] X` with finite-dimensional range such that `G ∘ A = 1 - F`.
  Apply `isFredholm_id_add` to `1 + (D ∘ A - 1) = D ∘ A`. Take a quasi-inverse
  `Q` (`IsFredholm.exists_isQuasiInverse`), set `G = Q ∘ D` and
  `F = 1 - Q ∘ D ∘ A`, which has finite range by the left quasi-inverse
  property.

## Provenance

This is standard Riesz–Schauder theory. Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §3.4,
p.194 (registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`; arXiv TeX lines
742–750) recall it with a reference to the literature: `1 - K` is Fredholm for
compact `K`, hence invertible modulo finite-rank operators. The induction on
the kernel dimension via rank-one perturbations is an internal proof route. It
avoids closed-range and codimension arguments and needs only Mathlib's Fredholm
alternative. It does not approximate compact operators by finite-rank ones,
which is impossible in general Banach spaces.
