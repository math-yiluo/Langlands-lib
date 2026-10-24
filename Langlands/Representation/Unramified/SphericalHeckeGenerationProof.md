# Generation of the spherical Hecke algebra by the standard elements up to central powers

Authors: Worker 267 (this module, the assembly), Worker 257
(`StandardMonomial`, `StandardMonomialSupport`) and Worker 202
(`StandardMonomialTop`).

The closing theorem is `Langlands.Unramified.sphericalHeckeGeneration`. Its type
is exactly `Langlands.Unramified.SphericalHeckeGenerationStatement.{uF}`. It
applies `sphericalHeckeGeneration_of_triangularity` to
`standardMonomialTriangularity F`, which is proved in
`Langlands.Representation.Unramified.StandardMonomialTop`.

The module imports the statement module, which is unchanged. It repeats, as local
instances, the field and `GL_n` structures of
`Langlands.Representation.Unramified.HeckeOperators`, so the algebra is the
Library's spherical Hecke algebra. The proof adds no hypothesis. It uses no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.

## Triangularity input

`StandardMonomialTriangularity F` is the interface proposition of
`Langlands.Representation.Unramified.StandardMonomial`. It concerns the standard
monomial `M_a = T_0^{a_0} ⋯ T_n^{a_n}` with exponent `λ = monomialExponent a`.

1. `M_a` is supported in double cosets `K ϖ^ν K`, where `ν` is antitone and
   dominated by `λ` with the same total. This is `standardMonomial_support` in
   `StandardMonomialSupport`.
2. `M_a(ϖ^λ) ≠ 0`. This is `standardMonomial_top_ne_zero` in
   `StandardMonomialTop`.

The theorem `standardMonomialTriangularity` in `StandardMonomialTop` combines the
two clauses. The rest of this file describes the assembly, which uses only the
proposition `StandardMonomialTriangularity` as its input.

The proof avoids the Satake transform. It follows the direct route sketched in the
task context, which goes back to Gross, *On the Satake isomorphism* (1998), Prop. 2.6
and (2.7)–(2.9): double cosets `K ϖ^λ K` with `λ` dominant form a basis, and
products of standard elements are triangular for the dominance order. Below,
`K = sphericalOpenSubgroup F r`, `n = r + 1`, `ϖ = standardUniformizer F`, and
`ϖ^ν = standardTorus F ν`. All auxiliary declarations are in the namespace
`Langlands.Unramified.SphericalGeneration`.

## Double cosets and the Cartan decomposition

- `cosetSet g` is the set `K g K`, and `cosetElement g` is its double-coset element
  in the corner. Because `K` has mass one, `cosetElement_apply` identifies
  `cosetElement g` with the indicator function of `K g K`, using
  `doubleCoset_apply_of_mass_one` and `sphericalHaar_real_self`.
- `exists_antitone_mem`: every `g` lies in `K ϖ^λ K` for an antitone `λ`. This is
  `GeneralLinear.Cartan.exists_cartan`, applied with
  `standardUniformizer_isUniformizing` from `StandardMonomialSupport`.
- `eq_of_torus_mem`: if `ϖ^ν ∈ K ϖ^ν' K` with `ν`, `ν'` antitone, then `ν = ν'`.
  This is `GeneralLinear.Cartan.exponent_unique`.

## Expansion along double cosets

`eq_sum_of_support` proves the following. Let `S` be a finite set of antitone
exponents, and let `f` be a spherical element whose support lies in the union of
the `K ϖ^ν K` for `ν ∈ S`. Then `f = ∑_{ν ∈ S} f(ϖ^ν) • torusHeckeElement F ν`.

Both sides are compared pointwise with `Corner.ext'`, after evaluation through the
linear functional `evalAt x`. Suppose `x` lies in `K ϖ^μ K` for some `μ ∈ S`. Then
only the `μ` term survives, since `eq_of_torus_mem` shows that the double cosets of
distinct members of `S` are disjoint. By bi-invariance, the value `f x` equals
`f(ϖ^μ)` (`apply_eq_of_mem_doubleCosetSet`). Otherwise every term vanishes, and so
does `f x` by the support hypothesis.

## Exponents of standard monomials

- `gapExponent λ : Fin (r + 2) → ℕ` lists the successive gaps of `λ`. Entry
  `i + 1` is `λ_i - λ_{i+1}`, the last entry is `λ_r`, and entry `0` is `0`.
- `monomialExponent_sub` shows that consecutive entries of `monomialExponent a`
  differ by `a (j + 1)`. `monomialExponent_last` shows that the last entry is the
  last entry of `a`.
- `monomialExponent_gapExponent`: if `λ` is antitone with `λ_r ≥ 0`, then
  `monomialExponent (gapExponent λ) = λ`. The proof is a downward induction from
  the last index.
- `standardMonomial_mem`: every standard monomial, which is a list product of
  powers of standard elements, lies in
  `A = Algebra.adjoin ℂ (Set.range (standardHeckeElement F r))`.

## Dominance weight

`tailSum ν k` is the sum of the entries `ν_j` with `j ≥ k`
(`GeneralLinear.Cartan.tailSum`). `weight ν` is the sum of the tail sums
`tailSum ν k` over `k = 0, …, r`.

- `weight_le`: for `ν ≥ 0`, `weight ν ≤ n · ∑ ν`, because each tail sum is at most
  the total (`tailSum_le_total`).
- `weight_lt`: if every tail sum of `ν` is at least that of `λ` and `ν ≠ λ`, then
  `weight λ < weight ν`. Equality of all the tail sums for `k ≤ r` would give
  `ν = λ` by `eq_of_tailSum_eq`. Tail sums for `k > r` vanish (`tailSum_of_le`).
- `nonneg_of_dominated`: suppose `ν` is antitone, `tailSum λ k ≤ tailSum ν k` for
  every `k`, and `λ_r ≥ 0`. When the totals agree, the tail-sum inequality says
  that `ν` is dominated by `λ`. Then `ν ≥ 0`, because the tail sums at `k = r` give
  `λ_r ≤ ν_r` (`tailSum_last`), and `ν` is antitone.

## Triangular induction

`torusHeckeElement_mem` assumes `StandardMonomialTriangularity F`. It proves that
`torusHeckeElement F λ ∈ A` for every antitone `λ` with `λ_r ≥ 0`. The proof is an
induction on a natural number `N` that bounds `n · ∑ λ - weight λ` strictly from
above. When `N = 0` the bound is impossible, by `weight_le`. In the inductive step,
let `T = ∑ λ`, let `M` be the standard monomial of `gapExponent λ`, and let `S` be
the finite set of antitone `ν ∈ [0, T]^n` with total `T` and
`tailSum λ k ≤ tailSum ν k` for every `k`, that is, the `ν` dominated by `λ`.
Triangularity and `monomialExponent_gapExponent` give two facts. First, the
support of `M` lies in the union of the `K ϖ^ν K` for `ν ∈ S`. Second,
`M(ϖ^λ) ≠ 0`. `eq_sum_of_support` then writes `M` as
`M(ϖ^λ) • torusHeckeElement F λ + R`. Every `ν ∈ S` other than `λ` has the same
total and a strictly larger weight (`weight_lt`), so the induction hypothesis puts
`R` in `A`. Hence `torusHeckeElement F λ = M(ϖ^λ)⁻¹ • (M - R) ∈ A`.

## The central shift

- `standardDiagonal_last`: the last standard diagonal element is the scalar matrix
  `ϖ · 1`. It is central (`standardDiagonal_last_mem_center`), and its powers
  shift exponents: `z^m ϖ^λ = ϖ^{λ + m}` (`pow_standardDiagonal_last_mul_torus`).
- `pow_mul_cosetElement`: `T_n^m * cosetElement x = cosetElement (z^m x)` for
  `z = standardDiagonal F r (Fin.last (r + 1))`. The proof is an induction on `m`
  with `Corner.doubleCoset_mul_mul_of_mem_normalizer`, since a central element
  normalizes `K`, and `Corner.doubleCoset_one`.

## Generation

`exists_pow_mul_mem` assumes triangularity and shows that every spherical `f` has
some `m` with `T_n^m * f ∈ A`. The corner is the span of its double-coset elements
(`Corner.span_range_doubleCoset`), and the proof is a span induction:

- For a double coset `K g K`, choose an antitone `λ` with `g ∈ K ϖ^λ K`, and take
  `m = max(0, -λ_r)`. Then `T_n^m * cosetElement g = torusHeckeElement F (λ + m)`.
  The shifted exponent is antitone with nonnegative last entry, so
  `torusHeckeElement_mem` applies.
- Zero needs `m = 0`.
- For a sum, use `m₁ + m₂`, since `T_n ∈ A`.
- For a scalar multiple, keep the same `m`.

`sphericalHeckeGeneration_of_triangularity` introduces `p`, `F`, `r` and `f`, and
applies `exists_pow_mul_mem`. Then `sphericalHeckeGeneration` supplies
`standardMonomialTriangularity F` for every `F`.
