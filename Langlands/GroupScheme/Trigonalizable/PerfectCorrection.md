# Correcting crossed homomorphisms over perfect fields with connected diagonalizable groups

Module
`Langlands.GroupScheme.Trigonalizable.PerfectCorrection`, namespace
`Langlands.GroupScheme.PerfectCorrection`.

This module proves that the correction equation in the Library's proof of
Milne 15.34(d) (module `LinearAdditiveExtension.Correction`) can be solved over
a perfect field when the diagonalizable group `D(Λ)` is connected. This is the
input for case (c) of Milne 16.26 (`ExtensionSplitPerfectConnected`).

## Declarations

`k` is a field and `k[X]` its polynomial ring.

- `choose_mul_coeff_eq_zero`: if `f` satisfies the Taylor identity
  `taylor X (f.map C) = f.map C + C f` (that is `f(X + Y) = f(X) + f(Y)`),
  then `(i.choose j : k) * f.coeff i = 0` whenever `0 < j < i`. It compares the
  coefficient of `X^j Y^(i-j)` through Mathlib's `hasseDeriv_coeff` and the
  Library's `AdditivePolynomial.taylor_map_coeff`.
- `eq_zero_or_eq_pow_of_coeff_ne_zero`: for `[ExpChar k p]`, a nonzero
  coefficient of such an `f` sits at an index `i` with `i = 0` or `i = p ^ v`.
  For `p` prime this is Mathlib's Lucas-type converse
  `Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat`; for `p = 1`
  (characteristic zero) the coefficient `i.choose 1 = i` forces `i ≤ 1`.
- `eq_one_of_pow_eq_one`: let `R` be a commutative ring with connected prime
  spectrum, `φ : R →+* K` with `K` nontrivial, `w ^ m = 1` with `(m : R)` a
  unit and `φ w = 1`. Then `w = 1`. The element `m⁻¹ ∑_{i<m} wⁱ` is idempotent
  (the Library's `isIdempotentElem_geomSum`), hence `0` or `1`; `φ` rules out
  `0`, and then `(w - 1) m = 0`.
- `eq_one_of_pow_eq_one_of_connectedSpace`: the same for global functions on a
  connected affine scheme, through `X ≅ Spec Γ(X, ⊤)`.
- `charValue_pow_eq_of_coeff_ne_zero`: let `a : K ⟶ 𝔾ₐ` be a closed subgroup
  whose range is stable under the weight action of a character `χ` of an affine
  commutative group `S`, with nonzero closed polynomial `f` of degree `N` (the
  Library's `ClosedAdditivePolynomial.closedPolynomial a`). If the `i`-th
  coefficient of `f` is nonzero, then `χ(d)^i = χ(d)^N` for every point `d` of
  `S` over every test scheme. It takes the `i`-th coefficient of the Library's
  universal scaling identity `comp_C_mul_X_eq` (`f(c₀ X) = c₀^N f(X)`) and
  evaluates it at `d` as in the Library's `eval₂_charValue_mul`.
- `surjective_or_charValue_pow_eq_one`: let `k` be perfect, `D(Λ)` connected,
  `a` a closed subgroup of `𝔾ₐ` stable under the weight action of a character
  `χ` of `D(Λ)`, with nonzero closed polynomial `f` of degree `N`. Then either
  every `m ∈ k` is a value `f(r)` with `r ∈ k`, or `χ(d)^N = 1` for every point
  `d` of `D(Λ)`.

## Proof of `surjective_or_charValue_pow_eq_one`

`f` is monic, `f(0) = 0` and `f` is additive (Library's `taylor_mem_span` and
`taylor_eq_of_mem_span`). With `p` the characteristic exponent, `N = p^s`. If
all coefficients below `N` vanish, `f = X^(p^s)` and the iterated Frobenius
of the perfect field is bijective. Otherwise some coefficient at `i = p^v`,
`v < s`, is nonzero (so `p` is prime). Then `u^(p^v) = u^(p^s)` for the
universal value `u = χ(𝟙)`, so `w = u^(p^v)` satisfies `w^m = 1` with
`m = p^(s-v) - 1`, which is `-1` in `k`. Evaluation at the identity point sends
`w` to `1`, and `D(Λ)` is connected and affine, so `w = 1`. Every value
`χ(d)` is the pullback of `u`, hence `χ(d)^N = (χ(d)^(p^v))^(p^(s-v)) = 1`.

## Source and provenance

This is the mathematics of Milne, *Algebraic Groups* (2017),
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, Theorem
15.34(b),(c) (printed p.319): over a perfect field the correction is possible
for infinitesimal subgroups `α_{p^r}` of `𝔾ₐ`, and for étale subgroups when the
group acting is connected. The Lean statements are derived: they are phrased
with the closed polynomial of the subgroup and the weight character, and the
dichotomy is proved directly from additivity and the scaling identity rather
than through the exact sequences used by Milne. Exercise 14-3 of Milne
(printed p.301) describes the additive polynomials involved.
