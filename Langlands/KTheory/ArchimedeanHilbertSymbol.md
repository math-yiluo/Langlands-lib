# Archimedean Hilbert symbols

The module defines the Hilbert pairings on the units of the actual real and
complex fields. Mathlib's `rootsOfUnity n F` is the subgroup of `Fˣ` whose
elements have `n`th power `1`.

## Source and normalization

Moore defines the integer-valued sign-pair cocycle in the paragraph introducing
`S₀(A)` on p. 170. Its value is `1` on pairs of negative real units and `0`
otherwise. He identifies its reduction modulo two with the real norm residue
symbol. With the multiplicative identification `0 ↦ 1` and `1 ↦ -1`, this
gives the formula used in `realQuadraticHilbertSymbol`. The order-one real
formula follows because `μ₁(ℝ)` has only the identity. In the complex case
Moore gives the trivial cocycle, which yields the constant identity in each
`μₙ(ℂ)` for positive `n`.

C. C. Moore, *Group extensions of p-adic and adelic linear groups*,
Publications Mathématiques de l'IHÉS 35 (1968), 5–70, §3, printed p. 170
(PDF p. 14) and Theorem 3.2 on printed pp. 171–172 (PDF pp. 15–16).
Literature ID `moore-1968-group-extensions`, SHA-256
`dfd467339cc20e6eb9bd5d3fbdb06ea2fea8efebdeb479ccaaa4a12529a740d4`.

## Constructions and evaluations

- `realQuadraticHilbertSymbol` has codomain `rootsOfUnity 2 ℝ`.
  Its right-hand homomorphism law follows by the four possible signs of the
  two factors when the fixed argument is negative, using `(-1)² = 1`.
  When the fixed argument is positive the map is constant `1`. Symmetry of
  the sign condition gives the left-hand homomorphism law.
  `realQuadraticHilbertSymbol_apply` gives the formula in the root group with
  `realQuadraticNegOne` as the negative value, and
  `realQuadraticHilbertSymbol_coe` gives it in `ℝ`.
  `realQuadraticHilbertSymbol_eq_neg_one_iff` and
  `realQuadraticHilbertSymbol_eq_one_iff` give the two value criteria in the
  root group.
- `exists_isPrimitiveRoot_real_iff` proves that a positive `n` admits a
  primitive real root exactly for `n = 1` or `n = 2`. A real root of unity
  is `1` or `-1` by the ordered-ring power criterion. The orders of these two
  roots are `1` and `2`.
- `realOrderOneHilbertSymbol` has constant value `1` in `rootsOfUnity 1 ℝ`.
  `realHilbertSymbol n hn` uses `hn : n = 1 ∨ n = 2` to choose the pairing in
  `rootsOfUnity n ℝ`. `realHilbertSymbol_one` and `realHilbertSymbol_two`
  identify the two specializations. Its value in `ℝ` is `-1` exactly when
  `n = 2` and both inputs are negative, and `1` otherwise
  (`realHilbertSymbol_coe`).
- `complexHilbertSymbol n` for `[NeZero n]` has constant value `1` in
  `rootsOfUnity n ℂ` (`complexHilbertSymbol_apply`).

All pairings are curried `MonoidHom`s, so the homomorphism laws apply in
each variable.
