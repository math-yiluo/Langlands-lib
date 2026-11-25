# Determinant twists in the JPSS integrals of a pair

This is a helper module for the proof of
`Langlands.RankinSelberg.PairGammaTwistExchangeStatement`. Its declarations are in the
namespace `Langlands.RankinSelberg.PairGammaTwistExchange`. It extends the rank-one helper
`RankOneGammaTwistAlgebra` / `RankOneGammaTwistIntegrals` from a rank-one test to a test of
arbitrary rank.

Throughout, `π` is a representation of `GL_(r+1)(F)` (the candidate), `σ` a representation
of `GL_(n+1)(F)` (the test), and `χ : Fˣ →* ℂˣ` is any group homomorphism. No genericity,
smoothness, central character, continuity of `χ` or nonvanishing of functionals is assumed.

## Determinant signs

- `determinant_weylLong_add`: `det w_(a+b) = (-1)^(ab) · det w_a · det w_b`. The proof is
  by induction on `b` from the published one-step recurrence
  `RankOneGammaTwist.determinant_weylLong_succ`.
- `determinant_blockWeyl`: the actual block matrix `blockWeylAt n r hnr`
  (`diag(1_(n+1), w_(r-n))`) has determinant `det w_(r-n)`. It uses the block determinant
  `Matrix.det_fromBlocks_zero₂₁` after the reindexing of `blockSum`.
- `determinant_weyl_ratio` and `determinant_dual_arguments`: for `n < r` and
  `det g = det a`,

  `det(w_(r+1) · (g · blockWeylAt n r hnr)^ι) = (-1)^((n+1)(r-n)) · det(w_(n+1) · a^ι)`,

  where `x^ι` is `inverseTranspose`.
- `determinant_neg_one`: `det(-1) = (-1)^(m+1)` in `GL_(m+1)`.
- `sign_exponent`: for `n ≤ r`, `χ(-1)^((n+1)(r-n)) = (χ(-1)^(n+1))^r`. This holds because
  `(n+1)r = (n+1)(r-n) + n(n+1)`, `n(n+1)` is even and `χ(-1)^2 = 1`
  (`RankOneGammaTwist.character_negOne_sq`).
- `character_negOne_mul_self`: `χ(-1) · χ(-1) = 1` in `ℂ`.

## Functionals and models

`twisted χ ρ ℓ` and `untwisted χ ρ ℓ` are the published `twistFunctional` and
`untwistFunctional` (`Representation/Whittaker/AlgebraicTwist.lean`) for the character
`χ ∘ det`, which is trivial on the upper unipotent group (`determinantCharacter_unipotent`).
Both keep the same underlying linear map, so `twisted χ ρ (untwisted χ ρ ℓ)` is `ℓ`
definitionally. They are generic in the character `θ` of the unipotent group, so they apply
to Whittaker functionals of the candidate and to inverse Whittaker functionals of the test.

- `twisted_coefficient`: the coefficient of `v` in the twisted model is
  `g ↦ χ(det g) · W_v(g)` (from `twistFunction_coefficient`).
- `minusOne_twist`: if the model of `ρ` (rank `m+1`) has minus-one scalar `ζ`
  (`HasModelMinusOneScalar`), the twisted model has `ζ · χ(-1)^(m+1)`.
- `minusOne_untwist`: conversely, if the twisted model has minus-one scalar `ζ`, the
  original model has `ζ · χ(-1)^(m+1)`. The proof cancels the nonzero factor
  `χ(-1)^(m+1) χ(det g)` and uses `(χ(-1)^(m+1))^2 = 1`.

## Integral comparisons

Pointwise identities between products of coefficient functions are pushed through the
iterated Bochner integrals with `integral_const_mul` and `integral_congr_ae`; no
integrability hypothesis is needed, because both sides are rewritten pointwise.

- `unequal_integral_scale`: if `W₁(g) W₁'(a) = c · W₂(g) W₂'(a)` whenever
  `det g = det a`, then the block integrals `unequalRankIntegralAt j k hr` of the two pairs
  differ by `c`, for every block pair, quotient measure and rectangular measure. It uses
  the published `determinant_unequalRankMatrix`.
- `equal_integral_eq`: the equal-rank integrals `equalRankIntegral` agree when the
  pointwise products agree, for every Schwartz–Bruhat test.
- `forward_product`: for `det g = det a`,
  `χ(det g) W_v(g) · W'_z(a) = W_v(g) · χ(det a) W'_z(a)`.
- `unequal_dual_product`: for `n < r` and `det g = det a`, the integrands of the dual
  integrals (actual `translateWhittaker` by `blockWeylAt n r hn` after
  `firstDualFunction`, and `secondDualFunction`) for `(π ⊗ χ, σ)` and `(π, σ ⊗ χ)` differ by
  the factor `χ(-1)^((n+1)(r-n))`, by `determinant_dual_arguments`.
- `equal_dual_product`: in equal rank the dual integrands agree.

The resulting theorems, with the same underlying functionals on both sides, are:

- `unequal_forward`: every forward block integral of `(π ⊗ χ, σ)` equals the one of
  `(π, σ ⊗ χ)`;
- `unequal_dual`: for `n < r`, every dual block integral
  (`dualUnequalRankModelIntegralAt`) of `(π ⊗ χ, σ)` is `χ(-1)^((n+1)(r-n))` times the one
  of `(π, σ ⊗ χ)`;
- `equal_forward` and `equal_dual`: for `r = n`, the forward and dual equal-rank model
  integrals of the two pairs agree for every Schwartz–Bruhat test.

## Provenance

These are internal computations from the Library's definitions of the JPSS integrals,
which follow H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, Amer. J. Math. 105 (1983), 367–464 (`jpss-1983-rankin-selberg`): the Weyl
and inverse-transpose conventions of (0.3), printed p. 376 (PDF 11), the dual function of
(2.1), printed pp. 385–386 (PDF 20–21), and the integrals (2.4), printed p. 387 (PDF 22).
The source states no such twist identity; the computation is the derivation sketched in
the statement's Markdown (`PairGammaTwistExchangeStatement.md`), in the Lean rank indexing
(candidate rank `r+1`, test rank `n+1`).
