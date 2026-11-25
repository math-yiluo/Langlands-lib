# The Weil index in the unramified case

**GKT §3.2.4**: **Lemma 3.23**, **Propositions 3.24** and **3.25** (p. 86), **Corollary 3.26**
(p. 87).

The module `Langlands.Theta.WeilIndex.Unramified` gives conditions under which a Weil index is `1`,
by exhibiting a self-dual ball on which the character of second degree is trivial (GKT
Corollary 3.11, `weilIndex_eq_one`). `F` is a nonarchimedean local field with `2 ≠ 0` and valuation
`v` (`ValuativeRel`), `ψ` a non-trivial unitary character of `F`.

## Content

- `UnitaryAdditiveCharacter.IsConductor ψ c` (`c ∈ Fˣ`): `ψ` is trivial on the ball
  `{v x ≤ v c}` and non-trivial on every ball `{v x ≤ v s}` with `v s > v c`. This is the book's
  "`ϖ^r O` is the conductor of `ψ`, so that `ψ` is trivial on `ϖ^r O` but not on `ϖ^{r-1} O`" with
  `c = ϖ^r`, stated without a uniformizer.
- `secondDegreeBicharacter_mul_sq`: the bicharacter of `x ↦ ψ(a x²)` is `ψ(2 a x y)`.
- **Lemma 3.23** (`annihilator_valuationBall`): if `ψ` has conductor `c`, the annihilator of the
  ball `{v x ≤ v t}` for `ψ(2 a x y)` is the ball `{v x ≤ v((2 a t)⁻¹ c)}`. Proof: for `v z` at most
  that radius, `v(2 a y z) ≤ v(c)` on the ball; otherwise `s = 2 a t z` has `v s > v c`, the
  conductor gives `w` with `v w ≤ v s` and `ψ(w) ≠ 1`, and `y = w / (2 a z)` lies in the ball. For
  `a = 1` and `t = ϖ^{⌈r/2⌉}` (the book's `L_b`) this is the book's `L_b^∨ = ϖ^{r/2 - e} O` or
  `ϖ^{(r-1)/2 - e} O` (`2 O = ϖ^e O`): the factor `2` enters through `v(2)`.
- **Proposition 3.24** (`weilIndexOne_scale_eq_one`): if `v(2) = 1` (odd residue characteristic),
  `ψ` has conductor `c` and `v(c) = v(a) v(t)²` for some `t ∈ Fˣ` (the book's "`r + s` even" with
  `s = ord(a)`), then `γ(ψ_a) = 1`: the ball `{v ≤ v t}` is self-dual and `ψ(a x²) = 1` on it.
  `weilIndexOne_eq_one_of_isConductor_one`: unramified `ψ` (`c = 1`) has `γ(ψ) = 1`.
- **Proposition 3.25** (`weilIndex_diagonal_eq_one` for `∑ aᵢ xᵢ²`,
  `weilIndex_eq_one_of_isometryEquiv` for a quadratic space isometric to it, through Corollary 3.14)
  and **Corollary 3.26** (`weilIndex_eq_one_of_isConductor_one`: `ψ` unramified, all `aᵢ` units).

The book's Proposition 3.24 (p. 86) says "the conductor of `ψ_a` is `ϖ^{r+s} O`"; since
`ψ_a(x) = ψ(a x)` is trivial exactly when `a x ∈ ϖ^r O`, the conductor of `ψ_a` is `ϖ^{r-s} O`. The
parity of `r + s` and `r - s` is the same, so the conclusion is unaffected.

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025), §3.2.4:
Lemma 3.23, Propositions 3.24, 3.25, p. 86; Corollary 3.26, p. 87.

## Declarations

- `Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.IsConductor`.
- `Langlands.Theta.secondDegreeBicharacter_mul_sq`, `annihilator_valuationBall`,
  `weilIndexOne_scale_eq_one`, `weilIndexOne_eq_one_of_isConductor_one`,
  `weilIndex_diagonal_eq_one`, `weilIndex_eq_one_of_isometryEquiv`,
  `weilIndex_eq_one_of_isConductor_one`.

Internal (`Langlands.Theta.WeilIndex.Internal`): `mem_valuationBall_iff`,
`valuationBallSubgroup`, `coe_valuationBallSubgroup`, `mul_mem_valuationBall_iff`.

## Dependencies

`Langlands.Theta.WeilIndex.OneDimensional`.
