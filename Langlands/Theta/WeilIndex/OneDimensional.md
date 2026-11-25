# The Weil index in dimension one

**GKT §3.2.1–3.2.3**: **Proposition 3.13** (c) and **Corollary 3.14** (p. 81) for quadratic forms,
**Corollary 3.15** (p. 81), the reduction to dimension one (p. 82), **Proposition 3.17**
(pp. 82–84), **Lemma 3.18**, **(3.20)** and **Proposition 3.19** (pp. 84–85), **Corollaries 3.20**
and **3.22** (pp. 85–86). (Proposition 3.13 (a), (b), (d), (e) for characters of second degree are
in `Langlands/Theta/WeilIndex/Defs.lean`.)

The module `Langlands.Theta.WeilIndex.OneDimensional` treats the Weil indices `γ(ψ_a)` of the
one-dimensional forms `x ↦ a x²` over a nonarchimedean local field `F` with `2 ≠ 0`, their relation
with the Hilbert symbol (`Langlands/ClassFieldTheory/Local/HilbertSymbol.lean`), and their
consequences for quadratic forms. `ψ` is a non-trivial unitary character of `F`
(`UnitaryAdditiveCharacter F`), `ψ_a = ψ.scale a = ψ(a ·)`.

## Content

- `weilIndexOne ψ`: the book's `γ(ψ) = γ(ψ ∘ q₁)`, `q₁(x) = x²`; `weilIndexOne (ψ.scale a)` is
  `γ(ψ_a) = γ(ψ ∘ q_a)` ((3.19); `weilIndexOne_scale`). `isCharacterOfSecondDegree_mul_sq`:
  `x ↦ ψ(a x²)` is a character of second degree (bicharacter `ψ(2a x y)`).
  `norm_weilIndexOne`, `weilIndexOne_ne_zero`.
- `normalizedWeilIndex a ψ = γ(ψ_a) / γ(ψ)`: the normalized Weil index `γ(a, ψ)` ((3.20));
  `norm_normalizedWeilIndex`.
- Proposition 3.13 (b) in dimension one: `weilIndexOne_scale_neg` (`γ(ψ_{-a}) = γ(ψ_a)⁻¹`).
- Lemma 3.18: `weilIndexOne_scale_mul_sq` (`γ(ψ_{ab²}) = γ(ψ_a)`, through `x ↦ b x`),
  `weilIndexOne_scale_sq`.
- Reduction to dimension one (p. 82): `weilIndex_diagonal` (`γ(ψ ∘ ∑ aᵢ xᵢ²) = ∏ γ(ψ_{aᵢ})`, from
  `weilIndex_pi`), `isCharacterOfSecondDegree_diagonal`; `exists_weilIndex_eq_prod`: a quadratic form
  with non-degenerate polar form is isometric to a diagonal one (Mathlib's
  `equivalent_weightedSumSquares_units_of_nondegenerate'`), so `γ(ψ ∘ q) = ∏ γ(ψ_{aᵢ})`;
  `separatingLeft_associated_iff`.
- Corollary 3.14: `weilIndex_quadraticForm_isometryEquiv`: isometric quadratic spaces (with
  non-degenerate polar forms) have the same Weil index; Proposition 3.13 (c):
  `weilIndex_sq_eq_one_of_isSquare_neg_one` (`γ(ψ ∘ q)² = 1` if `-1` is a square: `x ↦ √-1 x`
  turns `ψ ∘ q` into its conjugate). Both hold in every characteristic.
- `weilIndexOne_mul_four`: **`γ(ψ) γ(ψ_{-a}) γ(ψ_{-b}) γ(ψ_{ab}) = (a, b)_F`**, the Weil index of the
  norm form `⟨1, -a, -b, ab⟩` of the quaternion algebra `(a, b)_F`. The book derives it from
  Proposition 3.17 and the isomorphism of `⟨1, -a, -b, ab⟩` with the hyperbolic space or with the
  norm form of the division quaternion algebra (proof of Proposition 3.19, pp. 84–85). Here: for a
  square `a` the form is hyperbolic (Lemma 3.18 and 3.13 (b)); otherwise it is `N ⊕ (-b) N` for the
  norm form `N` of `E = F(√a)` (`QuadraticAlgebra F a 0` with its module topology; internal lemma
  `weilIndex_mul_norm_quadraticAlgebra`: `γ(ψ ∘ t N) = γ(ψ_t) γ(ψ_{-at})`), and
  `γ(ψ ∘ t N) = η(t) γ(ψ ∘ N)` (`weilIndex_mul_norm`) with `η = (a, ·)_F`
  (`normSign_eq_hilbertSymbol`) gives `γ(ψ ∘ N)² = η(-1)` (from `γ(ψ ∘ (-N)) = γ(ψ ∘ N)⁻¹`) and
  `γ(ψ ∘ (N ⊕ (-b) N)) = η(-b) γ(ψ ∘ N)² = η(b) = (a, b)_F`. No division quaternion algebra, no lattice
  in it, and no uniqueness of it (Proposition B.53) is used.
- Proposition 3.17: `weilIndex_quaternion`: for the quaternion algebra `D = QuaternionAlgebra F a 0 b`
  (`i² = a`, `j² = b`) with the reduced norm `N_D(x) = (x x̄)` (Proposition B.50: `x² - a y² - b z² +
  ab w²`) and its module topology, `γ(ψ ∘ N_D) = (a, b)_F`; `weilIndex_quaternion_of_isUnit`: if `D` is
  a division algebra, `γ(ψ ∘ N_D) = -1` (a solution of `x² - a y² = b` gives a non-zero quaternion
  `x + y i + j` of norm zero). The book's statement is for "the" division quaternion algebra (unique
  up to isomorphism, B.53); the theorem here holds for each quaternion algebra that is a division
  algebra.
- Proposition 3.19: `normalizedWeilIndex_mul_sq` ((a)), `normalizedWeilIndex_mul` ((b):
  `γ(ab, ψ) = γ(a, ψ) γ(b, ψ) (a, b)_F`); `normalizedWeilIndex_one`, `normalizedWeilIndex_inv`
  (`γ(a⁻¹, ψ) = γ(a, ψ)`).
- Corollary 3.20: (a) `normalizedWeilIndex_scale`; (b) `normalizedWeilIndex_neg_one`; (c)
  `normalizedWeilIndex_sq`, `normalizedWeilIndex_sq'`, `inv_normalizedWeilIndex`; (d)
  `normalizedWeilIndex_pow_four`; (e) `weilIndexOne_pow_four` (`γ(ψ)⁴ = (-1, -1)_F`, also for every
  `ψ_a`), `weilIndexOne_pow_eight`.
- Corollary 3.22: `normalizedWeilIndex_pow` (`γ(a^k, ψ) = (a, a)_F^{k(k-1)/2} γ(a, ψ)^k`, `k ≥ 0`,
  with `k(k-1)/2 = k.choose 2`), `normalizedWeilIndex_zpow_neg` (`γ(a^{-k}, ψ)` for `k ≥ 0`; the book's
  formula `(a, a)^{(-k)(-k-1)/2} γ(a, ψ)^{-k}` agrees with it since `γ(a, ψ)^{-1} = (a, a)_F γ(a, ψ)`
  and `(a, a)_F^{2k} = 1`).
- Corollary 3.15: `weilIndex_pow_eight`: `γ(ψ ∘ q)⁸ = 1` for every quadratic form with non-degenerate
  polar form, by the reduction to dimension one and Corollary 3.20 (e) (the direct proof the book
  mentions in Remark 3.21) instead of the structure of the Witt group.

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025), chapter 3:
Proposition 3.13, Corollaries 3.14, 3.15, p. 81; Remark 3.16 and the reduction to dimension one,
p. 82; Proposition 3.17, pp. 82–84; Lemma 3.18, (3.20), Proposition 3.19, pp. 84–85; Corollary 3.20,
Remark 3.21, Corollary 3.22, pp. 85–86; Appendix B.3, Proposition B.50, p. 624.

## Declarations

- `Langlands.Theta.weilIndexOne`, `normalizedWeilIndex`.
- `isCharacterOfSecondDegree_mul_sq`, `weilIndexOne_scale`, `norm_weilIndexOne`,
  `weilIndexOne_ne_zero`, `weilIndexOne_scale_neg`, `weilIndexOne_scale_mul_sq`,
  `weilIndexOne_scale_sq`, `weilIndex_diagonal`, `isCharacterOfSecondDegree_diagonal`.
- `weilIndex_quadraticForm_isometryEquiv`, `weilIndex_sq_eq_one_of_isSquare_neg_one`.
- `weilIndexOne_mul_four`, `weilIndex_quaternion`, `weilIndex_quaternion_of_isUnit`.
- `normalizedWeilIndex_one`, `normalizedWeilIndex_mul_sq`, `normalizedWeilIndex_mul`,
  `norm_normalizedWeilIndex`, `normalizedWeilIndex_scale`, `normalizedWeilIndex_neg_one`,
  `normalizedWeilIndex_sq`, `normalizedWeilIndex_sq'`, `inv_normalizedWeilIndex`,
  `normalizedWeilIndex_pow_four`, `weilIndexOne_pow_four`, `weilIndexOne_pow_eight`,
  `normalizedWeilIndex_inv`, `normalizedWeilIndex_pow`, `normalizedWeilIndex_zpow_neg`.
- `separatingLeft_associated_iff`, `exists_weilIndex_eq_prod`, `weilIndex_pow_eight`.

Internal (`Langlands.Theta.WeilIndex.Internal`): `conj_complex`, `complex_sum`,
`linearEquivToContinuousAddEquiv`, `linearEquivToContinuousAddEquiv_apply`,
`secondCountableTopology_self`, `locallyCompactSpace_self`, `compactOpenExhaustion_self` (used as
local instances in this file).

## Dependencies

`Langlands.Theta.WeilIndex.NormForm` (and through it `WeilIndex.Defs`),
`Langlands.ClassFieldTheory.Local.HilbertSymbol`, `Langlands.HarmonicAnalysis.CharacterTransport`;
Mathlib: `Algebra.Quaternion`, `LinearAlgebra.QuadraticForm.IsometryEquiv`.
