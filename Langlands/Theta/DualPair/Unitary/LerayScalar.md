# The scalar at the Weyl element of the Leray splitting of `U(ν, ν)`

**GKT Proposition 12.29** (p. 375), Case `3₊` with `W` split: `β^{V,χ}_{ψ,X}(w) =
γ(ψ_{1/2} ∘ Res_{E/F} V)^{n/2}`, `n/2 = |ν|`, for the function `β` of **(11.3)** (p. 318) and the
symmetric bilinear space `Res_{E/F} V` of **Corollary 11.4** (pp. 315–316); the measure `d𝐱` of
**Proposition 12.27 (1)** (p. 372) is the self-dual one.

The module `Langlands.Theta.DualPair.Unitary.LerayScalar` computes the scalar `lerayScalar c ψ χ Q μ`
by which the Weyl element `w = [[0, 1], [-1, 0]]` of `U(ν, ν)` acts in the Weil representation
`lerayWeil c ν ψ χ Q` of the Leray splitting, relative to the Fourier transform
`φ ↦ ∫ ψ(⟪x, y⟫) φ(y) dμ(y)` (`lerayWeil_weylElement_apply` of
`Langlands/Theta/DualPair/Unitary/LeraySplitting.lean`).

## Setting

`F` a nonarchimedean local field of characteristic zero (the unitary block's hypothesis; the book
allows characteristic `≠ 2`), `E = F(δ)` a quadratic extension with conjugation `c`, `Q` an invertible
Hermitian `α × α` matrix (the Hermitian space `V = E^α` with `(v, w) = vᵀ Q c(w)`), `ψ` a
non-trivial unitary character of `F` (the book's `ψ`), `χ` a continuous character of `Eˣ` with
`χ|_{Fˣ} = η^{|α|}` ((11.2)). `⟪x, y⟫ = hermitianTracePairing c Q x y = tr_{E/F} tr(Qᵀ x c(y)ᵀ)` is
the book's pairing of `𝕏^* = M_{α×ν}(E)` and `𝕏`.

## Content

- `hermitianTraceForm c Q : LinearMap.BilinForm F (α → E)`, `(v, w) ↦ tr_{E/F}(vᵀ Q c(w))`: the book's
  `Res_{E/F} V` (Corollary 11.4: `V` viewed as an `F`-space with `(v, v') ↦ tr_{E/F}(v, v')`); its
  quadratic form in the book's convention (3.1.1) is `q(v) = tr_{E/F}(v, v) = 2 (v, v)`, so the book's
  `γ(ψ_{1/2} ∘ Res_{E/F} V)` is `weilIndex (v ↦ ψ_{1/2}(tr_{E/F}(v, v)))`, the Weil index of
  `v ↦ ψ((v, v))`. Symmetric and non-degenerate (`hermitianTraceForm_symm`,
  `hermitianTraceForm_nondegenerate`, through the matrices with one column and `pr_alg`);
  `isCharacterOfSecondDegree_hermitianTraceForm`.
- `hermitianTracePairing_eq_sum`: `⟪x, y⟫ = ∑_j tr_{E/F}(x_j, y_j)` over the columns `x_j`, `y_j`;
  `hermitianTracePairing_symm`; `isSelfDualBicharacter_hermitianTracePairing`: `ψ ∘ ⟪,⟫` is a
  self-dual bicharacter of `M_{α×ν}(E)`.
- `lerayScalar_eq`: **for every Haar measure `μ`,
  `lerayScalar c ψ χ Q μ = C(μ)^{-1/2} · γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}`**, with
  `C(μ) = bicharacterFourierConstant μ (ψ ∘ ⟪,⟫)` the constant of Fourier inversion
  (`ℱ_μ ℱ_μ φ = C(μ) φ(-·)`; in the book's notation `C(dx) = |β_b|⁻¹` for `b = ⟪,⟫`).
- `lerayScalar_selfDualMeasure`: **for the self-dual measure of `ψ ∘ ⟪,⟫`,
  `lerayScalar = γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}`**, the book's `β(w)` of Proposition 12.29;
  `lerayWeil_weylElement_apply_selfDualMeasure`: `ω(w) φ(x) = γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}
  ∫ ψ(⟪x, y⟫) φ(y) d𝐱(y)`, `d𝐱` the self-dual measure (the third formula of Proposition 12.27 (1)
  with its value of `β(w)`).
- `isLerayWeil_weilIndex`: `lerayWeil c ν ψ χ Q` is `IsLerayWeil` for the Library's character
  `ψ(2 ·)` with the definite scalar `C(μ)^{-1/2} γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}`: with
  `IsLerayWeil.unique`, nothing existential is left in the unitary split case (the scalar of
  `exists_isLerayWeil` is this value).

So the phase of the scalar at the Weyl element is the book's `β(w)` with no complex conjugation and
no factor `χ(-1)^{|ν|}`. This
identifies the Library's scalar with the book's `β(w)` given the Library's Weyl element and Fourier
kernel; that these are the book's `w_{n/2}` and its kernel `ψ(⟪𝐱, x^* ⊗ v⟫) φ(I_{n/2} 𝐱)` is a
statement about the standard operators `r(g)`, not formalized.

## Proof

- `Unitary.Internal.mul_gaussIntegral_eq`: for `IsLerayWeil c ψ' χ Q μ κ ω` (any character `ψ'`) and
  the Gauss integral `γ₀` of `x ↦ ψ'(½ pr(x, x))`, `κ γ₀ = s(det(-1_ν))`, `s = splittingScalar`.
  The relation `w n(1) w = p₀ w n(-1)` of the big cell (`p₀ = [[-1, 1], [0, -1]]`) gives
  `κ² X = κ Y` for `X = ℱ T(n(1)) ℱ φ`, `Y = T(p₀) ℱ T(n(-1)) φ`, and the braid relation
  (`braid_relation`, Weil's formula) gives `s(det(-1)) X = γ₀ Y`; `X ≠ 0`.
- With `ψ' = ψ(2 ·)`, `ψ'(½ pr(x, x)) = ψ(½ ⟪x, x⟫) = f(x)`. The Hermitian Gauss integrals
  (`hasGauss_herm`) at `b = 1` and `b = -1` give the Gauss integrals `γ₀` of `f` and
  `γ₀ s(det(-1)⁻¹)` of `f(-·) = conj f`; the latter is also `conj γ₀` (`HasGaussIntegral.conj`,
  uniqueness `hasGaussIntegral_unique`). With `γ₀ conj γ₀ = C(μ)` (`hasGaussIntegral_mul_conj`):
  `κ C(μ) = κ γ₀ conj γ₀ = s(d) γ₀ s(d⁻¹) = γ₀`, and `γ₀ = C(μ)^{1/2} γ(f)`
  (`hasGaussIntegral_weilIndex`), so `κ = C(μ)^{-1/2} γ(f)`.
- `f(x) = ∏_j ψ(½ tr_{E/F}(x_j, x_j))` (`hermitianTracePairing_eq_sum`), so through
  `x ↦ (j ↦ x_j)`, `γ(f) = γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}` (`weilIndex_comp_addEquiv`,
  `weilIndex_pi`: GKT Proposition 3.13 (a), (d)).

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025):
Corollary 11.4, pp. 315–316; (11.3), p. 318; Proposition 12.27, p. 372; Proposition 12.29, p. 375.

## Declarations

- `Langlands.Theta.hermitianTraceForm`, `hermitianTraceForm_apply`, `hermitianTracePairing_eq_sum`,
  `hermitianTraceForm_symm`, `hermitianTraceForm_nondegenerate`,
  `isCharacterOfSecondDegree_hermitianTraceForm`, `hermitianTracePairing_symm`,
  `isSelfDualBicharacter_hermitianTracePairing`.
- `lerayScalar_eq`, `lerayScalar_selfDualMeasure`, `lerayWeil_weylElement_apply_selfDualMeasure`,
  `isLerayWeil_weilIndex`.

Internal (`Langlands.Theta.Unitary.Internal`): `addChar_sum`, `mul_gaussIntegral_eq`.

## Dependencies

`Langlands.Theta.DualPair.Unitary.LeraySplitting`, `Langlands.Theta.WeilIndex.Defs`.
