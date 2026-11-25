# The composition rule, block compatibility and the "Weyl group"

**GKT §2.2.2** (the scalar `c` of `M_A(g₁) M_A(g₂) = c M_A(g₁ g₂)`, `|c| = 1`, p. 52), **§2.3.1**
((2.11), p. 53), **§2.3.3** ((2.21), Proposition 2.24, (2.22), (2.23), (2.24), Lemma 2.25,
Proposition 2.26, pp. 61–66) and **§2.3.4** (Proposition 2.28, Corollary 2.29, pp. 66–68).

The module `Langlands.Theta.Metaplectic.Block` proves the general composition rule for the
standard Weil operator `r(g)` of `Langlands.Theta.Metaplectic.StandardOperator`, its block
compatibility for an orthogonal sum of two polarized spaces, and the splitting of the group generated
by the (partial) Weyl elements.

## Content

`F` is a nonarchimedean local field with `2 ≠ 0`, `ψ` a continuous non-trivial character, and the
pairings are perfect pairings of finite-dimensional spaces with their module topologies.

**The composition rule.** `exists_standardOperator_comp`: `r(g₁) r(g₂) = c r(g₁ g₂)` with
`|c| = 1`. Both pairs `(g₁, r(g₁)) (g₂, r(g₂))` and `(g₁ g₂, r(g₁ g₂))` lie in the metaplectic group
of pairs over `g₁ g₂`, so they differ by a scalar (Schur's lemma, through
`MetaplecticGroup.exists_scalar_mul_eq`), and `|c| = 1` since both are unitary. The scalar is the
Leray cocycle `c_X^ψ(g₁, g₂)` of Definition 2.7, which this module does not name. With `p` in the Siegel parabolic the scalar is `1` (Proposition 2.17, in
`Langlands.Theta.Metaplectic.SiegelParabolic`).

**Blocks.** For pairings `β₁ : X₁ × Y₁ → F` and `β₂ : X₂ × Y₂ → F`:

- `sumPairing β₁ β₂ ((x₁, x₂), (y₁, y₂)) = β₁(x₁, y₁) + β₂(x₂, y₂)`, whose polarized space is
  `W₁ ⊕ W₂`, and the tensor `schwartzBruhatTensor φ₁ φ₂ = φ₁ ⊗ φ₂` with
  `schwartzBruhatInner_tensor` are in `Langlands.Theta.Heisenberg.PartialFourier`.
- `blockDiag β₁ β₂ : Sp(W₁) × Sp(W₂) →* Sp(W₁ ⊕ W₂)`, the book's `diag(g₁, g₂)` (p. 67);
  `isometryInv_blockDiag`, `standardC_blockDiag`, and **`ker c(diag(g₁, g₂)) = ker c(g₁) × ker
  c(g₂)`** (`standardKernel_blockDiag`); `blockQuotientEquiv` the induced isomorphism of the
  quotients.
- `standardIntegrand_blockDiag` (the integrand of `diag(g₁, g₂)` at `φ₁ ⊗ φ₂` is the product of the
  integrands) and `standardOperatorFun_blockDiag` (Fubini over the product of the quotients).
- `standardOperator_blockDiag`: **Proposition 2.28**, `r(diag(g₁, g₂)) (φ₁ ⊗ φ₂) =
  r₁(g₁) φ₁ ⊗ r₂(g₂) φ₂`. The product `d_{g₁} × d_{g₂}` carried to `(Y₁ × Y₂) / ker c` is a positive
  multiple of `d_{diag(g₁, g₂)}` (`exists_standardOperator_blockDiag`), and the multiple is `1`
  because both sides are unitary on a tensor of non-zero norm. **This departs from the book's
  proof**, which uses the Bruhat decomposition and the splittings of `P(X)` and of `W`; the direct
  computation does not need the Bruhat decomposition.
- `standardOperator_blockDiag_comp`: **Corollary 2.29**, stated with the scalars of the composition
  rule: `r₁(g₁) r₁(g₁') = c₁ r₁(g₁ g₁')` and `r₂(g₂) r₂(g₂') = c₂ r₂(g₂ g₂')` give
  `r(diag(g₁, g₂)) r(diag(g₁', g₂')) = c₁ c₂ r(diag(g₁ g₁', g₂ g₂'))`.

**The Weyl elements.** For `J : Y ≃ X` with `β(J y, y')` symmetric, `w_J` is the Weyl element of
`Langlands.Theta.Metaplectic.WeylElement` (`r(w_J)` = the Fourier transform for the self-dual
measure, (2.24)).

- `isometryInv_weylIsometry_mul_self`, `weylIsometry_mul_self_mem`: `w_J² = -1` lies in the Siegel
  parabolic (the book's `w_S² = a_S`); `standardOperator_weylIsometry_mul_self_apply`:
  `r(w_J²) φ(x) = φ(-x)` (Lemma 2.16, `|det(-1)| = 1`).
- `standardOperator_weylIsometry_weylIsometry_apply` and `standardOperator_weylIsometry_mul_self`:
  **Lemma 2.25**, `r(w_J)² φ(x) = φ(-x)` (Fourier inversion for the self-dual measure), so
  `r(w_J)² = r(w_J²)`.
- `standardOperator_weylIsometry_pow_comp`: **Proposition 2.26** for the powers of `w_J`,
  `r(w_J^i) r(w_J^j) = r(w_J^{i + j})` (Lemma 2.25 and Proposition 2.17 for `w_J² ∈ P`).
- `partialWeylElement β₂ J hJ = diag(w_J, 1)`: the book's partial Weyl element `w_S` ((2.21)) for
  `W = W_S ⊕ W_{S^c}`, `W_S = X₁ × Y₁`, `J` the book's `I_S`.
- `standardOperator_partialWeylElement`: **(2.23)** (Proposition 2.24), `r(w_S)(φ₁ ⊗ φ₂) =
  ℱ φ₁ ⊗ φ₂` with `ℱ φ₁(x) = ∫ ψ(-β₁(x, J⁻¹ u)) φ₁(u) du` for the self-dual measure.
- `standardOperator_partialWeylElement_mul_self`, `standardOperator_partialWeylElement_mul_self_apply`:
  **Lemma 2.25** for `w_S`: `r(w_S)² = r(w_S²)`, and `r(w_S²)(φ₁ ⊗ φ₂)(x₁, x₂) = φ₁(-x₁) φ₂(x₂)`.
- `standardOperator_blockDiag_weyl_comp`: **Proposition 2.26** for the group of the
  `diag(w_{J₁}^i, w_{J₂}^j)`; for one-dimensional blocks it is the book's group `W` of a standard
  basis of rank 2.

The book's `W` for a standard basis of rank `n` is the group of the iterated block elements
`diag(w_{J₁}^{i₁}, …, w_{J_n}^{i_n})`; Proposition 2.26 for it follows from
`standardOperator_blockDiag_comp` and `standardOperator_weylIsometry_pow_comp` by induction on the
number of blocks. This induction (with spaces indexed by `Fin n`) and Proposition 2.28 for `k`
blocks as a single statement are not formalized; the two-block statements are.

The book's Proposition 2.24 has the kernel `ψ̄(⟨z_S, I_S(y_S)⟩)`; in the Library's conventions
it is `ψ(-β₁(x, J⁻¹ u))` with `I_S = J⁻¹`, as for the full Weyl element in
`Langlands.Theta.Metaplectic.WeylElement`.

## Declarations

- `exists_standardOperator_comp`.
- `blockDiagEquiv`, `blockDiagEquiv_apply`, `blockDiag`, `blockDiag_apply`,
  `isometryInv_blockDiag`, `standardC_blockDiag`, `standardKernel_blockDiag`, `blockQuotientEquiv`,
  `blockQuotientEquiv_mk`, `standardIntegrand_blockDiag`.
- `standardOperatorFun_blockDiag`, `exists_standardOperator_blockDiag`,
  `standardOperator_blockDiag`, `standardOperator_blockDiag_comp`.
- `isometryInv_weylIsometry_mul_self`, `weylIsometry_mul_self_mem`,
  `standardOperator_weylIsometry_mul_self_apply`,
  `standardOperator_weylIsometry_weylIsometry_apply`, `standardOperator_weylIsometry_mul_self`,
  `standardOperator_weylIsometry_pow_comp`.
- `partialWeylElement`, `standardOperator_partialWeylElement`,
  `standardOperator_partialWeylElement_mul_self`,
  `standardOperator_partialWeylElement_mul_self_apply`, `standardOperator_blockDiag_weyl_comp`.

All in the name space `Langlands.Theta`.

## Dependencies

`Langlands.Theta.Metaplectic.SiegelParabolic`, `Langlands.Theta.Metaplectic.WeylElement`,
`Langlands.Theta.Heisenberg.PartialFourier`.
