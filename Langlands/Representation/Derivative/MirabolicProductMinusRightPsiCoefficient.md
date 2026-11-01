# The coefficient of the positive-rank right `Ψ⁻` compatibility of BZ77 4.13(c)

Author: Worker 837.

This helper module belongs to the proof of the clause
`Langlands.Derivative.MirabolicProductMinus.RightPsiCompatibility.{uF,uV} F T`
of the published statement module
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`.
At positive ranks the published two-stage comparison
`Induction.splitStagesCompactEquiv` produces compact induction from
`K = P.comap levi` of a coefficient on coinvariants. This module identifies
that coefficient with `Ψ⁻τ ⊗ ρ` and computes its action and naturality. The
groups `Q`, `P`, `K`, `N`, the blocks `A`, `D` and the Haar ratio come from
`MirabolicProductMinusRightPsiGroups`. The final clause is assembled in
`Langlands.Representation.Derivative.MirabolicProductMinusRightPsi`.

## Provenance

All declarations are derived internal content for that proof. The normalizing
characters are the published ones:

- `T.rightCharacter m r`, the case (III) inducing character of
  `rightMixedProductFunctor` (BZ77 §4.12, printed pp.456–458, source
  `bernstein-zelevinsky-1977-induced-i`). At `(p, a)` it is
  `ν_r(projection p)^(m/2) ν_m(a)^(-(r+1)/2)`.
- `Mirabolic.psiMinusCharacter T n = |det|^(-1/2)`, the published `Ψ⁻`
  normalization.
- `T.parabolicHalfModulus`, the half modulus of the normalized binary product.

The module checks that these scalars combine exactly. No character is dropped
or assumed.

## Coinvariants of the inducing coefficient under `N`

Fix `τ` on `P_(r+1) = mirabolic r` with carrier `W` and `ρ` on `GL_m` with
carrier `V`.

- `rightPsiInducingCoefficient T τ ρ` is `twist χ_R (rightInducingRepresentation τ ρ)`
  on `H = rightSubgroup m r`, the coefficient of the published right mixed
  product.
- `rightCharacter_of_mem_rightPsiKernel`: `χ_R` is trivial on `N`, because the
  `GL_m` block is `1` and the projected mirabolic block is `1`.
- `rightPsiInducingCoefficient_kernel`: an element of `N` with mirabolic block
  `u ∈ V_(r+1)` acts on `w ⊗ v` by `τ(u) w ⊗ v`.
- `rightPsiTensorEquiv T τ ρ` is a linear equivalence from the
  `N`-coinvariants of this coefficient onto
  `Jacquet.Localization.Coinvariants τ (radical r) 1 ⊗ V`. That first factor is
  the carrier of `Ψ⁻τ`. The forward map `rightPsiTensorForward` descends
  `mk ⊗ id`. The inverse is the lift of the bilinear map
  `rightPsiTensorBilinear`, `([w], v) ↦ [w ⊗ v]`. This lift is well defined
  because every `u ∈ V_(r+1)` is the block of `rightPsiKernelEquiv.symm u ∈ N`.
  `rightPsiTensorEquiv_mk_tmul` gives its value on classes of pure tensors.

## The binary half modulus and the scalar identity

- `leviModulus_binary`: the published block modulus of shape `(a, b)` at
  `(x₀, x₁)` is `ν(x₀)^b / ν(x₁)^a`.
- `sqrt_div_pow_complex` and `parabolicHalfModulus_binary`: on the binary
  parabolic, `δ^(1/2)(q) = ν(q₀)^(b/2) ν(q₁)^(-a/2)`.
- `rightPsi_scalar_identity` (real form) and `rightPsi_scalar_identity_complex`
  state, for `a, d > 0`,

  ```text
  (a d)^(-1/2) · d · a^(m/2) d^(-(r+1)/2) = a^(m/2) d^(-r/2) · a^(-1/2).
  ```

## The coefficient identification

- `coinvariants_tensor_ext` and `coinvariants_tensor_ext_smul`: linear maps,
  and operator identities `e ∘ f = c • (g ∘ e)`, on coinvariants of a tensor
  product are determined by classes of pure tensors.
- `twist_twist_splitKernelCoefficientAction_mk` evaluates the doubly twisted
  published `splitKernelCoefficientAction` on a class.
- `rightPsiStagesCoefficient` is the coefficient restricted to
  `HP = H.subgroupOf P` along the published `subgroupOfEquivOfLe`.
- `rightPsiCoefficientEquiv T hr hm τ ρ` is a linear equivalence from the
  coinvariants of that restriction under `I = HP ∩ ker(rP)` onto
  `Ψ⁻τ ⊗ V`. It is the published `splitStagesCoefficientEquiv`, which
  identifies them with the `N`-coinvariants, followed by `rightPsiTensorEquiv`.
  `rightPsiCoefficientEquiv_mk_tmul` sends `[w ⊗ v]` to `[w] ⊗ v`.
- `rightPsiStagesCoefficient_section` and `rightPsiCoefficientEquiv_section`:
  the section `diag(l, 1)` of `l = [[A, X], [0, D]] ∈ K` acts on `[w ⊗ v]` by
  `χ_R(diag(l, 1)) · [τ(diag(A, 1)) w] ⊗ ρ(D) v`. This uses
  `rightProjection_levi`.
- `rightPsiCoefficientEquiv_psiMinus`: `Ψ⁻τ(A) ⊗ ρ(D)` sends `[w] ⊗ v` to
  `|det A|^(-1/2) · [τ(diag(A, 1)) w] ⊗ ρ(D) v` (published `psiMinus_action`).
- `rightPsi_scalar_eq` states, at `l ∈ K`,

  ```text
  |det l|^(-1/2) · χ_Haar(l) · χ_R(diag(l, 1)) = δ^(1/2)(l) · |det A|^(-1/2).
  ```

  Here `χ_Haar = |det D|` by `rightPsiHaarRatio_apply`,
  `|det l| = |det A| |det D|` by `determinantNorm_rightPsi`, and
  `δ^(1/2)` is the half modulus of shape `(r, m)` at `rightPsiCast l`. The
  proof substitutes these values into `rightPsi_scalar_identity_complex`.

## Action and naturality

- `rightPsiCoefficientEquiv_action` (with `rightPsiCoefficientEquiv_action_tmul`
  and the generic chaining lemmas `linearEquiv_map_smul_of_eq` and
  `linearEquiv_smul_chain`) is the action law. On the coefficient of the
  comparison, twisted by `|det|^(-1/2)` and by the Haar ratio character, an
  element `l = [[A, X], [0, D]] ∈ K` acts on `Ψ⁻τ ⊗ ρ` by

  ```text
  δ^(1/2)(l) · (Ψ⁻τ)(A) ⊗ ρ(D).
  ```

  This is the coefficient of the normalized binary product
  `Ψ⁻τ × ρ`, transported along `rightPsiCast`.
- `rightPsiCoefficientEquiv_natural` (with `_natural_tmul`) is naturality. Take
  morphisms `f₁ : τ → τ'` and `f₂ : ρ → ρ'` and a coefficient intertwiner `t`
  acting by `f₁ ⊗ f₂` on pure tensors. The published `splitKernelInducingMap`
  and `restrictAlongMap` turn `t` into a map on `I`-coinvariants. Under
  `rightPsiCoefficientEquiv` that map becomes `Ψ⁻(f₁) ⊗ f₂`. This uses the
  published `psiMinus_map_quotient`.

Two theorems use `set_option maxHeartbeats 400000`, a finite bound.

## Imports

The only direct import is the helper
`Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups`.
The complete import closure of the clause and its restriction audit are
recorded in
`Langlands/Representation/Derivative/MirabolicProductMinusRightPsi.md`.
