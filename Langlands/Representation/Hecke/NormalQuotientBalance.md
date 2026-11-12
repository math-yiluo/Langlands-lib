# Balancing identities for the Hecke bimodule of a quotient map

Supporting lemmas for Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, III.2.10 and (III.2.10.1),
printed pp.80–81 / PDF pp.86–87, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

All groups are locally compact Hausdorff nonarchimedean groups with arbitrary
left Haar measures; no unimodularity is assumed. The Hecke algebras, integrated
actions `heckeAction`, the left and right `H(H)`-actions `leftModule` and
`rightModule` on `H(G)`, and `rightRepresentation` are the published ones of
III.2.1. Statements in the `General` and `Comparison` sections hold for an
arbitrary continuous homomorphism `φ : H →* G`; the `Quotient` section
specializes to the projection `q : P → M = P ⧸ N` of a closed normal subgroup.

## General

- `integral_normalizedIndicator`: the normalized compact-open indicator `e_K`
  has total Haar mass one.
- `heckeAction_normalizedIndicator_translate`: `e_K · (ρ(k) v) = e_K · v` for
  `k ∈ K`. The proof pairs with an arbitrary linear functional, uses right
  invariance of `e_K` and `integral_mul_right_test`; the modular factor of `k`
  is one because `k` lies in a compact open subgroup.

## Comparison (arbitrary continuous `φ`)

- `heckeAction_comp_normalizedIndicator`: if `φ` maps `K` onto `KG`, then
  `e_K` acting through `ρ ∘ φ` equals `e_{KG}` acting through `ρ`. Both sides
  are compared with `e_{KG} · (e_K · v)`: the image of `e_K` is `KG`-fixed, and
  `e_{KG}` absorbs `ρ(φ(k))` for `k ∈ K` by the previous lemma and total mass one.
- `heckeAction_leftTests_eq_mul`: the integrated left regular action is
  convolution.
- `rightRepresentation_mul`: `r(h⁻¹)S * b = S * l(φ h)b`, a change of variables
  in the convolution integral with the modular factor of `rightRepresentation`.
- `heckeAction_rightModule`: for every smooth `ρ` of `G`,
  `(T·a)·v = T·(a·v)`, where `T·a` is the published right action and
  `a·v` is the integrated action of `ρ ∘ φ`. This is the identity
  `T * a = T * φ_*(a)` of the source in integrated form. Its proof pairs with a
  linear functional, expands `rightModule` by `rightModule_integral`, swaps the
  two compactly supported integrals (`integral_integral_swap_of_hasCompactSupport`)
  and evaluates the inner integral with `integral_mul_right_test`.

## Quotient

- `continuous_quotientMk'`: continuity of `QuotientGroup.mk' N`, stated with
  the coercion of the bundled homomorphism so that rewriting is type-correct.
- `heckeAction_quotient_normalizedIndicator`: `e_K` acting through `q` equals
  `e_{q(K)}` (`quotientOpenSubgroup N K`) acting on `M`.
- `leftModule_normalizedIndicator` and `rightModule_normalizedIndicator`:
  `e_K · f = e_{q(K)} * f` and `T · e_K = T * e_{q(K)}`, the special case
  `T·e_K = T * e_{K_M}` stated after (III.2.10.1). The right version is the
  left one conjugated by Haar inversion, which fixes normalized indicators.
- `rightModule_doubleCoset` is (III.2.10.1):
  `T · (e_K * l(p) e_K) = T * (e_{q(K)} * l(q p) e_{q(K)})`, where
  `e_K * l(p) e_K` is the density of `e_K * δ_p * e_K`. The proof splits the
  right action of the product, applies `rightModule_normalizedIndicator`, moves
  the left translation through `rightModule_leftTranslate`, and finishes with
  `rightRepresentation_mul` and associativity. The implemented route is this
  direct calculation, not the source's uniqueness argument for `φ_*(a_{t,K})`.
