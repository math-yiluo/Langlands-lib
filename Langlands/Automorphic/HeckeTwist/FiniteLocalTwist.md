# Images of finite and local automorphic realizations under any Hecke multiplier

Author: Worker 5136.

This internal module twists the Library's finite realizations
(`FiniteRealization F n`, subspaces of automorphic forms invariant under right
translation by `GL_n(𝔸_F^∞)`) and local realizations (`LocalRealization F n v`,
subspaces invariant under `GL_n(F_v)` for a finite place `v`) by `χ ∘ det`, for
an arbitrary Hecke character `χ`. Write `M_χ` for
`AutomorphicForms.heckeDeterminantMultiplier n χ` (module
`Langlands.Automorphic.HeckeTwist.AutomorphicMultiplier`).

- Private helpers: `scalarImage` is the image of an invariant subspace under a
  linear automorphism `e` with `ρ g (e f) = η(g) • e (ρ g f)`.
  `scalarImageRepresentationEquiv` identifies the action on the image with the
  scalar twist by `η`, and `scalarImage_eq_bot_iff` says the image is zero only
  for the zero subspace.
- `AutomorphicForms.localRightAction_heckeDeterminantMultiplier`: right
  translation by `g ∈ GL_n(F_v)` of `M_χ f` is
  `χ_v(det g) • M_χ (g · f)`, where `χ_v ∘ det` is the Library's
  `χ.finiteLocalDeterminant n v`. It is the finite case through the local
  inclusion.
- `FiniteRealization.heckeDeterminantTwist S χ`: the image of `S` under `M_χ`,
  invariant under `GL_n(𝔸_F^∞)`.
- `FiniteRealization.heckeDeterminantTwistEquiv`, `_val`, `_representation`:
  multiplication from `S` onto its twist, and its covariance with the scalar
  `χ(det (ofFinite g))`.
- `FiniteRealization.heckeDeterminantTwistRepresentationEquiv`: the twist of the
  representation of `S` by `g ↦ χ(det (ofFinite g))` is equivalent to the
  representation on the twisted realization.
- `toContinuous_`, `evaluate_`, `evaluate_…_symm`: values are multiplied by
  `χ(det g)` and `χ(det g)⁻¹`. `heckeDeterminantTwist_eq_bot_iff`,
  `_ne_bot_iff` and `_mono`: the twist is zero exactly when `S` is, and is
  monotone.
- The same declarations under `LocalRealization`, for the action of `GL_n(F_v)`
  and the scalar `χ_v(det g)`.
- `FiniteRealization.toLocal_heckeDeterminantTwist`: restriction to a local
  realization commutes with the twist.

Provenance: internal. This is the Library module
`Langlands.Automorphic.FiniteLocalDeterminantTwist` with the finite-order
hypothesis removed. No correspondence with a particular passage of the
literature is claimed.
