# Transporting universal families along open immersions of the base

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`). It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemGluing`. Let `a : S' ⟶ S` and `π := pullback.snd g a`.

- `cmpψ`, `cmpχ` (with `cmpψ_fst_fst`, `cmpψ_snd`, `cmpχ_fst`, `cmpχ_snd`, `cmpψ_cmpχ`,
  `cmpχ_cmpψ` and the `IsIso` instances): for `u : T ⟶ S'` with `u ≫ a = t`, the inverse
  comparison isomorphisms between `Y ×_S T` and `(Y ×_S S') ×_{S'} T`.
- `LS.comap_cmpχ`, `LS.comap_cmpψ`: the linear systems of `g` (class `m`) over `t` and of `π`
  (class pulled back to `Y ×_S S'`) over `u` correspond.
- `mapX_cmpψ`: compatibility of the comparisons with the maps `1 × k`.
- `IsUniversalOn.transport` (`a` an open immersion): a universal family for `π` over all of `S'`
  gives a universal family for `g` over the open image of `a`.
