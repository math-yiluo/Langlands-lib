# Root-group and torus homomorphisms into the split Cayley automorphism group scheme

Notation as in `Points.md`: `Aut` is the automorphism group scheme of Zorn's split Cayley algebra
over a field `K`.

- `map_rootFun`, `rootMatrix_map`, `rootGL_map`, `torusGL_map`: the explicit root-group and torus
  matrices from `RootGroups.lean` commute with changing coefficients along a ring homomorphism.
  `torusGL_one` states that `torusGL 1 1 = 1`.
- `rootHom α φ`: the group homomorphism `t ↦ x_α(t)` from the additive group of `A` into the
  automorphism matrices over `A`. `rootTrans K α` is the same map as a natural transformation of
  group functors on `K`-algebras.
- `rootMap K α : 𝔾ₐ ⟶ Aut`: the root-group homomorphism of group schemes, with source the
  published one-dimensional vector group `VectorGroup.groupScheme K 1`.
  `pointsEquiv_rootMap` and `affinePointsEquiv_rootMap` compute it on points.
  `affinePointsEquiv_rootMap_inclusion` states that its composite with the inclusion into `GL₈`
  sends the affine point `t` to `rootGL α (t 0)`.
- `torusHom φ`: the group homomorphism `(s, t) ↦ diag(1, s, t, s⁻¹t⁻¹, s⁻¹, t⁻¹, st, 1)` from
  pairs of units of `A` into the automorphism matrices over `A`. `torusPoints` and
  `torusPoints_naturality` give the same map on scheme points of the rank-two split torus.
- `torusMap K`: the homomorphism from the published rank-two split torus
  `splitTorus.commGroupScheme (Spec K) (ULift (Fin 2))` to `Aut`, built from points.
  `pointsEquiv_torusMap` computes it on points. `mono_torusMap` states that it is a
  monomorphism, since the entries in positions `1` and `2` recover `s` and `t`.
  `affinePointsEquiv_torusMap` states that its composite with the inclusion into `GL₈` sends an
  affine point to `torusGL` of its two torus coordinates.

These maps are internal to this development. They are the standard torus and root subgroups of
split `G₂` in Zorn's coordinates.
