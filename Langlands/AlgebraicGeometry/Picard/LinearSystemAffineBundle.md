# The line bundle `N` on the Grassmannian with `O(W) ≅ L ⊗ N`

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`). It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`.

- `classOf_pbLB`, `dcl_zeroIdeal` (`[O(Z(σ))] = [L]` for a regular section).
- `pullback_ptMap_class_eq_zero`: the class `[O(W)] - [L]` is trivial along every chart point.
- `exists_lineBundle_universal`: there is a line bundle `N` on `D.Gr` with
  `[O(W)] = [L] + [N]` on `X ×_R D.Gr`. The class `[O(W)] - [L]` is trivial over the preimages of
  the admissible affine opens, and the projection to `D.Gr` is proper, flat and geometrically
  integral, so `PushforwardLineBundle.exists_classOf_pullback` applies.

## Source

Kleiman, *The Picard scheme*, Exercise 3.14 (p.26): `O(W) = L_{P(Q)} ⊗ f^*O(1)`; here `N` plays the
role of `O(1)`.
