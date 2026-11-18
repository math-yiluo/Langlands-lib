# Geometric reducedness of affine schemes from their global sections

Worker 6.

- `geometricallyReduced_of_isAffine`: let `Y` be affine with `f : Y ⟶ Spec R'`. If
  `F ⊗[R'] Γ(Y, ⊤)` is reduced for every field `F : Type u` under `R'` (with the algebra
  structure induced by `f`), then `f` is geometrically reduced in Mathlib's sense. Every
  `Spec F → Spec R'` is `Spec` of a ring map, `Y ≅ Spec Γ(Y, ⊤)` turns `f` into `Spec` of an algebra
  map, and `pullbackSpecIso` identifies the fibre product with `Spec (Γ(Y, ⊤) ⊗[R'] F)`.
