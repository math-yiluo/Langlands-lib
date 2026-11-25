# Points of `SL₂` over a base scheme

Internal supporting development for the proof of
`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement` (Conrad, *Reductive group
schemes*, Proposition 4.3.1).

- `sl2 S` is the group scheme `SL₂` over `S` exactly as written in the target statement: the base
  change along `Gm.toSpecZ S` of `SpecialLinear.groupScheme (Fin 2) (CommRingCat.of (ULift ℤ))`.
  It is a reducible abbreviation, so it is definitionally the statement's `SL₂`.
- `slEquiv T : (T ⟶ (sl2 S).X) ≃* Mat.SL2 Γ(T.left, ⊤)` identifies the points of `SL₂` over a
  test scheme `T` with determinant-one `2 × 2` matrices over the global sections of `T`, as
  groups. It composes the published `GroupScheme.baseChangePointsEquiv` with
  `SpecialLinear.pointsEquiv`.
- `slEquiv_naturality`: for `g : V ⟶ T`, the matrix of the restricted point `g ≫ x` is the
  entrywise image of the matrix of `x` under the global-sections map `ring g`.
