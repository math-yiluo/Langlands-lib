# Uniqueness of relative rigidified isomorphisms

Module `Langlands.AlgebraicGeometry.Picard.RigidifiedRelativeIsoUniqueness`, namespace
`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle`.

Fix schemes `S`, `X`, a morphism `f : X ⟶ S` and a section `ε` with `ε ≫ f = 𝟙 S`.
For `T : Over S`, the relative family is `X_T = T ×_S X` with projection
`p_T = (relativeProjection f).app T : X_T ⟶ T` and induced section
`ε_T = (relativeSection f ε section_eq).app T : T ⟶ X_T`.

The hypothesis `hO` used below is exactly the universal structure-sheaf condition of the
published `RigidifiedFppfComparisonStatement`: for every `T : Over S` and every open `U` of `T`,
the map `p_T.app U : Γ(T, U) ⟶ Γ(X_T, p_T⁻¹ U)` is an isomorphism.

- `relativeSection_appTop_injective f ε section_eq hO T`: the map `ε_T.appTop` on global
  functions is injective. Proof: `ε_T ≫ p_T = 𝟙`, so `p_T.appTop ≫ ε_T.appTop = 𝟙`; since
  `p_T.appTop` is an isomorphism (`hO T ⊤`), every global function on `X_T` is of the form
  `p_T.appTop a`, and `ε_T.appTop` sends it back to `a`.
- `relative_iso_subsingleton f ε section_eq hO T L M`: for rigidified line bundles `L`, `M` in
  `relative f ε section_eq T` (line bundles on `X_T` rigidified along `ε_T`), the type `L ≅ M`
  of rigidified isomorphisms is a subsingleton. Proof: for `e₁ e₂ : L ≅ M`, the endomorphism
  `e₁.hom ≫ e₂.inv` of `L` is the identity by the published `endo_eq_id` (endomorphisms of a
  rigidified line bundle are the identity when the rigidifying morphism is injective on global
  functions), so `e₁.hom = e₂.hom`.

These are internal helper results for the proof of `RigidifiedFppfComparisonStatement`; they
are the uniqueness input (the `unique` hypothesis) of the general-`f` Zariski separation and
gluing results for rigidified classes.
