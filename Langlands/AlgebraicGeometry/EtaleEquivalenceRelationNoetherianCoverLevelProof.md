# A Noetherian level carrying the finite surjective cover

Authors: Worker 266 and Worker 1110.

This module proves the published statement
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianCoverLevelStatement.{u}` as
`Langlands.AlgebraicGeometry.etaleEquivalenceRelationNoetherianCoverLevel`, with the helper
`noetherianCoverLevel_of_presentation`. The latter is NL for a cover `E'` whose relation ring
has a finite-type Čech presentation: a bijective `F : B₁ ⊗[A₁] Γ(E'.U) → Γ(E'.R)` with
`F (b ⊗ d) = E'.t.appTop (φ b) * E'.s.appTop d`, where `A₁` is of finite type over `ℤ` and
`B₁` is étale and faithfully flat over `A₁`. The proofs depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

Proof of `etaleEquivalenceRelationNoetherianCoverLevel`: take the cover
`(f', g') : E' ⟶ E` with `f'` finite and surjective and `E'.HasAffineQuotient`. `Γ(E₀.U)` is
Noetherian (`IsLocallyNoetherian.component_noetherian` at the affine open `⊤`). `E.R` is affine
(`isAffine_R` of the cartesian morphism to `E₀`), `E'.U` is affine because `f'` is finite,
hence affine (`isAffine_of_isAffineHom`), and `E'.R` is affine (`isAffine_R` of `(f', g')`).
`exists_fg_pushout_of_hasAffineQuotient` (module
`EtaleEquivalenceRelationNoetherianPushout`) gives `A₁`, `B₁`, `φ` and `F` as above, and
`noetherianCoverLevel_of_presentation` concludes.

Proof of `noetherianCoverLevel_of_presentation`:
1. Coactions: `h.coaction` on `B = Γ(E.U)` and `(h'.comp h).coaction` on
   `B' = Γ(E'.U)`. `f'.appTop` is equivariant (`ringHom_comp_appTop`), finite,
   and has nil kernel, because `f'` is surjective.
2. Composing with the relation iso of `E' ⟶ E₀` turns `F` into a bijection
   `L : B₁ ⊗[A₁] B' → C₀ ⊗[B₀] B'`. `exists_bijective_level` gives a finite
   set `s ⊆ B'`.
3. `exists_finite_level` gives levels `D ⊆ B` and `D' ⊇ s` with `D → D'` finite
   and surjective on spectra, and `D` finitely generated over the Noetherian
   `B₀`.
4. `E₁` is the level relation of `D`. The cartesian morphism `E ⟶ E₁` composes
   `isCartesianHom_toScheme` with `isCartesianHom_of_equivariant` for
   `D ⊆ B`. The cover is the level relation of `D'` with the cartesian
   morphism of `D → D'`. Its affine quotient comes from
   `hasAffineQuotient_of_bijective` applied to the bijection of step 2 at `D'`.
