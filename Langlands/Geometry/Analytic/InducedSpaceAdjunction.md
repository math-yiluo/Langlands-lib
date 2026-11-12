# Induction of analytic spaces as a left adjoint of restriction

Author: Worker 21.

The module `InducedAnalyticSpace` constructs Berkovich's induced space
`X_{G/H}` of an analytic space `X` with an action of a subgroup `H ≤ G`. It
proves the universal property as a bijection `InducedSpace.homEquiv`. This
module turns induction into a functor and the universal property into an
adjunction. Induction is left adjoint to restriction of actions along
`H → G`. This makes `U ↦ U_{G/H}` functorial. Berkovich's Example 1.2.1(i)
compares the sites of `X(H)` and `X_{G/H}(G)`, and the natural comparison
functor sends `U(H)` to `U_{G/H}(G)`. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace`. The universes
are those of `InducedAnalyticSpace`. All statements are proved.

## Declarations

- `homEquiv_naturality`: the bijection `homEquiv H` is natural in the target.
  For a `G`-morphism `g : Y ⟶ Y'`,
  `homEquiv H (ψ ≫ g) = homEquiv H ψ ≫ (Action.res _ H.subtype).map g`.
  It follows from `homEquiv H ψ = unit H X ≫ res.map ψ`.
- `inductionFunctor H : Action LocalizedCategory H ⥤ Action LocalizedCategory G`
  is Mathlib's `Adjunction.leftAdjointOfEquiv` applied to `homEquiv`.
  On objects it is `inducedAction H X` (`inductionFunctor_obj`). On a morphism
  `f : X ⟶ X'` it is `lift H (f ≫ unit H X')` (`inductionFunctor_map`).
- `inductionAdjunction H : inductionFunctor H ⊣ Action.res _ H.subtype`
  (Mathlib's `Adjunction.adjunctionOfEquivLeft`). Its bijection of
  morphisms is `homEquiv H` (`inductionAdjunction_homEquiv`).
- `copy_liftHom_unitHom` and `copy_inductionFunctor_map`: on the copy
  indexed by `c`, the induced morphism is `f` followed by the inclusion of
  the copy `c` of `X'`. The proof uses `κ(c.out, H) = baseRep H`
  (`correction_out_baseCoset`), so the corrections in the unit and in the
  action cancel.

## Original source and provenance

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.1.2, printed p.2: "any H-morphism ϕ : X → Y to a G-space Y extends in a
unique way to a G-morphism ϕ′ : X′ → Y". The adjunction is the categorical
form of this universal property. The functor and adjunction are derived from
`homEquiv` by Mathlib's general constructions. The copy formula for induced
morphisms is computed here.
