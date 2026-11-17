# The diagonal factor projection of `G` on algebras over the descended coefficient algebra

Namespace `Langlands.GroupScheme.WeilChart`. This internal construction is the fifth step of the
proof of `AffineWeilPairSingleChartDescentStatement`. Let `T` be an `A`-algebra with an algebra
map `φ : B → T`. The module defines the projection of `G(T)` onto the factor of `G` cut out by
the diagonal of `B`. When `T` admits a chart map `A' → T`, the projection is the chart factor
projection of the diagonal idempotent (module `Langlands.GroupScheme.Reductive.WeilChartDiagonal`).
In general it is descended from `T ⊗[A] A'` by faithfully flat descent of points (module
`Langlands.GroupScheme.AffinePointFaithfullyFlatDescent`).

## Setting

As in `WeilChartDiagonal`: `e : A' ⊗[A] B ≃ₐ[A'] C`, a chart
`P : G_{A'} ≅ AffineWeil.groupScheme A' C H`, factor rigidity `hR`, and `H` reductive with
almost simple geometric fibres. The second part assumes in addition that `A'` is faithfully flat
over `A`. It also assumes the invariance `hinv` of the elements `1 ⊗ e (1 ⊗ b)` under all
canonical isomorphisms `chartAlgEquiv f₁ f₂`, which is the output of `exists_chartDescent`.

## Through a chart

- `chartFactor_congr`: chart factor projections of equal idempotents are equal.
- `diagProj e P φ f : G(T) →* G(T)` is the chart factor projection
  `chartFactor P f (diagIdem e φ f)`, evaluated on the points of `G` over `T` itself.
- `diagProj_chart`: under `hinv` it does not depend on the chart map (`chartFactor_diagIdem`).
- `diagProj_idem`: it is idempotent.
- `diagProj_map`: it is natural. For `χ : T ⟶ T₁`, the image under `χ` of `diagProj e P φ f x`
  is `diagProj e P (χ ∘ φ) (χ ∘ f)` of the image of `x`. The proof uses the naturality of the
  chart factor projection, `grestrict_chartFactor` and `diagIdem_map`.

## Descent to all algebras

- `extT A' T = T ⊗[A] A'` with the inclusion `extι A' T : T ⟶ T ⊗[A] A'`, the chart map
  `extChart T : A' → T ⊗[A] A'` and the functoriality `extMap χ`, with `extι_comp_extMap` and
  `extMap_comp_extChart`. `extι_faithfullyFlat`: `T → T ⊗[A] A'` is faithfully flat when `A'` is
  faithfully flat over `A` (Mathlib's base change instance).
- `exists_descProj`: for `x ∈ G(T)`, the element `diagProj` of the image of `x` in
  `G(T ⊗[A] A')` (through `extChart T` and `B → T → T ⊗[A] A'`) comes from `G(T)`. Two maps
  `a, b : T ⊗[A] A' ⟶ Z` that agree on `T` give the same image. By `diagProj_map` the images
  are `diagProj` through the chart maps `a ∘ extChart` and `b ∘ extChart` of the same point. The
  two projections agree by `diagProj_chart`. Effective descent
  (`AffinePointDescent.exists_affinePointMap_eq`) applies.
- `descProj e P hR hred hsimple hinv φ : G(T) →* G(T)` is the descended map. It is a group
  homomorphism because the image map in `G(T ⊗[A] A')` is injective
  (`AffinePointDescent.affinePointMap_injective`). `descProj_spec` records its defining
  property.
- `descProj_eq_diagProj` (**chart formula**): when `T` has a chart map `g : A' → T`,
  `descProj φ = diagProj φ g`.
- `descProj_idem`: `descProj` is idempotent.
- `descProj_map`: `descProj` is natural. For `χ : T ⟶ T₁`, the image under `χ` of `descProj φ x`
  is `descProj (χ ∘ φ)` of the image of `x`.

## Provenance

This is internal. In Conrad, *Reductive group schemes* (2014), proof of Proposition 6.4.4, the
descended group `G'` over `B` is the factor of `G_B` cut out by the diagonal of `B`. Over the
étale cover it is described by the given Weil restriction presentation. The construction here
defines the projection onto that factor through charts, proves that it does not depend on the
chart, and descends it along the faithfully flat cover.
