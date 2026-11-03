# Local representations as global charts

This is an internal categorical construction from the full-slice lifted Yoneda
presheaf and the existing extension product. No geometric representability
result or sheaf property is assumed or proved here.

Let `B` and `U` be arbitrary schemes in universe `u`, let `j : U ⟶ B`,
and let `F : Presheaf B`. Suppose `H : Over U` represents the restriction
`(Over.map j).op ⋙ F` by a natural isomorphism `e` on the entire slice over `U`.
The presheaves have values in `Type (u + 1)`; the scheme Yoneda presheaf
retains its explicit `ULift`.

`LocalRepresentation.chart j H e` is the map from the Yoneda presheaf of
`H` viewed over `B` to `F` corresponding to the section
`e.hom.app (op H) ⟨𝟙 H⟩`. Its value on a map over `U` agrees with `e.hom`,
as shown by `chart_app_map` using naturality.

`chartToProduct` pairs this chart map with the represented map `H ⟶ U`.
`chartProductIso` proves it is a natural isomorphism

```text
Y_B(H viewed over B) ≅ F × Y_B(U).
```

The component proof works on every object `Z ⟶ B`. For surjectivity, a pair
consists of a section of `F` over `Z` and a map `Z ⟶ U` over `B`. View `Z`
over `U`, transport the section along the identity-underlying isomorphism
back to `Z`, and apply `e.inv` to obtain the map to `H`. Naturality and the
inverse identities recover both coordinates. For injectivity, equality of
the second coordinate makes both maps morphisms over the same `U`-scheme;
naturality transports equality of the first coordinate to equality under
`e.hom`, whose component is injective.

`chartProductIso_hom_fst` identifies the first projection with the original
chart. If `j` is an open immersion, `chart_isOpenImmersion` follows from
`extProd.relative_fst` and invariance under isomorphism. Thus the global
chart is a representable open immersion in the Library's presheaf sense.
This requires no sheaf hypothesis. Covering, gluing, and the existence of
local geometric models are separate obligations.
