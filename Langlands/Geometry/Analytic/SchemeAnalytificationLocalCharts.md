# Local affinoid charts of the glued analytification of a scheme

A local chart `G : LocalChart K f` of the glued analytification `Space K f` is
an affine open `G.affineOpen = U` of `X` together with a local affinoid domain
`G.domain = L` of the polynomial-locus atlas `atlas K (chartPresentation K f U)`
of `U^an`. The unit attaches to `G`:

* `G.algebra`, the presented affinoid algebra of `L`;
* `G.coord : Γ(U, ⊤) →ₐ[K] G.algebra`, the coordinate-algebra map
  `localAlgebraMap`;
* `G.point = schemePoint U G.coord : Spec G.algebra ⟶ X`;
* `G.chart : M(G.algebra) → Space K f`, the composite `ι K f U ∘ L.ambientMap`;
* `G.image = ι K f U '' L.locus`, equal to the range of `G.chart`
  (`range_chart`).

It then builds bounded restriction maps between local charts of possibly
different affine opens. This is internal supporting material for the atlas of
`Space K f` (`SchemeAnalytificationAtlas`).

## Compatible maps

A bounded map `ρ : G'.algebra → G.algebra` is compatible (`Compatible G G' ρ`)
when `schemePoint G'.affineOpen (ρ ∘ G'.coord) = G.point`.

* `hom_ext`: bounded maps out of `G.algebra` are determined by their scheme
  morphisms (`localDomain_hom_ext` and `schemePoint_injective`). Hence compatible
  maps are unique (`compatible_unique`).
* `compatible_id`, `Compatible.comp`: identities are compatible, and composites of
  compatible maps are compatible (`schemePoint_comp`).
* `chart_comap`, `Compatible.chart`: the chart of a point pulled back along a
  bounded map can be computed from any description of its scheme morphism, by the
  chart compatibility `ι_affinoidBaseMap_eq`. For compatible `ρ`,
  `G'.chart (comap ρ x) = G.chart x`.
* `compatible_inclusion`: restrictions along inclusions of local domains of the
  same affine open are compatible (`inclusion_localAlgebraMap`).
* `compatible_saturatedHom`: for affine opens `V ≤ U`, the bounded pullbacks of
  `saturatedHom K P_U P_V (restriction f h)` are compatible between the chosen
  local-domain representatives. The proof uses
  `saturatedHom_pullback_localAlgebraMap` and `schemePoint_restriction`.

## Lifting and cross-chart restrictions

The remaining results assume `hι : ∀ U, Function.Injective (ι K f U)`. This is a
consequence of clause (2) of the published `SchemeAnalytificationGluingStatement`.

* `exists_lift`: let `α'' : Γ(U'', ⊤) →ₐ[K] R` be such that every point
  `ι K f U'' (affinoidBaseMap … α'' x)` lies in `G.image`. Then some bounded
  `ψ : G.algebra → R` satisfies
  `schemePoint G.affineOpen (ψ ∘ G.coord) = schemePoint U'' α''`.
  Proof: the centers of these points lie in `U` (the published
  `center_ι`, `center_ι_mem`), so by `range_schemePoint_subset` the scheme
  morphism lands in `U`. `exists_schemePoint_eq` then gives
  `α : Γ(U, ⊤) → R` with the same scheme morphism. By `ι_affinoidBaseMap_eq` and
  injectivity of `ι K f U`, every `affinoidBaseMap … α x` lies in `L.locus`, so
  `exists_localDomain_lift` produces `ψ`.
* `exists_compatible`, `cross`: if `G.image ⊆ G'.image`, a compatible map
  `G'.algebra → G.algebra` exists. `cross hι G G' h` is the chosen one, and
  `eq_cross` says that it is the only compatible map.
* `cross_chart`: `G'.chart (comap (cross …) x) = G.chart x`.
* `cross_self`, `cross_trans`: the cross map of `G` to itself is the identity,
  and cross maps compose. Both follow from uniqueness of compatible maps.
* `cross_universal`: let `φ : G'.algebra → R` be bounded with spectrum landing in
  `G'.chart ⁻¹' G.image`. Then `φ` factors uniquely as `ψ ∘ cross …`. Existence
  applies `exists_lift` to `φ ∘ G'.coord`. Uniqueness uses `hom_ext` together
  with `Compatible.schemePoint_comp`.
* `range_comap_cross`, `represents_cross`: the cross map represents the closed
  subset `G'.chart ⁻¹' G.image`, in the sense of the Library's `Represents`. The
  subset is closed as the compact image of a spectrum. The range statement uses
  `cross_chart` and injectivity of `G'.chart`.

## Provenance

Internal. This implements, for the Library's polynomial-locus model, the
existence of bounded restriction maps between affinoid domains of affine
analytifications coming from different affine opens. These maps are needed to
glue the analytifications in step (3) of the proof of Theorem 3.4.1 of
Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), printed p.64/PDF p.78 (registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`, SHA256
`9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`). The
construction characterizes the maps by compatibility of scheme morphisms, not by
Tate acyclicity. Uniqueness comes from the universal property of the local
domains. Existence comes from the lifting lemma above.
