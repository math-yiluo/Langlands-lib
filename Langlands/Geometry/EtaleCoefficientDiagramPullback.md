# Pulling geometric coefficient diagrams back along morphisms of scheme diagrams

This file extends the geometric coefficient diagrams of
[EtaleGeometricCoefficientDiagram](EtaleGeometricCoefficientDiagram.md) along a
morphism of contravariant scheme diagrams. A coefficient diagram on one scheme
diagram is pulled back by inverse image to the other. The transition maps of the
new diagram are proved coherent from the coherence of inverse images. It is an
internal construction and asserts no result from the literature. It generalizes
`canonicalCoefficients` of
[EtaleCanonicalCoefficientDiagram](EtaleCanonicalCoefficientDiagram.md), which
pulls back a single sheaf on one base scheme.

The intended use is a family of coefficient sheaves on Shimura varieties over
their field of definition, pulled back to their base changes to an algebraic
closure. There the source diagram is indexed by levels and torsion stages, and
the target diagram has the same index together with the Galois group. The pulled
back diagram then carries the Galois action by construction. The file itself
concerns arbitrary schemes and arbitrary scheme maps; it needs no etaleness
condition.

## Inputs and notation

Schemes, the commutative ring `R : Type u` and module carriers have universe
`u`. `ModuleSheaf X R` is the category of sheaves of `R`-modules on the small
etale site of `X`. `inverseImage f R` (written `f^*`) is the Library's geometric
inverse image. Its composition, identity and equality comparisons are
`inverseImageComp`, `inverseImageId` and `inverseImageCongr`. The triangle
comparison

```text
T(p, q, f, e) = projectionInverseImageIso R p q f e : p^* ⋙ f^* ≅ q^*,   e : f ≫ p = q,
```

is `inverseImageComp R p f` followed by the equality transport along `e`.

## Triangle lemmas

The namespace `Langlands.Geometry.EtaleInverseImage` gains the following
lemmas:

* `inverseImageCongr_inv_app`: the inverse of an equality transport is the
  transport along the reversed equality.
* `projectionInverseImageIso_congr_top`: if `h : f = f'`, then the transport
  along `h`, followed by `T(p, q, f', e')`, is `T(p, q, f, e)`.
* `projectionInverseImageIso_congr_comp`: `T(p, q, f, e)` followed by the
  transport along `e' : q = q'` is `T(p, q', f, e.trans e')`.
* `projectionInverseImageIso_paste`: for triangles `f ≫ p = q`, `g ≫ q = r`,
  `k ≫ p = r` and `g ≫ f = k`,

  ```text
  g^*(T(p, q, f)) ≫ T(q, r, g) = T(f, k, g)(p^* M) ≫ T(p, r, k).
  ```

  It restates the Library's `projectionInverseImageIso_comp`, folding the
  composition comparison and the equality transport into the triangle
  comparison `T(f, k, g)`.
* `projectionInverseImageIso_top_id`: when the top map `f` equals `𝟙`,
  `T(p, q, f)` is the transport along `f = 𝟙`, then `inverseImageId`, then the
  transport along `p = q`.
* `projectionInverseImageIso_base_id`: when the base map `p` equals `𝟙`,
  `T(p, q, f)` is `f^*` of the transport along `p = 𝟙` followed by
  `inverseImageId`, then the transport along `f = q`. The proof uses the
  Library's `inverseImageComp_id_target`.

## Square comparisons

For a commuting square `s : p₂ ≫ f = f' ≫ p₁`, with `p₁ : Y₁ ⟶ X₁`,
`p₂ : Y₂ ⟶ X₂`, `f : X₂ ⟶ X₁` and `f' : Y₂ ⟶ Y₁`, the morphism
`squareInverseImageMap R p₁ p₂ f f' s M` is

```text
f'^*(p₁^* M) --T(p₁, f' ≫ p₁, f', rfl)--> (f' ≫ p₁)^* M --T(f, f' ≫ p₁, p₂, s)⁻¹--> p₂^*(f^* M).
```

It is an isomorphism, being a composite of isomorphisms, but only the morphism
is used. The following are proved:

* `squareInverseImageMap_naturality`: it is natural in `M`.
* `squareInverseImageMap_id`: suppose `p₁ = p₂ = p`, `f = 𝟙` and `f' = 𝟙`, with
  equalities `e` and `e'`. Then the square comparison, followed by `p^*` of the
  identity comparison of `f`, equals the identity comparison of `f'` at
  `p^* M`. Here the identity comparison of `f` is the transport along `e`
  followed by `inverseImageId`.
* `squareInverseImageMap_base_id`: suppose only `f = 𝟙` (by `e`), and
  `e' : f' ≫ p₁ = p₂`. Then the square comparison, followed by `p₂^*` of the
  identity comparison of `f`, is the triangle comparison `T(p₁, p₂, f', e')`.
  This identifies square comparisons over an identity base map with the
  comparisons used by Galois actions on inverse images of sheaves from a base,
  such as `cmGeometricGaloisInverseImageIso`.
* `squareInverseImageMap_comp`: take squares `sa`, `sb` and `sab` for arrows
  `fa, fb, fab` below and `fa', fb', fab'` above, with `ec : fb ≫ fa = fab` and
  `ec' : fb' ≫ fa' = fab'`. Then

  ```text
  T(fa', fab', fb', ec')(p₁^* M) ≫ square(sab)(M)
    = fb'^*(square(sa)(M)) ≫ square(sb)(fa^* M) ≫ p₃^*(T(fa, fab, fb, ec)(M)).
  ```

  The proof applies `projectionInverseImageIso_paste` three times, to the top
  triangles, the left triangles and the bottom triangles. It identifies the
  remaining right triangle through `projectionInverseImageIso_congr_comp` and
  `projectionInverseImageIso_congr_top`, and cancels isomorphisms.

## Pulling back coefficient diagrams

In the namespace `Langlands.Geometry.EtaleGeometricDiagram`, let `J` be a
category, and let `S S' : J ⥤ Scheme.{u}ᵒᵖ` be scheme diagrams. Write
`X_i = (S.obj i).unop`, `X'_i = (S'.obj i).unop`, `f_a = (S.map a).unop` and
`f'_a = (S'.map a).unop`. A morphism `π : S ⟶ S'` gives scheme maps
`diagramProjection π i = (π.app i).unop : X'_i ⟶ X_i`.
`diagramProjection_square` proves the naturality square
`p_j ≫ f_a = f'_a ≫ p_i`. `diagramInverseImageComp_eq` records, by
definition, that the composition comparison `diagramInverseImageComp` of a
diagram is the triangle comparison of `T.map_comp`.

For `D : CoefficientDiagram R S`, `CoefficientDiagram.pullback R π D` is the
coefficient diagram on `S'` with

```text
obj i   = p_i^*(D.obj i),
map a   = squareInverseImageMap(p_i, p_j, f_a, f'_a, square a)(D.obj i) ≫ p_j^*(D.map a).
```

Its identity law follows from `squareInverseImageMap_id` and the identity law of
`D`. Its composition law follows from `squareInverseImageMap_comp`, naturality of
the square comparison, and the composition law of `D`. `pullback_obj` and
`pullback_map` state the definitions.

`pullbackMap` sends a morphism `α : D ⟶ E` to the family `p_i^*(α.app i)`. Its
compatibility with transitions follows from naturality of the square comparison.
`pullbackFunctor` is the resulting functor
`CoefficientDiagram R S ⥤ CoefficientDiagram R S'`.

## Scope

The file constructs no specific scheme diagram, no cohomology and no Galois
action. Composing `pullback` with `reindex` (along, for example, the projection
`J × SingleObj G ⥤ J`) and with the cohomology constructions of
[EtaleGeometricActionDiagram](EtaleGeometricActionDiagram.md) is left to the
modules that use it.
