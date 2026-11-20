# Gluing homomorphisms of abelian schemes along the cover by small opens

## Setting

`hU : iSup U = ⊤`; abelian schemes `A`, `A'` over `S`; for every small open `W`
(`SubOpens U`) a homomorphism `loc W : (baseChange W.ι).obj A ⟶ (baseChange W.ι).obj A'`,
compatible on nested opens in the sense `hloc`: for `W ≤ W'`,
`hom (loc W) ≫ pullback.map … (S.homOfLE h) … = pullback.map … (S.homOfLE h) … ≫ hom (loc W')`
(the canonical maps of fibre products over `W → W'`, for `A'` and for `A`).

## Declarations

Namespace `Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing`.

- `homCover hU`: the open cover of `A.X.left` pulled back from `subCover hU`
  (Mathlib's `pullback₁`, locally directed by `locallyDirectedPullbackCover`).
- `homCover_compat`, `homCover_w`: the local maps `hom (loc W) ≫ pullback.fst` are
  compatible with its transition maps and lie over `S`.
- `gluedHomOver`: the glued morphism `A.X ⟶ A'.X` over `S`
  (`glueMorphismsOverOfLocallyDirected`); `fst_gluedHomOver_left` describes its
  restrictions.
- `gluedHomOver_unit`: it preserves the unit sections (checked on the cover of `S`, using
  `unitSection_baseChange_fst` and `unitSection_hom`).
- `gluedHom`: the glued homomorphism `A ⟶ A'` (a monoid morphism by
  `pointedMorphismRigidity`); `hom_gluedHom`.
- `baseChange_map_gluedHom W`: `hom ((baseChange W.ι).map gluedHom) = hom (loc W)`
  (both components into the fibre product agree).

## Provenance

Internal: Zariski descent of morphisms, with the group structure recovered by rigidity.
