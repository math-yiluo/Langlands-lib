# Gluing ordered torsion sections along the cover by small opens

## Setting

`hU : iSup U = ⊤`; an abelian scheme `A` over `S`; for every small open `W` an ordered
tuple `w W : SectionTuple ((baseChange W.ι).obj A) g n` of `n`-torsion sections; and the
compatibility `hw`: for `W ≤ W'` and every index `i`, the composites of the sections
with the projection to `A.X.left` satisfy
`(w W i).left ≫ pullback.fst = S.homOfLE h ≫ (w W' i).left ≫ pullback.fst`.

## Declarations

Namespace `Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing`.

- `gluedTorsionSection i : S ⟶ A.X.left`: the glued underlying morphism
  (`glueMorphismsOfLocallyDirected` on `subCover hU`); `gluedTorsionSection_restrict`;
  `gluedTorsionSection_hom`: it is a section of `A.X.hom`.
- `gluedPoint i : Over.mk (𝟙 S) ⟶ A.X`.
- `smallOpenPoint W`, `smallOpenPoint_gluedPoint`: restricted to `W`, the glued point
  corresponds under the base-change adjunction (`GroupScheme.baseChangePointsEquiv`) to
  the local section.
- `gluedPoint_pow`: `gluedPoint i ^ n = 1`. On each `W`, the restriction is the image
  of `(w W i)^n = 1` under the multiplicative equivalence `baseChangePointsEquiv`
  (Mathlib's `MonObj.comp_pow`, `MonObj.comp_one`).
- `gluedLevel i`, `gluedTuple`: the glued torsion points and tuple.
- `pullbackTuple_gluedTuple W`: `pullbackTuple W.ι gluedTuple = w W` (compare both
  projections out of the fibre product, using `pullbackTuple_fst`).

## Provenance

Internal: Zariski descent of sections; being `n`-torsion is checked locally.
