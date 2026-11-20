# Frame charts from a universal frame datum

This module reduces `FrameChartRepresentabilityStatement` for one family `ρ` to the
existence of a universal datum. All schemes lie in universe `0`.

## `IsUniversalFrameDatum ρ X U`

For a level base `X : LevelBase n` and a datum `U : Datum P X.obj g d n`, a structure of
three propositions:

- `injective`: for morphisms `f f' : T ⟶ X` of level bases, a polarized isomorphism
  `U.pullback f.hom ≅ U.pullback f'.hom` forces `f = f'`;
- `exists_pullback`: every datum `b` over a level base `T` with `b.frameLocus ρ = ⊤` is
  polarized-isomorphic to `U.pullback f.hom` for some `f : T ⟶ X`;
- `frameLocus_eq_top`: every datum polarized-isomorphic to some `U.pullback f.hom` has frame
  locus `⊤`.

## `frameChart_of_isUniversalFrameDatum`

If `U` is a universal frame datum over `X`, then the natural transformation
`a := uliftYonedaEquiv.symm U.classOf : uliftYoneda.{1}.obj X ⟶ moduliFunctor P g d n hd hn`
has injective components, and the class of a datum `b` over `T` lies in the image of
`a.app (op T)` exactly when `b.frameLocus ρ = ⊤`. This is the conclusion of
`FrameChartRepresentabilityStatement` for `ρ` and `X`.

Proof: by Yoneda, `a.app (op T) ⟨f⟩` is the class of `U.pullback f.hom`
(`moduliFunctor_map_classOf`). Equality of classes is the existence of a polarized
isomorphism (`Quotient.exact`, `Datum.classOf_eq`), so the three fields give injectivity
and the two directions of the image characterization.

## Provenance

Internal: the standard translation between a universal family and a representing object
(fine moduli), for the frame-chart subfunctor. Part of Task 7811's reduction
(`FrameChartRepresentabilityReduction`).
