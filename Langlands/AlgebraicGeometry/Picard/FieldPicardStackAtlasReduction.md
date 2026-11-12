# Reduction of the field Picard stack atlas to finite-type `ℤ`-algebras

Namespace: `Langlands.AlgebraicGeometry.Picard`.

`fieldPicardStackAtlas_of_finiteType` proves the implication

`FiniteTypePicardStackAtlasStatement.{u} → FieldPicardStackAtlasStatement.{u}`

between the two published statements, at every universe `u`. It does not prove
either statement. The finite-type statement remains an explicit hypothesis.

`fieldPicardStackAtlasOfFiniteType` is the same implication packaged as a
definition: its body is the theorem `fieldPicardStackAtlas_of_finiteType`.

## Argument

Let `k : Type u` be an arbitrary field and `X : Over (Spec k)` with
`IsProper X.hom`.

1. `field_hasProperFlatFiniteTypeModel` (module
   `Picard.ProperFlatFiniteTypeModel`) gives a commutative ring `R : Type u`
   of finite type over `ℤ` with an algebra map `R → k`, a proper flat
   `p₀ : X₀ ⟶ Spec R`, and an actual Cartesian square
   `IsPullback π X.hom p₀ (Spec.map (algebraMap R k))`.
2. The hypothesis, applied to `R` and `Over.mk p₀`, gives an actual smooth
   surjective scheme atlas of the relative Picard stack of `p₀`, locally of
   finite type over `Spec R`.
3. `PicardGroupoid.hasLocallyFiniteTypeSmoothSchemeAtlas_of_isPullback`
   (module `Picard.StackAtlasBaseChange`) base changes this atlas along the
   Cartesian square. The result is an atlas of `X.hom` with the same smooth
   surjective representing schemes for the actual point fibres on the full
   slices.

## Relation to the sources

The task's source, the Stacks Project snapshot
`stacks-picard-stack-algebraicity-2026-11-01`, proves algebraicity of the
Picard stack for flat, proper, finitely presented morphisms over an arbitrary
base (`0D04.html`, Proposition 99.10.2). The finite-type statement is the
noetherian case of that result. The present module supplies the passage from
finite-type `ℤ`-algebras to fields by the standard noetherian approximation
argument and the compatibility of the Picard stack with base
change of the proper scheme. Both inputs are proved here from published
Library results.
