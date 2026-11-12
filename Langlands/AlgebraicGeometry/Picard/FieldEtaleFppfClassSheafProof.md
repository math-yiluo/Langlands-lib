# Proof: the etale Picard class sheaf of a proper scheme over a field is an fppf sheaf

Module `Langlands.AlgebraicGeometry.Picard.FieldEtaleFppfClassSheafProof`.

`Langlands.AlgebraicGeometry.Picard.fieldEtaleFppfClassSheaf` proves the published
proposition `Langlands.AlgebraicGeometry.Picard.FieldEtaleFppfClassSheafStatement.{u}`. For
every field `k : Type u` and every `X : Over (Spec k)` with `IsProper X.hom`, the presheaf
`RelativePicard.etaleClassSheafPresheaf X.hom` (the etale sheafification of the ordinary
relative line-bundle classes) satisfies the fppf sheaf condition on the entire slice
`Over (Spec k)`. There are no further hypotheses: fields may be imperfect, `X` may be
nonreduced, disconnected or without rational points, and test schemes are arbitrary. The
universe `u` is kept.

## Proof

1. `RigidifyingSubscheme.exists_finite_injective` (module `RigidifyingFiniteSubscheme`) gives a
   scheme `Z` and `z : Z ⟶ X` such that `g := z ≫ X.hom` is finite and `z` is injective on
   global functions. `Z` is a finite coproduct of spectra of finite-dimensional quotients of
   affine coordinate rings of `X`.
2. `RigidifyingSubscheme.injective_zRel_appTop` transfers this injectivity to
   `T ×_k Z ⟶ T ×_k X` for every test `T`, using the published flat base change of global
   functions over a field. A finite `g` is proper.
3. `SubschemeRigidification.isSheaf_etaleClassSheafPresheaf_of_rigidifying` (module
   `SubschemeRigidifiedComparison`) concludes. It rigidifies line bundles along `T ×_k Z`. The
   units of `T ×_k Z` act through the smooth quotient of the unit group scheme of `Z` by that of
   `X` (published `normalSubgroupQuotient`). Ordinary classes are, etale-locally, images of
   rigidified classes, and rigidified classes with the same ordinary class are etale-locally
   translates (smooth surjections have etale-local sections). Hence the canonical comparison
   `RelativePicard.etaleToFppfClassSheaf X.hom` is locally bijective, so it is an isomorphism.
   The published `RelativePicard.etaleToFppfClassSheaf_isIso_iff` turns this into the fppf sheaf
   property.

The proof does not use `FieldPicardSheafAlgebraicSpaceStatement`,
`FieldPicardSheafRepresentabilityStatement`, or any proof of either.

## Supporting internal modules

- `QuotientActionLocality`: the abstract engine for etale-local orbits and lifts.
- `SubschemeRigidifiedClasses`, `SubschemeRigidifiedDescent`: rigidified classes, unit action,
  separation and descent.
- `FinitePointsGeneratingSection`, `SubschemeRigidifiedLocal`: local rigidifiability.
- `RelativeUnitGroupSchemes`: unit group schemes and the quotient.
- `SubschemeRigidifiedComparison`: the assembly above.
- `RigidifyingFiniteSubscheme`: the finite subscheme.

Each module has its own Markdown explanation.
