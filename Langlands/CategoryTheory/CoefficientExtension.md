# Morphisms with coefficients in a commutative ring

For a preadditive category `C` and a commutative ring `R : Type`, the module
`Langlands.CategoryTheory.CoefficientExtension` constructs the `R`-linear
category `CoefficientExtension R C`. Its objects are precisely the objects of
`C`, wrapped by `CoefficientExtension.of`, and its morphism groups are

```text
Hom_R(X, Y) = R ⊗[ℤ] Hom_C(X, Y).
```

This is the construction of Kottwitz, *Points on some Shimura varieties over
finite fields*, J. Amer. Math. Soc. 5 (1992), §9, printed p.401 (PDF p.29),
source `kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`:
for any commutative ring `R` the category of abelian varieties *up to
`R`-isogeny* has Hom groups `Hom(A, B) ⊗_ℤ R`, and an `R`-isogeny is an
isomorphism of that category. The source writes the tensor factor on the
right; the module places `R` on the left, as the Library's
`Langlands.Rationalization` does for `R = ℚ`. Nothing is inverted except
through the coefficients: an ordinary morphism becomes invertible only if an
inverse exists in `R ⊗ Hom`.

## Construction

* `Hom R X Y` is the tensor product above. `comp R X Y Z` is the ℤ-bilinear
  map obtained from the tensor universal property, with
  `comp_tmul : (r ⊗ f, s ⊗ g) ↦ (r s) ⊗ (f ≫ g)`; `identity R X` is
  `1 ⊗ 𝟙 X`. The unit and associativity laws are proved by induction on
  tensors.
* `comp_smul_left` and `comp_smul_right` prove that composition is
  `R`-linear in each variable, and `compLinear` bundles it as an
  `R`-bilinear map. These give the `Category`, `Preadditive` and
  `CategoryTheory.Linear R` instances.
* `ofHom R : (X ⟶ Y) →ₗ[ℤ] Hom R X Y`, `f ↦ 1 ⊗ f`, and the additive functor
  `inclusion R : C ⥤ CoefficientExtension R C`. `tmul_eq_smul_ofHom` writes
  a pure tensor as `r • ofHom R f`.
* `End R X` is the endomorphism `R`-algebra of `of X` in the constructed
  category (multiplication `f * g = g ≫ f`), `algebraMap_eq` identifies its
  scalars with `r ⊗ 𝟙 X`, and `ofEnd R X` is the unital ring map from
  `End X`.
* `extendAddHom R φ : R ⊗[ℤ] M →ₗ[R] R ⊗[ℤ] N` is the `R`-linear extension
  `r ⊗ x ↦ r ⊗ φ x` of an additive map `φ : M →+ N`. It is used to extend
  additive operations on Hom groups, for instance dualization of abelian
  schemes.

## Extension of additive functors

For an additive functor `F : C ⥤ D` into an `R`-linear preadditive category,
`liftHom R F` is the `R`-linear map `r ⊗ f ↦ r • F.map f`, obtained from
`TensorProduct.AlgebraTensorModule.lift`. `liftHom_comp` proves that it
preserves composition, and `lift R F` is the resulting additive, `R`-linear
functor. `inclusionLiftIso` identifies its restriction along `inclusion R`
with `F`. `liftEnd R F X` is the induced `R`-algebra homomorphism on
endomorphism algebras, with `liftEnd_ofEnd` and `liftEnd_tmul`.

## Change of coefficients and the rationalization

For a ring homomorphism `φ : R →+* R'`, `changeHom φ X Y` is
`LinearMap.rTensor` of `φ`, sending `r ⊗ f` to `φ r ⊗ f`. It is
`φ`-semilinear (`changeHom_smul`), preserves identities and composition,
and gives the additive functor `changeCoefficients φ`, the isomorphism
`inclusionChangeIso` with the inclusions, and the unital ring map
`changeEnd φ X`.

For `φ : R →+* ℚ` the same formula gives the additive functor
`toRationalization φ : CoefficientExtension R C ⥤ Langlands.Rationalization C`
into the Library's existing rationalization, whose Hom groups are
`ℚ ⊗[ℤ] Hom`. `inclusionToRationalizationIso` compares the two inclusions
of `C`, and `toRationalEnd φ X` is the unital ring map to
`Langlands.Rationalization.End X`, with `toRationalEnd_ofEnd`.

## Scope

The construction is purely algebraic and is derived from Mathlib's tensor
products and linear categories, following the generic rationalization in
`Langlands.CategoryTheory.Rationalization` and its extension in
`Langlands.CategoryTheory.RationalizationLift`. No property such as
faithfulness of `changeHom`, flatness of `R` or invertibility of particular
morphisms is asserted. The coefficient ring is in `Type`, which is the case
for `ℚ` and for the localization `ℤ_(p)`.
