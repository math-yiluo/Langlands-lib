# Proper flat models over finite-type `ℤ`-algebras

Namespace: `Langlands.AlgebraicGeometry.Picard`.

This module proves that a proper flat morphism of finite presentation to an
affine scheme `Spec A` is the base change of a proper flat morphism to
`Spec R`, for an algebra map `R → A` with `R` of finite type over
`ℤ`. In particular this holds for every proper scheme over a field. This is
the standard noetherian approximation argument (EGA IV₃, §8). Here it is
derived entirely from published Library descent theorems; it introduces no
new literature assertion.

## Flatness from a line bundle

`IsLocallyFreeRankOne.flat_of_isFlatOver` shows that `f : X ⟶ Y` is flat if
some locally free rank-one module sheaf `M` on `X` is flat over `Y` in the
sense of the published `Modules.IsFlatOver`. At each point the published
stalk basis `IsLocallyFreeRankOne.relativeStalkLinearEquiv` identifies the
stalk of `M`, as a module over the base local ring, with the local ring of
`X`. Hence the stalk map is flat, and Mathlib's `Flat.of_stalkMap` applies.
The converse direction is the published `LineBundle.isFlatOver`.

## The model predicate

`HasProperFlatFiniteTypeModel p`, for `p : Y ⟶ Spec A`, asserts the existence
of a commutative ring `R : Type u` of finite type over `ℤ`, an algebra
structure `R → A`, a scheme `X₀` with a proper flat morphism
`p₀ : X₀ ⟶ Spec R`, and `π : Y ⟶ X₀` such that
`IsPullback π p p₀ (Spec.map (algebraMap R A))` holds.

## The descent chain

The namespace `ProperFlatFiniteTypeModel` follows the stages of the published
`Modules.ProperNoetherianModelProof`, additionally tracking finite type over
`ℤ`. `finiteType_of_fg` shows that a finitely generated subalgebra over a
finite-type `ℤ`-algebra is of finite type over `ℤ` (Mathlib's
`Algebra.FiniteType.trans`). Each stage works with a ring `T` of finite type
over `ℤ`, hence noetherian, and a Cartesian square over `Spec A → Spec T`.

1. `of_finitePresentation`: separatedness of the base change descends to a
   finitely generated `T₂ ⊆ A` (`isSeparatedSubalgebraDescent`); the new square
   comes from `exists_isPullback_subalgebra'`.
2. `of_isSeparated`: properness descends to `T₃`
   (`isProperSubalgebraDescent`).
3. `of_isProper`: flatness descends to `T₄` through the trivial line bundle.
   Its pullback to `Y` is flat over `Spec A` because `p` is flat
   (`LineBundle.isFlatOver`). `isFlatOverSubalgebraDescent` gives flatness of the
   pulled-back trivial line bundle on the chosen model over `Spec T₄`, and
   `flat_of_isFlatOver` gives flatness of the model morphism. The model is
   proper as a base change of a proper morphism.

`hasProperFlatFiniteTypeModel` starts the chain: with
`A₀ = (⊥ : Subalgebra ℤ A)`, of finite type over `ℤ`, the published
`schemeSubalgebraDescent` gives a finitely presented, quasi-compact,
quasi-separated model over a finitely generated `T₁`.

`field_hasProperFlatFiniteTypeModel` specializes to a proper scheme
`X : Over (Spec k)` over an arbitrary field `k`, including imperfect fields.
Local finite presentation of `X.hom` is Mathlib's instance for locally finite
type morphisms to a locally noetherian scheme. Flatness of `X.hom` is Mathlib's
instance for morphisms to an integral one-point scheme. No projectivity,
smoothness, reducedness, connectedness or section is assumed.
