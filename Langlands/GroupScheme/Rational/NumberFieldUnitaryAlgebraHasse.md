# The Hasse kernel for special unitary groups of algebras with involution

Module: `Langlands.GroupScheme.Rational.NumberFieldUnitaryAlgebraHasse`.

Let `F ⊆ E` be fields, `B` a finite-dimensional central simple `E`-algebra that is an
`F`-algebra through `E` and finite-dimensional over `F`, `τ` an `F`-linear involution
of `B`, and `p : UnitaryAlgebra.Presentation E τ G` a presentation of a group scheme
`G` over `Spec F` as `SU(B, τ)`. Write `U` for the unit group scheme
`FiniteAlgebraUnits.groupScheme (Module.finBasis F B)` of `B`, whose points with
coefficients in `R` are the units of `R ⊗[F] B`.

## The embedding into the units of `B`

`toUnits p R` sends a point of `G` to the underlying unit of its special unitary point,
and `toAmbient p R` sends it to the corresponding point of `U`. The module proves that
`toAmbient p R` is injective, natural in `R` (`toAmbient_naturality`, from the
naturality of the presentation and of `FiniteAlgebraUnits.affinePointsEquiv`), that
its values are special unitary (`toUnits_mem`), and that every point of `U` whose
unit is special unitary is a value (`exists_toAmbient_eq`).

## Galois descent of a cocycle

For a finite Galois field extension `L/F`, `exists_unit_of_fixed` shows that a unit of
`L ⊗[F] B` fixed by `Gal(L/F)` (acting on `L`) is `1 ⊗ y` for a unit `y` of `B`, using
the published `mem_range_includeRight_iff` for the unit and its inverse;
`exists_fieldUnit_of_fixed` is the same for `E ⊗[F] L`. Over an infinite ground field,
`exists_ambient_coboundary` applies the published finite-algebra Hilbert 90
(`Langlands.Algebra.exists_unit_coboundary`) to the values of a cocycle
`ξ` on the cover `Spec L → Spec F`, giving a point `b` of `U` with
`toAmbient (ξ_s) = b · s(b)⁻¹` for every `s ∈ Gal(L/F)`.

A `CocycleDescent E p ξ` records such a primitive `b`, a unit `y` of `B` with
`b⁻¹ τ(b⁻¹) = 1 ⊗ y` and a unit `z` of `E` with `Nrd(b⁻¹) = z ⊗ 1` for the relative
reduced norm. `exists_cocycleDescent` constructs one: writing `c_s` for the unit of
`ξ_s`, one has `s(b⁻¹) = b⁻¹ c_s`; since `c_s τ(c_s) = 1` and `Nrd(c_s) = 1`, the
elements `b⁻¹ τ(b⁻¹)` and `Nrd(b⁻¹)` are Galois fixed and descend.

## Local solutions

`CocycleDescent.exists_local_of_baseChange_isTrivial`: if the pullback of `ξ` to a
field `K` of characteristic zero over `F` is trivial, there is a unit `x` of
`K ⊗[F] B` with `1 ⊗ y = x τ(x)` and `Nrd(x) = z ⊗ 1`. A finite Galois comparison
field `M/K` receiving `L` is chosen by the published
`CentralSimpleUnits.exists_finiteGalois_over_baseChange`. The pullback trivialization
gives a point `Y` of `G` over `M` with the same coboundary as `b`, by
`GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial`; the quotient
`Y⁻¹ b` is fixed by `Gal(M/K)` and descends to a point `r` of `U` over `K`. The unit
`x` of `r⁻¹` satisfies `x = b⁻¹ Y` over `M`, so `x τ(x) = b⁻¹ τ(b⁻¹)` and
`Nrd(x) = Nrd(b⁻¹)` there because `Y` is special unitary; injectivity of
`K ⊗[F] B → M ⊗[F] B` and of `E ⊗[F] K → E ⊗[F] M` gives the equations over `K`.

## Global trivialization

`CocycleDescent.isTrivial_of_global`: if a unit `X` of `B` satisfies `y = X τ(X)` and
`reducedNorm E B E (1 ⊗ X) = z`, then `w = b · (1 ⊗ X)` is special unitary, it has the
same coboundary as `b` because `1 ⊗ X` is Galois fixed, and its point of `G` (by
`exists_toAmbient_eq`) trivializes `ξ` through `GaloisCocycle.isTrivial_iff`.

## The arithmetic step

`isTrivial_of_landherr_unitaryNorm` assumes that `F` is a number field, `E/F` a
separable quadratic extension and `τ` a unitary involution
(`τ (algebraMap E B e) = algebraMap E B (SU3Root.conjugation F E e)`), and takes
`NumberFieldLandherrStatement` and `NumberFieldUnitaryNormStatement` as premises. A
locally trivial cocycle has local solutions at every place, archimedean and finite,
by the local step applied to the completions. The element `y` is symmetric because
`b⁻¹ τ(b⁻¹)` is. Landherr's theorem gives `x` with `y = x τ(x)`. At every place,
`(1 ⊗ x)⁻¹ x_v` is unitary with relative reduced norm `z Nrd(x)⁻¹` (using
`relativeNorm_includeRight`), so the unitary norm theorem gives a unitary `w` of `B`
with `Nrd(w) = z Nrd(x)⁻¹`. Then `X = x w` satisfies `X τ(X) = y` and `Nrd(X) = z`,
and the global step trivializes the cocycle.

## Provenance

This is the reduction of the Hasse principle for `SU(B, τ)` to Landherr's theorem and
the unitary norm theorem in Platonov and Rapinchuk, *Algebraic Groups and Number
Theory* (1994), §6.7, pp. 359–360, and Kneser, *Lectures on Galois Cohomology of
Classical Groups* (1969), §5.5 (the reduction to the pair `(y, z)`), formulated for the
Library's natural cocycles on finite Galois covers. The descent steps follow the
published Hermitian matrix case in `Langlands.GroupScheme.Rational.HermitianGaloisGramDescent`
and `Langlands.GroupScheme.Rational.HermitianGaloisLocalGram`.
