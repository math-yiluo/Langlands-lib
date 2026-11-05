# Averaging additive functions over a diagonalizable group

Module `Langlands.GroupScheme.LinearAdditiveExtension.DiagonalizableAverage`, namespace
`Langlands.GroupScheme.DiagonalizableAverage`.

This internal construction gives a *Reynolds operator* for the diagonalizable group
`D(Λ) = Diagonalizable.groupScheme (CommRingCat.of k) Λ`. It integrates a `𝔾ₐ`-valued function
of two variables `(z, x) ∈ D(Λ) × X` over the variable `z`. Here `k` is any field and `Λ` is any
additive commutative group in the same universe; no finiteness or torsion-freeness is assumed.
`𝔾ₐ` is the published one-dimensional vector group `VectorGroup.groupScheme (CommRingCat.of k) 1`.
Functions with values in `𝔾ₐ` are morphisms to its underlying scheme. Their sum is the product
of points of the group object, which adds coordinates.

The provenance is internal. The averaging is the standard fact that taking the constant
coefficient in the group algebra `k[Λ]` is an invariant integral on `D(Λ)`. This is the linear
reductivity used in Milne, *Algebraic Groups* (2022), §15h, behind Proposition 15.31 and
Theorem 15.34. The module imports no such theorem; everything is proved from the definitions.

## Coordinates on affine tests

The module works with the affine points `PointedCoordinateWeights.Points V A` of a scheme `V`
over `Spec k`, for `k`-algebras `A`.

- `pmap f v` is change of coefficients along `f : A →ₐ[k] B`. It abbreviates the published
  `PointedCoordinateWeights.pointsMap`.
- `gammaHom A` reads global functions of `Spec A` in `A`, through `Scheme.ΓSpecIso`.
- `coord v ∈ A` and `ofCoord a` translate between affine points of `𝔾ₐ` and elements of `A`.
  They use the published `RelativeRoot.vectorAffineCoordinates` for the coordinates
  `VectorGroup.coordinates`. The lemmas `coord_ofCoord`, `coord_injective`, `coord_mul`,
  `coord_one`, `coord_inv` and `coord_pmap` say that `coord` is a bijective, additive,
  natural map.
- For a commutative group scheme `S` and a character `χ`, `charCoeff χ s ∈ A` is the value of
  `χ` at an affine point `s`, read through `gammaHom`. `coord_weightAction` says that the
  published linear action `VectorGroup.weightAction χ` multiplies the coordinate by this
  value. `charCoeff_pmap`, `charCoeff_one`, `charCoeff_mul` and `charCoeff_mul_inv` record
  naturality and multiplicativity.
- `isAffineHom_diagonalizable`: `D(Λ)` is affine over `Spec k`.

## The group algebra and its translations

Fix a `k`-algebra `A`.

- `const k Λ A : A →ₐ[k] A[Λ]` is the inclusion of constants.
- `univPoint k Λ A` is the point of `D(Λ)` over `A[Λ]` given by the universal character
  `λ ↦ e_λ`. It is built with the published `CharacterAction.characterPoint`.
- `character Λ d` is the character `Λ → Aˣ` of an affine point `d` of `D(Λ)`, from the published
  `Corepresented.affinePointsEquiv`. `characterPoint_character` says that it recovers `d`.
- `translation k Λ t` is the `A`-algebra endomorphism `e_λ ↦ t(λ) e_λ` of `A[Λ]`, viewed as a
  `k`-algebra map. The lemmas `translation_single`,
  `coeff_zero_translation` (it fixes the constant coefficient, since `t(0) = 1`) and
  `translation_comp_const` describe it.
- `coeff_zero_const_mul`, `coeff_zero_const`, `coeff_zero_add`, `coeff_zero_mapAlgHom` and
  `mapAlgHom_comp_const` describe the constant coefficient. It is `A`-linear, fixes constants
  and commutes with change of coefficients.
- `pmap_comp`, `pmap_lift`, `pmap_comp_hom` and `pmap_mul` are the functoriality of `pmap`.
- `pmap_univPoint`: extending coefficients along `f` sends the universal point over `A[Λ]` to
  the universal point over `B[Λ]`.
- `pmap_translation_univPoint`: for a point `d` of `D(Λ)` over `A`, translating the universal
  point by the constant extension of `d` equals the universal point after coefficient change
  along `translation (character d)`. The proof compares the characters.

## The average

For `X` over `Spec k` and `Ψ : D(Λ) ⊗ X ⟶ 𝔾ₐ`:

- `pair Λ x` is the point `(univPoint, const x)` of `D(Λ) ⊗ X` over `A[Λ]`, for an affine point
  `x` of `X`.
- `averagePoint Λ Ψ A x` is the point of `𝔾ₐ` whose coordinate is the coefficient at `0` of
  `coord (pair Λ x ≫ Ψ) ∈ A[Λ]`. `averagePoint_naturality` proves that it is natural in `A`.
- For `X` affine over `Spec k`, `average Λ Ψ : X ⟶ 𝔾ₐ` is the morphism with these values on
  affine points. It is produced by the published `PointedCoordinateWeights.homOfAffinePoints`.
  `comp_average` and `coord_comp_average` give its values.

The proved properties are these. Each is checked on affine points with the published
`affine_hom_ext`.

- `comp_average_eq` (naturality): for `t : Y ⟶ X` with `Y` affine,
  `t ≫ average Λ Ψ = average Λ ((D(Λ) ◁ t) ≫ Ψ)`.
- `average_snd` (constants): `average Λ (snd ≫ Θ) = Θ`.
- `average_mul` (additivity): `average Λ (Ψ * Ψ') = average Λ Ψ * average Λ Ψ'`.
- `average_weightAction` (linearity): for a commutative group scheme `S`, a character `χ` and
  `s : X ⟶ S`, averaging commutes with the action of `χ(s)`, which depends only on `x`:
  `average Λ (act (snd ≫ s) Ψ) = act s (average Λ Ψ)`.
- `average_translate` (invariance): for `d₀ : X ⟶ D(Λ)`, the substitution `z ↦ z · d₀(x)` does
  not change the average:
  `average Λ (lift (fst * (snd ≫ d₀)) snd ≫ Ψ) = average Λ Ψ`.
  The integrand at the universal point becomes its image under `translation (character d₀(x))`,
  and translation fixes the constant coefficient.
