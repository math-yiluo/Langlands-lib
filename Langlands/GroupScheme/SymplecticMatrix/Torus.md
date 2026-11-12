# The diagonal torus of the split symplectic group and its Lie weights

This internal module defines the diagonal torus `t ↦ diag(t, t⁻¹)` of the split symplectic
group `SymplecticMatrix.groupScheme l R`. It also computes the weights of this torus on the
Lie algebra in the matrix coordinates `lieMatrix` of `SymplecticMatrix.LieAlgebra`. Here `l`
is a finite index type with decidable equality. Matrices are indexed by `l ⊕ l`: `inl a` is
the `a`-th row of the upper block and `inr a` the `a`-th row of the lower block.

## Weights of diagonal matrices

* `torusWeights τ : l ⊕ l → Aˣ`, for `τ : ULift l → Aˣ`, is the list of diagonal entries of
  `diag(t, t⁻¹)`: `t_a` at `inl a` and `t_a⁻¹` at `inr a`.
* `weightCoord l : l ⊕ l → (l → ℤ)` gives the corresponding weights in coordinates:
  `weightCoord l (inl a) = e_a` and `weightCoord l (inr a) = -e_a`, where `e_a = Pi.single a 1`.
  The `@[simp]` lemmas `weightCoord_inl` and `weightCoord_inr` unfold it.
* `prod_zpow_single`, `torusWeights_eq_prod`: `torusWeights τ x = ∏_c τ_c ^ (weightCoord l x)_c`.
* `prod_zpow_weightCoord_sub`: the monomial of `weightCoord l x - weightCoord l y` is
  `torusWeights τ x * (torusWeights τ y)⁻¹`.
* `torusWeights_mulSingle`: at the point `τ = Pi.mulSingle c U`, which is `U` in coordinate `c`
  and `1` elsewhere, the weight of `x` is `U ^ (weightCoord l x)_c`.
* `weightCoord_injective`: distinct indices have distinct weights.

## The torus

* `diagonalTorus l R : (splitTorus.commGroupScheme (Spec R) (ULift l)).toGrp ⟶ groupScheme l R`
  is the Library's diagonal torus `GeneralLinear.diagonalTorus l R` of `GL_l`, followed by the
  Levi embedding `leviMap R : GL_l ⟶ Sp_{2l}`, `g ↦ [[g, 0], [0, (g⁻¹)ᵀ]]`, of
  `SymplecticMatrix.Reductive`. On points it sends `(t_a)` to `diag(t, t⁻¹)`.
* `coe_inv_diagonalTorusUnits`: the inverse of `diag(t_a)` is `diag(t_a⁻¹)`. The Library has a
  version with an extra, unused base-ring argument, so it is restated here without it.
* `affinePointsEquiv_leviMap`: on affine points the Levi embedding is `leviHom`.
* `levi_diagonalTorusUnits`: `levi (diag t) = diag(torusWeights t)`.
* `affinePointsEquiv_diagonalTorus_inclusion`: an affine point `t` of the torus, mapped into
  `GL_{l ⊕ l}` through `Sp`, is the diagonal matrix of `torusWeights` of its coordinates
  `GeneralLinear.torusCoords t`.
* `pointsEquiv_diagonalTorus`: the same description on points over every test scheme, as
  `leviHom` of the diagonal matrix.
* `mono_diagonalTorus_hom`: the diagonal torus is a monomorphism. The upper-left diagonal
  entries of `diag(t, t⁻¹)` recover `t`.

## Over a field

Let `k` be a field and `𝔻` the split torus `splitTorus.commGroupScheme (Spec k) (ULift l)`.

* `isAffineHom_groupScheme_of`, `smooth_groupScheme_of`: the Library's instances
  `isAffineHom_groupScheme` and `smooth_groupScheme`, restated for the base
  `CommRingCat.of k`. Instance search does not find the originals for this base.
  `isAffineHom_diagonalTorusSource` does the same for `𝔻`.
* `isSplitTorus_diagonalTorus l k`: `𝔻` is a split torus.
* `isClosedSubgroup_diagonalTorus l k`: the diagonal torus is a closed subgroup. A
  monomorphism from a torus is a closed subgroup (`IsTorus.isClosedSubgroup_of_mono`).
* `isSplitSubtorus_diagonalTorus l k`: the two facts together.
* `characterValue_eq_prod`: a character `χ` of `𝔻` takes the value
  `∏_c t_c ^ χ_c` at an affine point with coordinates `t`. Here `χ_c` are the coordinates
  `GeneralLinear.characterCoordEquiv l k χ` of the Library's `Reductive.GeneralLinearRoots`.
* `mem_weightSpace_diagonalTorus_iff`: membership of a Lie algebra element `X` in the weight
  space of `χ` (the Library's `weightSpace`), written entrywise in the matrix `lieMatrix X`
  for every `k`-algebra `A` and every affine point. Proof: transport to `GL_{l ⊕ l}` with
  `lieKernelHomLinear_mem_weightSpace_iff` and use the Library's adjoint action of `GL` in
  coordinates.
* `mem_weightSpace_diagonalTorus_iff_support` (**weights of the diagonal torus**): `X` lies in
  the weight space of `χ` exactly when, for every entry `(x, y)` with `lieMatrix X x y ≠ 0`,
  the coordinates of `χ` are `weightCoord l x - weightCoord l y`. For the forward direction,
  evaluate at the Laurent-polynomial point `Pi.mulSingle c T` and compare exponents of `T`
  (`GeneralLinear.exponent_eq_of_C_mul_T`). The converse is `prod_zpow_weightCoord_sub`.

No assumption is made on `l` (it may be empty) or on the characteristic.

## Provenance

This is the standard diagonal torus of `Sp_{2l}`. This module only shows that every weight
on the Lie algebra is a difference `w(x) - w(y)`. Maximality and the long roots are in
`SymplecticMatrix.Roots`. The module is internal. Its proofs follow the Library's treatment
of the diagonal torus of `GL_n` in `Reductive.GeneralLinearRoots`, transported along the
Levi embedding.
