# The Harish-Chandra map of the centre through the parabolic projection

Module `Langlands.Algebra.ParabolicCenterProjectionCoordinates`, namespace
`Langlands.Algebra.ParabolicCenterProjection.GradingData`.

Fix `D : GradingData g H` and `j : m →ₗ⁅ℂ⁆ g` as in
`Langlands.Algebra.ParabolicCenterProjectionLevi`.

## The polynomial ring

- `zeroIndex`: the basis indices of grading zero, `zeroIndexEquiv` identifies them with the Levi
  indices of grading zero, and `cartanBasis` is the corresponding basis of `leviCartan`, with
  `cartanToG (cartanBasis c) = b c` where `cartanToG = j ∘ incl` (`cartanToG_basis`).
- `cartanPoly`: the isomorphism of `Z(U(leviCartan)) = U(leviCartan)` with
  `MvPolynomial zeroIndex ℂ` given by `AbelianEnveloping.polyEquiv`, for the order of the
  letters of grading zero inherited from the order of decreasing grading.
- `leviHC = cartanPoly ∘ leviProj : Z(U(m)) → MvPolynomial zeroIndex ℂ`, injective
  (`leviHC_injective`).

## The Harish-Chandra map of `Z(U(g))`

For `P : Z(U(g)) →ₐ[ℂ] Z(U(m))` with `z - U(j)(P z) ∈ positiveRightIdeal H` for all `z`:

- `hcMap P = leviHC ∘ P`.
- `positiveRightIdeal_le`: `positiveRightIdeal H` lies in the positive right ideal for the
  grading `φ`, since eigenvectors of `ad H` with positive integral eigenvalue are combinations
  of basis vectors of positive grading (`re_wt_reg_pos`).
- `map_positiveWeightRightIdeal_levi`: `U(j)` maps the positive right ideal of `m` into that of
  `g`. `map_comp_incl`: `U(cartanToG) = U(j) ∘ U(incl)`.
- `sub_hcMap_mem`: `z - U(cartanToG)(leviProj (P z))` lies in the positive right ideal of `g`.
- `coeff_hcMap`: the coefficients of `hcMap P z` are the PBW coordinates of `z`, in the order of
  decreasing grading, at the exponents supported on letters of grading zero. The positive right
  ideal has no such coordinates (`positiveWeightRightIdeal_le_positivePBWSpan`), and
  `repr_envelopingMap_embDomain` identifies the coordinates of `U(cartanToG)(a)` with those of
  `a`, which are the coefficients of `cartanPoly a` (`AbelianEnveloping.coeff_polyEquiv_symm`).
- `hcMap_injective`: if `hcMap P z = 0`, then `z` lies in the positive right ideal of `g`, and
  the vanishing theorem with `exists_shiftPart_ne_zero_g` gives `z = 0`.

## Provenance

`hcMap P` is the Harish-Chandra homomorphism of `Z(U(g))` for the Cartan subalgebra and the
positive system given by the regular grading, computed through the parabolic projection: the
transitivity of the projections modulo the positive right ideals. Internal.
