# Elements of `I⁺` with nonzero invariant `D` are regular elliptic

Lean module: `Langlands.Representation.AffineGeneric.Elliptic`, namespace
`Langlands.AffineGeneric`.

Let `F` be a nonarchimedean local field with uniformizer `ϖ`, and `D = coordProd ϖ` the product
of the cyclic coordinates on `I⁺`.

## Declarations

- `val_det_sub_one_eq`: if `γ ∈ I⁺` and `D(γ) ≠ 0`, then `v(det(γ - 1)) = v(ϖ)`. By
  `coordProd_eq`, `(-1)^m ϖ⁻¹ det(γ - 1)` has nonzero residue, so it is a unit of `𝒪`
  (`val_eq_one_of_resOf_ne_zero`).
- `isRegularElliptic_of_coordProd_ne_zero`: if moreover `F` has characteristic zero, then `γ` is
  regular elliptic (`JacquetLanglands.IsRegularElliptic`): its characteristic polynomial is
  separable and irreducible over `F`.
- `isRegularSemisimple_of_coordProd_ne_zero`: in particular `γ` is regular semisimple.

**Proof of regular ellipticity.** Let `Y = γ - 1 ∈ 𝔓` and let `p` be the characteristic
polynomial of `Y` viewed over `𝒪`. The reduction of `Y` is strictly upper triangular, so `p`
reduces to `X^{m+1}` (`Matrix.charpoly_map`, `Matrix.charpoly_of_isUpperTriangular`) and its
non-leading coefficients lie in `𝔭`. Its constant term is `± det Y`. If it lay in `𝔭²`, writing
`𝔭 = (π)` for an irreducible `π` of the discrete valuation ring `𝒪`, one would get
`v(det Y) ≤ v(π)² ≤ v(ϖ)² < v(ϖ)`, contradicting `val_det_sub_one_eq`. So `p` is Eisenstein at
`𝔭` and irreducible over `F` (`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`).
The characteristic polynomial of `γ = Y + 1` is the Taylor shift of that of `Y` by `-1`
(`Matrix.charpoly_sub_scalar`, `taylorEquiv`), hence irreducible, and separable because `F` is
perfect (`PerfectField.separable_of_irreducible`).
