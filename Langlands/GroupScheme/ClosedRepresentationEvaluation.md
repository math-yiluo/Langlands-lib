# Regular functions through a closed matrix representation

Module `Langlands.GroupScheme.ClosedRepresentationEvaluation` (namespace
`Langlands.GroupScheme.MatrixRepresentation`). Internal supporting result: a closed immersion
into a general linear group is surjective on global regular functions, so every regular function is
a polynomial in the matrix entries and the inverse-matrix entries. This is the scheme-theoretic
input used to compare the published regular charts of `G(F_v)` with the matrix entries of a
closed realization.

## Declaration

`exists_polynomial_affinePointEvaluation`. Let `k` be a field, `G` an affine group scheme over
`Spec k`, `ρ : MatrixRepresentation G n` with `IsClosedSubgroup ρ` (its underlying morphism is a
closed immersion), and `b` a global section of `G`. Then there is
`P : MvPolynomial (GeneralLinear.Coordinate n) k` such that for every `k`-algebra `S` and every
affine point `x : G.affinePoints S`,

```text
G.affinePointEvaluation S x b = MvPolynomial.aeval (GeneralLinear.values (ρ.affineMatrix S x)) P,
```

where `GeneralLinear.values g` sends the variable `entry i j` to `g i j` and `inverseEntry i j` to
`g⁻¹ i j`.

## Proof

The map `π : MvPolynomial (Coordinate n) k → Γ(G)` obtained by composing the quotient onto the
general linear coordinate ring, the identification of its spectrum's global sections
(`spectrumCoordinateAlgEquiv`) and the pullback along `ρ` (`affineCoordinatePullback`) is
surjective, because a closed immersion of affine schemes is surjective on global sections
(`IsClosedImmersion.isAffine_surjective_of_isAffine`); this is the construction already used in
`Langlands.GroupScheme.MatrixRepresentationPolynomialGrowth`. Choose `P` with `π P = b`. Evaluating
`ρ`'s pullback at `x` is evaluation at the general linear point `x ≫ ρ`
(`affinePointEvaluation_postcomp`), whose matrix is `ρ.affineMatrix S x`; that point is the
spectrum point classified by this matrix (`affinePointsEquiv_symm_apply`), and evaluation there is
`classify` (`affinePointEvaluation_map_classify`), which sends the class of `P` to
`aeval (values g) P` (`classify_quotient`).
