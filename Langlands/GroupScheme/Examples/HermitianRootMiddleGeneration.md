# Elementary lifts of anisotropic Hermitian middle isometries

This internal continuation of `HermitianRootReflectionAction` proves that
each middle isometry has an actual elementary Levi lift. The coefficient
field and finite middle-index universes are independent; all
characteristics and the empty index are allowed.

`PreservesMiddle H T` states the standard-column pairing equations

    H.pairing (column i of T) (column j of T)
      = if i=j then H.weight i else 0.

This definition does not assert invertibility independently. The lift theorem
below realizes each such middle matrix inside an actual invertible Levi
matrix under the stated anisotropy and trace-zero assumptions.

The helper identities `leviMatrix_one` and `leviMatrix_mul` identify the
identity Levi matrix and multiplication of two Levi matrices:

    leviMatrix a S * leviMatrix b T = leviMatrix (a*b) (S*T).

They follow by block-entry calculations and multiplicativity of conjugation
and field inversion, including when either scalar is zero.

`preservesMiddle_of_levi` derives column pairing preservation from
preservation of the full hyperbolic Hermitian form. Its proof applies the
existing form-preservation entry identity to the reversed pair of middle
indices and cancels the minus sign in the middle Gram block.
`preservesMiddle_of_elementary_levi` applies the established containment of
the elementary subgroup in the special unitary subgroup to obtain this
hypothesis for an actual elementary Levi element.

`exists_elementary_levi_middle` assumes `H.IsAnisotropic`, a scalar
`s≠0` with `s+bar(s)=0`, and `PreservesMiddle H T`. It proves

    ∃ g ∈ elementarySubgroup H, ∃ a≠0, g = leviMatrix a T,

where `g` is an actual general linear group element and the final equality
is of underlying matrices. The proof uses induction over finite sets of
matched columns. Initially it uses the identity. At an insertion, the
current and desired columns have equal norms by their column-pairing
equations. The existing single-vector matching theorem supplies an
elementary Levi reflection taking the current column to the desired one.
Each previously matched column is perpendicular to their difference,
because its pairings with the two columns are equal. Thus the reflection
fixes it. Multiplication of the actual elementary elements and the Levi
matrix product identity extend the partial match, with a nonzero scalar
product. At the full index set, equality of all columns gives the requested
middle matrix.

The theorem leaves its nonzero hyperbolic scalar unspecified. Adjustment to
a prescribed determinant-one Levi element, generation of the full
hyperbolic unitary group, group-scheme comparisons and the unrestricted
local Kneser–Tits theorem remain separate obligations.
