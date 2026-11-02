# Hyperbolic unitary cocharacters and matrix subgroups

All declarations are in `Langlands.GroupScheme.QuasiSplitUnitary`. Let `F` and
`E` be fields with an `F`-algebra structure on `E` and
`IsQuadraticExtension F E`. Fix an `F`-algebra automorphism `c` of `E` and a
finite `F`-basis `b` of `Matrix (Fin 2) (Fin 2) E`. The group `groupScheme b c`
and its matrix coordinates come from the preceding module. The intended unitary
specialization takes the nonidentity quadratic automorphism; the constructions
here also allow the identity automorphism. There is no characteristic
restriction, and every coefficient algebra is an arbitrary commutative
`F`-algebra, with no reducedness assumption.

For a coefficient algebra `R`, put `B = E ⊗[F] R` and write `c_R` for
`scalarConjugation R c`. The declaration `traceZero R c` is the `R`-submodule
of `B` defined as the kernel of the linear map `x ↦ x + c_R(x)`.
`mem_traceZero` states this equation. Thus the parameter space carries both its
additive group and its scalar action. The helper `scaleTraceZero R c t m x`
is the parameter `t^m • x`, for a unit `t : Rˣ` and an integer `m`.

The weights `weights m` are `(m,-m)`. The multiplicative homomorphism
`diagonalUnitary R c m` sends `t` to `diag(t^m,t^(-m))`, using the scalar
algebra map from `R` to `B`. Its values lie in `matrixPoints R c`;
`diagonalUnitary_val` gives their underlying matrices.
`tensorCoefficientMap_algebraMap` and `diagonalUnitary_naturality` show that
this construction commutes with every change of coefficient `F`-algebra.
`diagonalUnitary_neg_one` identifies the weight `-1` value with the inverse of
the weight `1` value.

`matrixCoordinates b c T` is the matrix-valued homomorphism on the points of
`groupScheme b c` over an arbitrary test scheme `T` over `Spec F`. Its
coefficient algebra is `((algΓ (CommRingCat.of F)).obj T).unop`, the global
sections with the `F`-algebra structure induced by the structure morphism of
`T`. `matrixCoordinates_naturality` identifies restriction to `T' → T` with
entrywise change of coefficients.

The natural homomorphisms `weightCocharacterPoints b c m` are transported from
`diagonalUnitary` through `Gm.pointsEquiv` and `pointsEquiv`.
`weightCocharacterPoints_naturality` proves naturality on all test schemes, so
`homOfPoints` gives the actual group-scheme morphism
`weightCocharacter b c m`. The abbreviations `cocharacter b c` and
`inverseCocharacter b c` use weights `1` and `-1`, respectively.
`pointsEquiv_weightCocharacter` specifies their matrices at every point, and
`inverseCocharacter_points` states that their values are mutual inverses.

The helper `ofMatrixSubgroups` pulls any family of subgroups of `GL₂` stable
under coefficient changes back along `matrixCoordinates`. Applying it to the
Library's block subgroups gives the following `SubgroupFunctor`s:

| Declaration | Condition on the matrix of a point |
| --- | --- |
| `upperTriangular b c` | Entry `(1,0)` is zero. |
| `lowerTriangular b c` | Entry `(0,1)` is zero. |
| `diagonal b c` | Both off-diagonal entries are zero. |
| `upperUnipotent b c` | Entry `(1,0)` is zero and both diagonal entries are one. |
| `lowerUnipotent b c` | Entry `(0,1)` is zero and both diagonal entries are one. |

The five `mem_…` lemmas state exactly these entry conditions. They follow by
expanding the two opposite weights in the existing block parabolic, Levi and
unipotent subgroups.

`upperRootMatrix R x` and `lowerRootMatrix R x` are the invertible matrices
`[[1,x],[0,1]]` and `[[1,0],[x,1]]`, with inverses obtained by replacing `x`
with `-x`. The homomorphisms `upperRoot R c` and `lowerRoot R c` restrict them
to trace-zero parameters and take values in `matrixPoints R c`.
`Multiplicative (traceZero R c)` is the standard type synonym expressing the
additive parameter group multiplicatively, so these maps add parameters when
their matrices are multiplied. Membership in the unitary group follows directly
from `x + c_R(x) = 0`.

The homomorphisms `upperRootPoints b c T` and `lowerRootPoints b c T` transport
these root maps to points of the actual group scheme for every `T`.
`pointsEquiv_upperRootPoints` and `pointsEquiv_lowerRootPoints` give the
comparison with the matrix maps. Direct matrix multiplication proves
`diagonalUnitary_upperRoot` and `diagonalUnitary_lowerRoot`, and transport
through the multiplicative point equivalence proves
`cocharacter_upperRootPoints` and `cocharacter_lowerRootPoints`:

```
λ(t) u(x) λ(t)⁻¹ = u(t² x),
λ(t) u⁻(x) λ(t)⁻¹ = u⁻(t⁻² x).
```

The scalar powers on the right are interpreted by `scaleTraceZero`, with `t`
converted to a unit of the global-sections algebra by `Gm.pointsEquiv`.
The calculation uses matrix entries and the unit inverse identities, so it
remains valid in characteristic two and over non-reduced test schemes.

This presentation is derived from the antidiagonal hermitian form described in
the preceding module. For the unitary algebra-involution framework see Milne,
*Algebraic Groups* (2017), Proposition 24.40, Definition 24.42 and Theorem 24.44,
printed pp.523–525. Theorem 24.44 concerns the special unitary group, whereas
the model here retains the full unitary equation. Milne's Example 13.31,
printed pp.264–265, computes the analogous dynamic subgroups for `SL₂`, and
Theorem 13.33 and its proof, printed pp.265–266, describe the general dynamic
decomposition. The explicit unitary root maps and matrix calculations here
are derived content, rather than a quotation of those `SL₂` calculations.
This module supplies the cocharacters, subgroup functors and root maps; the
identifications with `Dynamic.parabolic`, `Dynamic.centralizer` and
`Dynamic.unipotent`, the assertions that the root maps have those full images,
and the Levi decomposition are separate statement and proof units.
