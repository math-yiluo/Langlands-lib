# Dynamic subgroups of the quasi-split unitary group: statement

`Langlands.GroupScheme.QuasiSplitUnitary.DynamicStatement` is a proposition
definition, the target for a separate proof unit. It quantifies over fields
`F` and `E`, an `F`-algebra structure and `IsQuadraticExtension F E`, a finite
`F`-basis `b` of `Matrix (Fin 2) (Fin 2) E`, and a nonidentity automorphism
`c : E ≃ₐ[F] E`. It imposes no characteristic restriction.

Put `G = groupScheme b c`, `λ = cocharacter b c` and
`λ' = inverseCocharacter b c`. The proposition asserts the following equalities
of subgroup functors:

| Dynamic subgroup | Matrix-entry subgroup |
| --- | --- |
| `Dynamic.parabolic λ` | `upperTriangular b c` |
| `Dynamic.centralizer λ` | `diagonal b c` |
| `Dynamic.unipotent λ` | `upperUnipotent b c` |
| `Dynamic.parabolic λ'` | `lowerTriangular b c` |
| `Dynamic.centralizer λ'` | `diagonal b c` |
| `Dynamic.unipotent λ'` | `lowerUnipotent b c` |

Here the indices are `0,1`: upper triangular means entry `(1,0)` is zero;
lower triangular means entry `(0,1)` is zero; diagonal means both such entries
are zero. The two unipotent conditions additionally set both diagonal entries
equal to one. These subgroup functors were constructed in
`QuasiSplitUnitaryDynamic`.

The final conjunct quantifies over every test scheme `T` over `Spec F`. It
identifies the subgroup of upper unipotent points with the range of
`upperRootPoints b c T`, and the lower one with the range of
`lowerRootPoints b c T`. The root parameters are the additive group of
`x ∈ E ⊗[F] R` with `x + c_R(x) = 0`, where `R` is the global-sections
`F`-algebra of `T`; `Multiplicative` expresses that additive group in
multiplicative notation. The upper and lower matrices are respectively
`[[1,x],[0,1]]` and `[[1,0],[x,1]]`.

The assertions concern all test schemes, including non-reduced schemes.
`Dynamic.parabolic` is defined by extension of a conjugation orbit across zero
in the affine line; `Dynamic.centralizer` requires that orbit to be constant;
`Dynamic.unipotent` requires an extension whose value at zero is the identity.
The equalities therefore refer to the actual dynamic subgroup functors of `G`.

The source framework is Milne, *Algebraic Groups* (2017), Example 13.31 and
Theorem 13.33 with its proof, printed pp.264–266. The example computes the
analogous subgroups for `SL₂`; the explicit full-unitary identifications and
the root-image assertions here are derived from the antidiagonal hermitian
presentation and are separate proof obligations. For that unitary
algebra-involution framework, see Milne, Proposition 24.40, Definition 24.42
and Theorem 24.44, printed pp.523–525. The last theorem concerns special
unitary groups; the group scheme here is the Library's full unitary model.
This module states the proposition and does not prove it.
