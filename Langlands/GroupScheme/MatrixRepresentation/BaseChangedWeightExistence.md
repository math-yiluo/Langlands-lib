# Every geometric character occurs in an original finite representation

Internal prerequisite for the orbit classification of
representations of a group of multiplicative type.
`ScalarExtensionCoordinates` supplies the comparison of scalar-extended actual
point matrices.

When the actual character spaces of a finite representation span, an absent
character's coefficient projector is zero. Equivalently, the selected character
functional vanishes on each universal matrix entry.

`tensorCharacterCoefficient χ` is the extension-field linear functional on
`K ⊗[k] O(G)` obtained by evaluating the universal tensor point at the universal
point of the actual base change and selecting the coefficient of `χ`.

Suppose all original finite representations have spanning character spaces after
extension from `k` to `K`. For a character `χ` of the base change, evaluate its
universal tensor unit in the coordinate algebra of the base-changed group and
apply the selected `χ` coefficient. This gives a `K`-linear functional on
`K ⊗[k] O(G)` with value one on that unit. If `χ` occurred in no extended original
representation, the functional would vanish on `1 ⊗ c` for every original
matrix coefficient `c`. The published
`Lie.exists_representation_coefficient_span` says that each original coordinate
lies in the coefficient span of some finite original representation. The
functional would therefore vanish on every pure tensor, hence everywhere, a
contradiction.

Over a separable closure, a group of multiplicative type is diagonalizable by the
published finite-splitting proof. Applying the complete diagonalizable character
decomposition establishes the hypothesis and yields
`exists_weight_baseChange_of_isMultiplicativeType`.

This is a derived coordinate route to the occurrence part of Milne,
*Algebraic Groups* (2017), Theorem 12.30, printed pages 241–242 (PDF pages
257–258), source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
It uses the existing finite coefficient-span theorem in place of explicitly
descending a finite orbit representation. It proves occurrence in a finite
representation, without proving that representation irreducible or
identifying its full set of weights.
