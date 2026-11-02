# Character-normalized centralizer valuations and dominant sets

This is a definition unit for the corrected Cartan targets. It uses actual group
schemes and their algebraic characters. To use the names as centralizer objects,
`i : S → G` must be the chosen maximal split torus, `j : Z → G` must represent
`torusCentralizer i`, and `s : S → Z` must satisfy `s ≫ j = i`. Those conditions
are imposed by the companion comparison statement and the Cartan statements;
the elementary transport construction works for any such homomorphism `s`.

The sources are Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
§2.6(d), especially (2.6.4), and §5.2, equation (5.2.1), printed pp. 103 and
187 (PDF 134 and 218), read with the authors' *Corrections and additions*,
1 November 2024, PDF 24–25 and 30. In particular the corrected convention is
`χ(ω_Z(z)) = ord_F(χ(z))`, with positive order, and the dominant inequalities
are `α(ω_Z(z)) ≥ 0`. The reversed inequality in corrected (5.2.2) has the same
nonnegative sign. The implementation composes the already published positive
`rationalCharacterValuation`/`rationalNormLogarithm` with the inverse of actual
character restriction followed by evaluation. It uses the residue-normalized
field order, valid in mixed and equal characteristic.

`characterRestriction s` is actual pullback of characters. `restrictionEvaluation
s` takes a vector in the actual real cocharacter space `V(S)` to its evaluations
on those restricted characters. Its bijectivity is an **explicit comparison
hypothesis**, not an invented group or an assumed Cartan decomposition. The
companion `CentralizerValuationComparisonStatement` asks for that comparison on
an actual represented centralizer of a maximal split torus in every connected
reductive local group. No general existence result is proved here.

`centralizerValuation s h` is the resulting homomorphism on the actual `Z(F)`.
The two short intrinsic proofs use the inverse linear equivalence and the
published equality of the norm logarithm with positive integer order. They prove
its character normalization and uniqueness, and contain no building argument.
`centralizerValuationImage` is its actual range. No assertion identifies that
range with the full integral cocharacter lattice or supplies rank, index or
discreteness. `dominantCentralizer` and `dominantValuationImage` use the actual
positive relative roots `positiveRelativeRoots i ν`. The Cartan targets require
`ν` to be generic, and impose the represented-centralizer and maximal-split
hypotheses explicitly. A choice of chamber is not a choice of affine origin.

This unit defines neither `Z(F)^0` nor the geometric parahoric `P_x` or maximal
compact `K_0`. In the subsequent targets the dominant quotient by `Z(F)^0` and
the dominant valuation image indexing the `K_0` decomposition are distinct.
