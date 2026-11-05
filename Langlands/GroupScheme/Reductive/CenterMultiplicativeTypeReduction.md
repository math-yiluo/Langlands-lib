# Full-center multiplicative type from maximal-torus self-centralization

Author: Worker 1232.

`CenterMultiplicativeTypeCentralizerReductionStatement.{u}` is the implication
from the existing `AlgClosedMaximalTorusCentralizerStatement.{u}` to
`CenterMultiplicativeTypeStatement.{u}`. The theorem
`centerMultiplicativeTypeCentralizerReduction` proves this implication.

Given a connected reductive group and an actual representative of its full
center over an arbitrary field `k`, pass to `AlgebraicClosure k`. The
published geometric reductivity and center base-change results preserve the
two hypotheses. The existing conditional full-center containment theorem
then supplies a closed split torus containing that center on every test
scheme. Its representing inclusion gives an actual factorization of the
center inclusion through the torus; the factor map is closed because its
composite is closed.

The helper `exists_diagonalizableIso_of_isClosedSubgroup_splitTorus` now gives
an actual diagonalizable presentation of the base-changed full center.
That presentation is precisely the witness required by `IsMultiplicativeType`
over the original field, with splitting extension `AlgebraicClosure k`.
The finitely generated character group retains its torsion.

The provenance is this internal derivation from the published center
base-change, algebraic-closure reductivity, conditional maximal-torus
containment, and diagonalizable closed-subgroup results. The implemented
proof does not assume that the full center is smooth or connected and does
not pass to its largest torus or reduced subgroup.

The maximal-torus self-centralization input remains an explicit hypothesis.
This result does not prove it, establish the unconditional
`CenterMultiplicativeTypeStatement`, construct the full-center quotient,
or establish its rational-point compactness.
