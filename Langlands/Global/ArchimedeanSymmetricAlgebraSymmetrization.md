# Actual whole-algebra symmetrization and conjugation

For every field `K : Type u` and every natural rank `n`,
`lieSymmetricAlgebraSymmetrize` is the complex-linear normalized symmetrization
from the actual `LieSymmetricAlgebra K n` to the genuine archimedean universal
enveloping algebra. It specializes `symmetricAlgebraSymmetrize`; its values on
one, scalars, Lie generators and arbitrary generator monomials are recorded.
A monomial of length `d` has image in the genuine enveloping degree piece `d`.

`lieSymmetricAlgebraSymmetrize_conjugation` intertwines the existing actual
whole-symmetric-algebra action `lieSymmetricConjugation` with
`envelopingConjugation`, for every element of `InfiniteAdelicGL K n`. The proof
specializes generic compatible-map naturality, using exactly the published
identity for conjugation of an enveloping generator. Both actions use
`X ↦ g X g⁻¹` on the actual real matrix Lie algebra and its full complex scalar
extension. The theorem imposes no number-field or connected-component condition.

`envelopingCompactInvariants` and `envelopingGroupInvariants` are the actual
fixed subalgebras under the whole standard compact group and the whole
archimedean group, respectively. Their defining equalities are exposed by
membership lemmas. The two invariant symmetrization maps restrict the underlying
linear map to the corresponding existing fixed symmetric subalgebras;
equivariance proves membership. Their coercion formulas are definitional.

This is an internal specialization of the existing whole-algebra construction,
actual matrix adjoint and enveloping conjugation. The invariant restrictions are
linear maps; multiplicativity of symmetrization is not asserted. This unit
proves neither equality of the full-group fixed algebra with the center nor
surjectivity, PBW, central generation, or automorphic differential growth.
