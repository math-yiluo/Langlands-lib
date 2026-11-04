# The full-centre quotient of a connected reductive group is connected reductive

Authors: Worker 1499 and Worker 1404.

This module proves the published Library statement
`Langlands.GroupScheme.CenterQuotientReductiveStatement` (module
`Langlands.GroupScheme.Adjoint.CenterQuotientStatement`).

## `centerQuotientReductive`

`theorem Langlands.GroupScheme.centerQuotientReductive :
CenterQuotientReductiveStatement.{u}`.

For every universe `u`, every field `k : Type u` and every homomorphism
`q : G ⟶ Q` of group schemes over `Spec k`, if `G` is connected reductive
(`IsConnectedReductive G`), `Q.X.hom` is affine and locally of finite type, and
`RelativeRoot.IsFppfQuotient (center G) q` holds (`q` is flat, surjective and
locally of finite presentation, and its actual kernel has range the full
scheme-theoretic centre of `G`), then `Q` is connected reductive. There are no
further hypotheses: no finiteness of `q`, no smoothness or reducedness of the
centre, and no perfectness of `k`.

## Proof

The proof is the composite of two helper modules.

1. `centerQuotientReductive_of_geometricCore` (module
   `CenterQuotientReduction`, by Worker 1404) reduces the statement to
   `CenterQuotientGeometricCoreStatement`: over an algebraically closed field,
   the target of an fppf quotient of a smooth connected affine group with
   trivial unipotent radical by its full centre, with affine target locally of
   finite type, has trivial unipotent radical. The other fields of
   `IsConnectedReductive Q` (smoothness, affineness, connectedness) are proved
   there directly, and the core is applied after base change to
   `AlgebraicClosure k`.
2. `CenterQuotient.hasTrivialUnipotentRadical_of_isFppfQuotient_center`
   (module `CenterQuotientCore`, by Worker 1499) proves the core statement.
   Its proof uses the helper modules `CenterQuotientLinearAlgebra`,
   `CenterQuotientConjugation`, `CenterQuotientCommutator` and
   `CenterQuotientEnvelope`.

The proof term applies the first to the second.

## Helper modules

All in `Langlands/GroupScheme/Adjoint/`, each with its own Markdown file:

- `CenterQuotientLinearAlgebra`: block polynomials, commuting idempotents, and
  the nilpotence criterion for commuting matrices with equal characteristic
  polynomial.
- `CenterQuotientConjugation`: in a connected group, if every conjugate of a
  rational point `h` commutes with `h` in a matrix representation, the
  commutators of `h` act unipotently.
- `CenterQuotientCommutator`: central unipotent images in a group with trivial
  unipotent radical are trivial, and rational points of `G` over central
  points of a unipotent subgroup of the quotient commute.
- `CenterQuotientEnvelope`: closed normal subgroups with commuting rational
  points have central rational points.
- `CenterQuotientCore`: the geometric core.
- `CenterQuotientReduction`: the reduction to algebraically closed fields.
