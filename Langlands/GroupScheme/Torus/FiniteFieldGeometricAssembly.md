# Geometric maximal-torus data from explicit geometric conjugacy

This internal construction combines previously implemented existence, Lang,
Frobenius transport, and descent interfaces. Maximal-torus conjugacy is an
explicit premise throughout. This module does not prove conjugacy or the
unconditional finite-field existence statement.

`GeometricMaximalTorusData k K G` retains an actual commutative group scheme
over `k`, its homomorphism into `G`, maximality of that inclusion over `k`,
and maximality of the same inclusion after the specified actual base change
to `K`. Both fields and the group schemes have an arbitrary common universe
`u`. The record itself requires no finiteness or smoothness assumptions.

For a finite field with a chosen `Fintype`, an algebraic algebraically closed
extension `Ω/k`, and a smooth connected affine group `G`,
`exists_geometricMaximalTorus_of_conjugacy` assumes
`MaximalToriAreConjugate G_Ω` and constructs the two maximality witnesses.
Its proof proceeds as follows.

1. Apply the independent maximal-torus existence theorem to the smooth affine
   group `G_Ω` to obtain an actual maximal torus inclusion `i`.
2. Pull `i` back along the Frobenius field automorphism. The independent
   field-isomorphism maximality theorem and the canonical ambient descent
   isomorphism prove maximality of this transformed inclusion. This uses
   inverse pullback and maximality reflection, with no use of general forward
   maximality preservation.
3. Apply the explicit conjugacy premise to the transformed inclusion and `i`.
   The Lang construction `frobeniusStableConjugate` then supplies a conjugate
   of `i` with Frobenius-invariant range on every test scheme. Ambient
   isomorphism transport preserves maximality.
4. Split the torus over `Ω` using the proved pure-coalgebra group-like
   spanning theorem and its separably closed splitting adapter.
5. Apply geometric Frobenius descent. The recovery equation certifies
   maximality of the actual descended inclusion after extension to `Ω`;
   independent reflection supplies maximality over `k`.

`geometricMaximalTorusDataOfConjugacy` chooses and retains the resulting actual
data. It has the same finite-field, extension, geometric, and explicit
conjugacy hypotheses as the preceding theorem.

`finiteFieldGeometricMaximalTorus_of_maximalTorusConjugacy` takes the published
`MaximalTorusConjugacyStatement.{u}` as an explicit argument and concludes the
exact published `FiniteFieldGeometricMaximalTorusStatement.{u}`. It supplies a
local enumeration from `Finite k`, uses the actual `AlgebraicClosure k`,
and obtains geometric connectedness from the proved connected-group base
change theorem. The commutative group-scheme isomorphism in the supplied
conjugacy statement is converted to the underlying group-scheme isomorphism,
retaining the same point and conjugacy equation.

There is no restriction on characteristic, and no reductivity or splitness
premise on `G`. The target statement and its imports are preserved. The proof
route avoids the no-torus/unipotence theorem and general maximal-torus
base-change preservation. The remaining unconditional input is the separately
owned maximal-torus conjugacy theorem. The construction is an internal
composition of the cited Lean interfaces, rather than a claim to have proved
that structural input.
