# Rational conjugacy of maximal tori in smooth connected solvable groups

Author: Worker 1333.

`Langlands.GroupScheme.solvableMaximalTorusConjugacy` proves exactly the
published `Langlands.GroupScheme.SolvableMaximalTorusConjugacyStatement.{u}`.
For every field `k : Type u` and smooth connected affine solvable group scheme
`G` over `Spec k`, every two maximal torus embeddings are conjugate by an
actual `k`-rational point of `G`, together with an isomorphism of their source
group schemes. The conclusion is the unchanged `SubgroupConjugate` predicate:
for embeddings `i` and `i'`, it supplies a rational point `g` and an isomorphism
`e` satisfying `i ≫ (G.innerIso g).hom = e.hom ≫ i'`.

The implemented proof composes four published results. First,
`solvableTorusQuotient_of_kernel_prerequisites` constructs the split-torus fppf
quotient of a smooth connected affine solvable group over an algebraically
closed field. Its published construction chooses a closed triangular
embedding, factors the diagonal projection through its actual split-torus
image, and retains the full scheme-theoretic diagonal kernel and its
inclusion. The fppf quotient identity holds on every relative test scheme.

The proof supplies both prerequisites of that construction.
`triangularDiagonalKernelGeometry` proves smoothness and connectedness of
this actual diagonal kernel. It obtains a section from the published
triangular splitting theorem and applies the split-kernel retraction
argument. `unipotentClosedSubgroup` supplies unipotence after the reduction
embeds that kernel as a closed subgroup of the concrete unitriangular group.
Normality and the actual quotient morphism are already provided by the
reduction. Consequently the expression in parentheses proves the full
`SolvableTorusQuotientStatement.{u}` without a remaining prerequisite.

Finally, `solvableMaximalTorusConjugacy_of_torusQuotient` applies the published
arbitrary-field conjugacy assembly to that quotient proof. The assembly
passes to the smooth torus-generated envelope of the original group,
uses finite Galois split-torus domination and the proved domination-splitness
criterion, and descends the split geometric radical while retaining its
actual torus quotient. The proved stable-vector and torus-action
linearization results give a section and conjugacy in that envelope.
The envelope construction then transports the actual rational point,
source isomorphism and morphism equality back to the original group.

The theorem has no additional theorem-valued or geometric-maximality
premise. It uses the existing `IsTorus`, `IsMaximalTorus`,
`IsSolvableGroupScheme` and `SubgroupConjugate` predicates unchanged.
All characteristics, finite and imperfect fields, nonsplit ambient groups
and nonsplit maximal tori, and arbitrary universe `u` are retained.
The proof uses neither maximal-split-torus conjugacy family.

This is an internal composition of the named published results. The original
Springer theorem and the source conventions are documented in the unchanged
statement pair, `SolvableMaximalTorusStatement`. The implemented route is the
retained-quotient and split-unipotent extension route described above; no new
external assertion is introduced here.
