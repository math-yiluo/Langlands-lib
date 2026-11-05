# Rational conjugacy of maximal split tori in solvable groups

Authors: Workers 1356 and 1352.

`Langlands.GroupScheme.solvableMaximalSplitTorusConjugacy` proves exactly
the published
`Langlands.GroupScheme.SolvableMaximalSplitTorusConjugacyStatement.{u}`.
For every field `k : Type u` and every smooth connected affine group scheme
`G` satisfying the existing `IsSolvableGroupScheme G`, two maximal split
torus embeddings are conjugate by an actual `k`-rational point of `G`.
The conclusion includes an actual isomorphism of the source group schemes
and the equation
`i ≫ (G.innerIso g).hom = e.hom ≫ i'`.

The implemented proof first derives affineness of `G.X.left` from its
affine structure morphism. Smoothness supplies local finite type.
Each maximal split torus is a closed torus, so
`exists_maximalTorus_extension_of_finiteType` supplies a maximal torus
containing it, together with the factorization of its embedding.
This is applied to both supplied split tori.

The published theorem `solvableMaximalTorusConjugacy` makes these two
maximal torus overgroups rationally conjugate under the original smooth,
connected, affine and solvable hypotheses. Finally,
`subgroupConjugate_of_conjugate_commutative_overgroups` restricts their
conjugacy to the original maximal split tori. That restriction theorem
uses the largest split subtorus universal property inside a commutative
overgroup and transports the rational point, source isomorphism and
embedding equation back to `G`.

This is an internal composition of the named published results. The
original source and conventions for the split-torus target are documented
in the unchanged `SolvableMaximalSplitTorusStatement` pair. The proof
implements the maximal-torus containment and conjugacy route described
there. It uses the independently proved full maximal-torus conjugacy
theorem, whose imports contain neither maximal-split-torus conjugacy
family.

The theorem has no additional premise and preserves the existing
predicates unchanged. It retains every field in universe `u`, all
characteristics, finite and imperfect fields, and smooth connected
affine solvable groups without a splitting assumption.
