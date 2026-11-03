# Closed subgroup descent for maximal split torus conjugacy

This module records an unproved structural descent proposition and proves a
conditional assembly theorem. It does not prove the general smooth-group
conjugacy theorem: both the solvable conjugacy result and the structural
descent proposition remain explicit premises of the assembly theorem.

`SplitToriFactorThrough j` says that every split subtorus of the ambient
group factors through one given homomorphism `j : H ⟶ G`, with an actual
homomorphism of group schemes over the field. `SplitToriConjugateInto j`
says that every split subtorus admits such a factorization after conjugation
by an actual rational point of `G`. Its equation is
`f ≫ j = i ≫ (G.innerIso g).hom`, on schemes over the base and therefore on
all test schemes. The point and factorization may depend on the torus.

`SmoothMaximalSplitTorusDescentStatement` quantifies over every field in
universe `u` and every smooth connected affine group scheme `G` over that
field. It states that at least one of the following holds:

- There is one smooth connected affine solvable closed subgroup `H ⟶ G`
  through which every split subtorus of `G` factors. This subgroup may be
  all of `G`.
- There is one proper smooth connected affine closed subgroup `H ⟶ G`
  into which every split subtorus can be rationally conjugated. Properness
  means that its inclusion is not an isomorphism.

Both branches use the published `IsSplitSubtorus`, `IsClosedSubgroup` and
`innerIso` definitions; solvability is the published `IsSolvableGroupScheme`.
There is no perfectness, infinitude, reductivity or characteristic restriction.
The same subgroup must serve every split subtorus within the chosen branch.

This is derived content from the proof of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Theorem C.2.3, printed
pp.593–594 (PDF pp.619–620), source ID
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
In the branch with no proper pseudo-parabolic subgroup, the source takes the
preimage of the maximal central split torus in the quotient by the
unipotent radical; it is solvable and contains every split torus. In the
other branch, Lemma C.2.2 conjugates each split torus into a chosen proper
pseudo-parabolic subgroup. The source's point can be inverted to match
`innerIso`'s `g x g⁻¹` convention. This proposition retains just those two
consequences, without installing them as proved facts. Radical and quotient
constructions, the solvable envelope, pseudo-parabolic geometry, the split
solvable bridge and rational containment all remain proof obligations.

`smoothMaximalSplitTorusConjugacy_of_solvable_of_descent` implements the
assembly using `smoothAffineGroup_closedSubgroup_induction`. Its induction
property is conjugacy conditional on connectedness. In the first branch,
the separate solvable conjugacy premise applies to `H`, and maximal split
tori of `G` remain maximal in `H` through their factorizations. In the
second branch, the induction hypothesis applies to the proper subgroup,
and the closed-overgroup conjugacy reduction transports its result back
to `G`. This gives exactly the conclusion of the published
`SmoothMaximalSplitTorusConjugacyStatement`, conditional on the two stated
premises. The support induction replaces the source's dimension induction.

Worker 1305 proposed the support route and coordinated the geometric
branches; Worker 1295 implemented this statement and conditional assembly.
