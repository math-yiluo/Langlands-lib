# Reduction of the rank-one solvable obstruction to Borel subgroups

This module proves a conditional reduction, not
`Langlands.GroupScheme.RankOneSolvableObstructionStatement` without
assumptions. The remaining premise is exactly the opposite-weight exclusion
for every Borel subgroup through the specified torus.

For an affine group scheme locally of finite type over any field,
`not_meets_oppositeWeightSpaces_of_borel` transfers that Borel exclusion to
every smooth connected solvable closed subgroup `i : H ⟶ G` through which
`j : T ⟶ G` factors. This first lemma does not require reductivity,
splitness or maximality of the torus.

The implemented proof uses the published
`BorelExistence.exists_isBorelSubgroup_containing` to obtain a Borel
`b : B ⟶ G` and a homomorphism `a : H ⟶ B` satisfying `a ≫ b = i`.
Composing the original torus factorization with `a` supplies its
factorization through `B`. Each nonzero ambient Lie vector is unchanged;
its dual-number preimage is postcomposed with `a`, using
`Lie.MeetsWeightSpace.of_factorization`. Thus the pair of witnesses for `H`
would be a pair of witnesses for `B`, contradicting the supplied premise.

`rankOneSolvableObstruction_of_borel` assembles this argument with the full
quantifiers of the public statement, at an arbitrary universe `u`.
Connected reductivity supplies ambient affineness and smoothness;
smoothness supplies local finite type. The theorem retains its universal
Borel premise explicitly and adds no restriction on fields or
characteristic. The final unconditional proof must still establish that
premise.

This is an internal formal reduction motivated by Milne, *Algebraic Groups*
(2017), Lemma 21.28, printed p.433 (PDF p.449), and the initial Borel-containment
step in the proof of Proposition 21.29, printed p.434 (PDF p.450).
Milne proves the geometric
lemma using the two Borels of a semisimple-rank-one centralizer (20.20,
printed pp.414–415, PDF pp.430–431) and Borel intersection with that
centralizer (17.72, printed p.376, PDF p.392). Neither geometric assertion is
proved or assumed silently here. Unlike the printed route, this formal
reduction uses the Library's factorization-preserving Borel containment
over the original field. It does not use `RegularCocharacterBorelStatement`
or `ParabolicDynamicStatement`.
