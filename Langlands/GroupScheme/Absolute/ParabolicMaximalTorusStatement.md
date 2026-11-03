# Maximal tori contained in parabolic subgroups: statement

Worker 1270.

`ParabolicMaximalTorusStatement.{u}` asserts that, for every field
`k : Type u`, connected reductive group scheme `G` over `Spec k`, and
parabolic subgroup `i : P ⟶ G`, there are a commutative group scheme `T`
and homomorphisms `j : T.toGrp ⟶ G` and `f : T.toGrp ⟶ P` such that
`IsMaximalTorus j` and `f ≫ i = j`.

All group schemes and homomorphisms are defined over `k`. Maximality is
the published `IsMaximalTorus` in `G`; it includes that `T` is a torus
and that `j` is a closed subgroup. The statement does not require `T`
to be split. It applies in arbitrary characteristic and over imperfect
fields. Parabolicity is the published geometric
`IsParabolicSubgroup`, so it includes smoothness and closedness of `P`.

The source is Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Theorem 25.1, printed p.544
(one-based PDF p.560): the converse proof starts by choosing a maximal
torus in the parabolic. The underlying general results are Theorem
17.82 and Corollary 17.83, printed p.379 (PDF p.395), which give
geometric maximality and a maximal torus defined over the base field.
Theorem 17.10, the paragraph after Definition 17.12, and Theorem
17.16, printed pp.354–356 (PDF pp.370–372), give the geometric
maximal-torus and Borel-containment inputs.
Corollary 17.49, printed p.367 (PDF p.383), states that a smooth
subgroup containing a Borel is connected.

The displayed statement is a **derived formulation** of that
structural input. The parabolic is smooth and affine; after extension
to an algebraic closure it contains a Borel of `G`, and hence is
connected by Corollary 17.49. Choose a maximal torus of the parabolic
defined over `k` using Corollary 17.83. After extension to the
algebraic closure, it is still maximal in the parabolic by Theorem
17.82. The paragraph after Definition 17.12 supplies a maximal torus
of `G` in the contained Borel; it is maximal in the parabolic as well.
Conjugacy of maximal tori inside the connected parabolic (Theorem
17.10), and geometric invariance of maximality, show that the chosen
torus is maximal in `G`. The factorization equation
expresses containment using homomorphisms rather than identified
subgroups. This paragraph explains the source derivation; no part of
it is proved in this file.

This module only defines a proposition. It supplies no proof or
instance of that proposition. In particular it does not identify
parabolic subgroups with dynamic subgroups, construct a splitting
field, or perform cocharacter descent.
