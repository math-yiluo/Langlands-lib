# Actual conjugate subgroup inclusions and overlap invariance

Worker 655, Task 6339.

This is an internal construction from published group-scheme base change,
inner automorphisms, normalizers, and actual Čech comparison isomorphisms.
It generalizes the subgroup-independent part of
`MaximalTorusParameterExistence.overlap_range_eq` from torus inclusions to
arbitrary group-scheme homomorphisms. It asserts no new representability
or effective descent theorem.

For an arbitrary scheme morphism `b : S' ⟶ S`, an actual homomorphism
`i : H ⟶ G`, and a base point `g` of the actual pullback `G_S'`,
`SubgroupFunctor.conjugatePullback b i g` is the pullback of `i` followed
by the actual inner automorphism defined by `g`. Its source is the actual
pullback of `H`. Closedness of `i` implies closedness of this inclusion,
and smoothness of `H/S` implies smoothness of its pulled-back source.
The construction itself requires neither property.

`mem_range_conjugatePullback_iff` characterizes its points on every test
scheme `V/S'`. Project both the test point and the constant conjugator to
the original group over `S`; membership is exactly that their inverse
conjugation belongs to `range i`. In particular, the equality here retains
all scheme tests, including nonreduced ones.

`range_conjugatePullback_eq_of_normalizer` says that two supplied
conjugators give identical subgroup functors if their quotient, projected
back to `G`, belongs to the full normalizer of `range i`. The normalizer
tests all refinements of the base test scheme. The proof restricts this
normalizing point to each test and invokes the published elementary
conjugate-membership equivalence. No torus, field, smoothness, closedness,
or reductivity hypothesis enters this argument.

`conjugatePullback_overlap_range_eq` starts with an actual parameter map
`q : G.X ⟶ Q` such that equal parameters have differences in that full
normalizer. A point of the pulled-back group is supplied whose image under
`q` lies over a fixed ground parameter `x : S ⟶ Q.left`. The conclusion
is literal equality of the subgroup functors of the two actual Čech
pullbacks of its conjugate inclusion. The first pullback is transported
through the published canonical ambient overlap isomorphism.

The implemented overlap proof compares the original-group points using
the identity isomorphism between the two underlying test schemes over
`S`. The canonical overlap identifies the ambient test points. The two
conjugators have the same parameter by the supplied equation and the
pullback condition; the normalizer hypothesis then makes membership in
their conjugate subgroups equivalent. This follows the already published
torus overlap proof, with its unused torus restriction removed.

These results supply an invariant actual inclusion for the local
quotient-chart construction in the parabolic-scheme task. They neither
descend that inclusion nor prove it parabolic, construct a universal
family, classify parabolics, or prove the host representability theorem.
