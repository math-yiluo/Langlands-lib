# Connected unipotent subgroups of linearly reductive groups

`HasTrivialConnectedUnipotentSubgroups G` says that every connected closed
unipotent subgroup scheme of `G` has the trivial subgroup functor as its
range. It contains no smoothness or normality restriction.
`hasTrivialConnectedUnipotentSubgroups_of_linearlyReductive` proves this
property for every affine locally finite-type group over a field of nonzero
characteristic satisfying the exact task's finite-coordinate linear-reductivity
condition. No algebraic-closure, perfectness or reducedness assumption is used.

First consider any supplied finite representation of the ambient group whose
restriction to an unipotent subgroup is monic as an actual group-scheme
morphism. Every tangent matrix of that restricted representation is nilpotent
by the published unipotent tangent theorem. The actual restriction law makes
it a tangent matrix of the ambient representation at the image tangent point.
The nilpotent-tangent obstruction for the linearly reductive ambient group
makes it zero. The monic restricted representation is injective on actual
dual-number kernels, and the general-linear tangent coordinate equivalence
then makes the subgroup's entire tangent kernel trivial.

For an arbitrary closed unipotent subgroup, the published closed linear
embedding theorem supplies such a faithful finite representation of the
ambient affine group. Closed immersions and their composites are monic,
so the preceding argument applies. This proves
`subsingleton_lieKernel_closed_unipotent_of_linearlyReductive`, whether
or not the subgroup is connected, smooth or normal.

If the subgroup is connected, it inherits affineness and local finite type
from its closed immersion into the ambient group. The published zero-tangent
triviality theorem then makes its structure morphism an isomorphism to
`Spec k`. Monicity of that structure morphism shows that every point on
every scheme test is the identity. Consequently the closed subgroup's
range is the trivial subgroup functor, including on nonreduced tests.
The module records each of these actual-scheme and pointwise conclusions.

This is an internal consequence of the symmetric-power infinitesimal
obstruction used by the source, combined with the existing Library closed
linear embedding, unipotent tangent and zero-tangent results. The source
uses absence of an alpha_p subgroup in its connected-group classification;
the present corollary supplies actual triviality of every connected closed
unipotent subgroup without introducing a separate alpha_p model. It does
not assert linear-reductivity inheritance by subgroups or prove the remaining
connected multiplicative-type classification in Nagata's theorem.

Source context: M. Demazure and P. Gabriel, *Groupes algebriques*, Tome I (1970), IV, section 3, proof of Theorem 3.6 and the start of Lemma 3.7, printed p.510 (PDF p.540). Registered source `provided-fbc22c29e33197d3b9f2e242cdac44714e2e1a2f5faa337e9ebc1d657ad1d6fe`, SHA-256 `fbb2f907cc281afba245917449bae4bca1175c35215539c700575c517069e127`.
