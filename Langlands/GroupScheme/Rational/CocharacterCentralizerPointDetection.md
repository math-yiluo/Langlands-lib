# Rational points detect common-torus cocharacter centralizers

This internal deduction by Worker 561 compares actual cocharacter-centralizer
subgroup functors through their rational-point subgroups. It uses the existing
relative-root subgroup and dynamic-centralizer theorems, with no new
literature assertion.

`RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero` works over
every field. If the character of a root subgroup pairs to zero with a
cocharacter, the cocharacter factors through that character's actual kernel
on every test scheme. A root subgroup point centralizes this full kernel,
so it centralizes the cocharacter. Neither the torus nor its map is required
to be split or monomorphic for this first lemma.

For `root_zero_imp_of_dynamicCentralizer_rationalPoints_le`, the ambient
group is smooth and affine, and the common torus is split. Each actual
relative root has a nonidentity rational point by
`RelativeRoot.exists_rootPoint_actual`. A root annihilated by the first
cocharacter supplies such a point in its centralizer. The displayed
rational-point containment puts that point in the second centralizer.
A positive pairing with the second cocharacter would put it in the second
contracting subgroup, contradicting the trivial intersection of a
centralizer and its contracting subgroup. A negative pairing gives the
same contradiction with the negative cocharacter. Thus the second pairing
is zero.

`dynamicCentralizer_le_of_rationalPoints_le` additionally assumes that the
ambient group is connected. It combines this zero-root implication with
`dynamicCentralizer_le_of_root_zero_imp`, supplying the proved
`dynamicConnected` theorem. Its conclusion is inclusion of the actual
subgroup functors, on every test scheme. Applying it in both directions
proves `dynamicCentralizer_eq_of_rationalPoints_eq`.

`cocharacterCentralizerRationalPointsOrderEmbedding` packages this result
as an order embedding. Its domain is the subtype of actual subgroup
functors that are centralizers of cocharacters of this fixed split torus;
its codomain is the subgroup lattice of the ambient rational-point group.
It sends each functor to its rational-point subgroup. The preceding
equality and inclusion lemmas prove injectivity and reflection of order,
and evaluation itself preserves order. Different cocharacters with the
same full centralizer therefore represent the same domain element.

The direct declaration dependencies are
`RelativeRoot.mem_kernelCentralizer_of_isOrbitExtension`,
`RelativeRoot.mem_kernelCentralizer`, `kernelPointsEquiv`,
`torusCentralizer_gm_eq_dynamicCentralizer`, `eq_gmEndEquiv_zsmul`,
`RelativeRoot.exists_rootPoint_actual`,
`RelativeRoot.subgroup_le_dynamicUnipotent`,
`groupHom_neg_comp_eq_oppositeCocharacter`,
`Dynamic.centralizer_le_precomp`,
`Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent`,
`Dynamic.HasLimit.unique`, `dynamicCentralizer_le_of_root_zero_imp`,
and `dynamicConnected`. Uniqueness of limits applies because an affine
group scheme is separated. The `rationalPoints` notation is the actual
base-test-scheme carrier from `Rational.ParabolicPointConjugation`.

The field universe is arbitrary. These results do not assume reductivity,
maximality of the split torus, infinitude or perfection of the field,
characteristic zero, a reduced root system, or a restriction on test
schemes. The rational points here are those of the dynamic subgroup
functors, which already encode commutation after every refinement; they
are not centralizers computed only in the abstract group of rational
points.

This unit supplies a point-to-functor comparison needed in the rational
corrected-orbit modulus proof. It does not itself prove that modulus
identity, extend the published torus Haar balance to every Levi point,
or prove a rational-character detection theorem.
