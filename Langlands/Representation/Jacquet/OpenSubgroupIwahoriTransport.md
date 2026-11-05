# Opposite Iwahori bases in an open subgroup

This internal construction transports the published contraction conditions
through the inclusion of an actual open subgroup, and applies the published
compact-coefficient converse. The ambient group and the representation carrier
have independent universes. No reductive geometry is asserted here.

`ambientOpenSubgroup` maps an open subgroup of an open subgroup to the ambient
group by reusing `Langlands.Induction.openSubgroupMap`. The inclusion is open,
so this is again an open subgroup.

An ambient Iwahori contraction at a level contained in an open subgroup H
restricts to H, with each of the three groups replaced by its actual inverse
image under H's inclusion. Factorization lifts because each of its factors
belongs to the original level. The conjugation and exhaustion conditions are
the same equalities under inclusion. For uniform contraction, an open test
subgroup of H has an open ambient image, to which the original condition applies.

An ambient opposite basis for a specified element in H therefore gives an
opposite basis in H. For an open identity neighborhood in H, its ambient image
is open. Choosing the ambient level inside that image ensures it is contained
in H. Its inverse image is compact, with its inclusion image exactly the
original compact level. Both contraction orders restrict for the same element.
Normalization also restricts to the inverse-image subgroups.

Finally, compact smooth-dual coefficients, normalization and an opposite
Iwahori basis for an element whose powers escape compact sets force the actual
Jacquet coinvariant space to be a subsingleton. The proof identifies the top
subgroup with the full group as a topological group. The published coefficient
transport theorem retains the entire smooth algebraic dual, and the existing
compact-restriction converse applies to that top subgroup. No admissibility,
irreducibility or dimension premise is used.
