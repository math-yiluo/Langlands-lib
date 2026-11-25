# Proof: reduction of connected-group unirationality

`Langlands.GroupScheme.connectedGroupUnirationalityReduction` has exactly the
published type `ConnectedGroupUnirationalityReductionStatement.{u}`. It proves
the implication from the torus and split-unipotent affine-space statements
to the full connected-group unirationality statement, in every universe.
The premises remain explicit; this is separate from the unconditional proof.

An ordinary scheme section of a quotient with its full represented kernel
gives a surjective map from kernel times quotient to the group. The proof
factors `g ↦ g σ(q(g))⁻¹` through the kernel and constructs a right inverse
of multiplication. This step uses scheme morphisms, rather than requiring
the section to be a group homomorphism.

For a smooth connected affine group over a perfect field, the ground-field
unipotent radical is split, and its quotient is pseudo-reductive and hence
reductive. The split-affine-space premise makes the radical unirational.
Split-unipotent affine torsor vanishing supplies an ordinary section over
the affine quotient. The published product unirationality theorem and the
surjective multiplication map then make the original group unirational
whenever the reductive quotient is unirational.

Over an infinite field, torus domination and the torus premise make every
connected reductive group unirational. Over a finite field, the group is
quasi-split. A maximal split torus whose centralizer is a torus admits a
cocharacter with that same centralizer. The associated open three-factor
cell has split-unipotent outer factors and this torus as its middle factor.
The two premises and binary product unirationality treat the cell. Its
identity sections ensure nonemptiness, and the ambient smooth connected
group is irreducible, so the open immersion has dense image. Transport of
unirationality completes this field case. The final theorem combines
finite and infinite fields and then the perfect-field radical argument.

This is derived content for the Library. The quotient route is motivated
by Milne, *Algebraic Groups* (2017), Remark 17.94(a), printed p.382, and
the conclusion is Theorem 17.93, printed p.382 (registered source
`milne-2017-algebraic-groups`). The registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to these
items. The implemented proof uses the Library quotient, open-cell, torus
domination, torsor section, and product theorems, rather than the Cartan
route in Milne's proof of 17.93.
