# Split binary generation on specified actual models and factor images

This internal consequence applies to an actual group scheme `A` supplied with
an isomorphism over the ground field to the existing split binary special
linear group scheme. The field has arbitrary characteristic and universe `u`.
The isomorphism is an explicit premise; neither existence nor classification
of any forms is claimed.

The proved split binary radical-generation theorem and the proved invariance
of `parabolicElementarySubgroup = top` under actual ground-field isomorphisms
give `parabolicElementarySubgroup_eq_top_of_iso`. The existing quotient
criterion then makes the actual parabolic Whitehead quotient a subsingleton.
The elementary subgroup's universal property proves that any subgroup of
`A(k)` containing every actual rational parabolic radical image is the whole
point group, even without a normality premise.

For a homomorphism `a : A -> G` and any subgroup `K` of the actual ambient
rational-point group, `rationalPoints_range_le_of_iso` assumes that each actual
parabolic radical of `A` has its image under `a` inside `K`. The proof takes
the preimage of `K` under the actual rational-point map, checks its radical
containment by composition of scheme morphisms, and applies the generation
result. The preimage is the full point group, so the entire image of `A(k)`
lies in `K`. `rationalPointsToSubgroupOfIso` is the actual map with its
codomain restricted using exactly this proved containment; its underlying
ambient value is the original point map.

The derivation uses only the imported actual split binary generation,
isomorphism transport, and universal property of subgroup generation. It
requires no local-field, simple-connectedness, or ambient-normality premise.
It retains the specified ground-field isomorphism and all actual radical-image
containments as hypotheses. Constructing such isomorphisms for appropriate
factors and proving the containments in a general group remain separate
obligations, as do nonsplit rank-one cases and the unrestricted local
Kneser–Tits statement.
