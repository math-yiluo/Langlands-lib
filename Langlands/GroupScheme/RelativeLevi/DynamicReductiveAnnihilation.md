# Surjections from dynamic parabolics kill their contracting subgroup

This is an internal prerequisite for the relative parabolic reductive
quotient. It proves `DynamicReductiveAnnihilationStatement` in every universe.
It does not prove the unchanged `RelativeParabolicReductiveQuotientStatement`:
local dynamic presentations of arbitrary relative parabolics, identification of
their radicals, and quotient construction and descent remain separate steps.

For every scheme `S`, reductive group `G/S`, and cocharacter `χ`, suppose
`i : P → G` represents `P_G(χ)` and `r : U → P` has composite `r ≫ i`
representing `U_G(χ)`. Then every homomorphism `f : P → H` to a reductive group
scheme `H/S` that is surjective on underlying schemes satisfies `r ≫ f = 0`.
Representability and the conclusion concern all scheme tests and actual
morphisms over `S`. There is no reduced-base, affine-base or field hypothesis,
and surjectivity of `f` is not assumed to imply flatness.

The helper `Dynamic.annihilates_contracting_subgroup` only needs the ambient
`G/S` to be smooth and affine, rather than reductive. The final theorem
`dynamicReductiveAnnihilation` supplies these properties from ambient
reductivity and proves the displayed Prop-valued statement.

The proof proceeds as follows.

1. `Dynamic.parabolic_eq_top_of_surjective_range` starts with a surjective
   homomorphism whose range lies in `P_H(ψ)`, for a smooth affine group `H/S`.
   Published arbitrary-base dynamic representability supplies a closed
   representative `j : A → H`, and dynamic smoothness makes `A/S` smooth.
   Membership of the universal point of the source factors the homomorphism
   through `j`, making `j` surjective. Every residue-field base change is then
   a surjective closed immersion into a smooth, hence reduced, scheme and is
   an isomorphism. The fibrewise open-immersion criterion and fibrewise point
   lifting make `j` an isomorphism over `S`. Its all-test range is therefore
   the whole group.
2. `Dynamic.centralizer_eq_top_of_parabolic_eq_top` assumes `H/S` reductive
   and `P_H(ψ)` full. On every residue-field fibre, the group is connected
   reductive, hence pseudo-reductive, and the published
   `pseudoReductiveCentralCocharacter` makes `Z_H(ψ)` full there. A closed
   centralizer representative is smooth over `S`; after base change it has
   full all-test range and is monic, so it is an isomorphism. The same
   fibrewise isomorphism argument makes the original representative an
   isomorphism, proving full centrality over the base.
3. `Dynamic.unipotent_eq_one_of_parabolic_eq_top` uses uniqueness of dynamic
   limits in the separated reductive group: a centralizing point has itself
   as limit, so an identity-limit point is the identity.
   `Dynamic.comp_eq_one_of_full_parabolic` applies this to `χ ≫ f`.
   Functoriality carries the full source parabolic into the target parabolic
   and contracting points into the target contracting subgroup. Step 1 makes
   the target parabolic full, and steps 2 and 3 kill each such point.
4. For the represented dynamic parabolic, the cocharacter lifts to `P` by
   `cocharacterToParabolic`. Uniqueness of representatives transports the
   closedness of a chosen representative to `i`. The published closed-subgroup
   comparison shows the lifted cocharacter has full dynamic parabolic and
   that `r` is contracting. Step 3 applied to the universal point of `U`
   proves the actual map `r ≫ f` is zero.

The private residue-field isomorphism helper follows the implementation in
`Rational/LocalRootProducts.lean`, using the published fibrewise open-immersion
criterion. Its source is flat and locally of finite presentation and its target
is locally of finite type; smoothness supplies these hypotheses at both uses.
The other private helpers express that an isomorphism has full range and that
a monomorphism with full all-test range has an inverse, obtained by evaluating
range membership at the identity point of the target.

This module is derived entirely from the named published Library results. It is
not a transcription of an additional external-source assertion. In particular,
it does not infer equality of morphisms from equality on geometric fibres:
smooth dynamic representatives and the fibrewise morphism criterion supply
the necessary control over the entire base scheme.
