# Original number-field projective Weil adelic comparison

This derived construction supplies the generic-fiber and spread-topology
assembly for the number-field case of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 4.2, printed
pp.9–10. Registered source: `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The proof uses the existing original integral-model comparison, its actual
generic-fiber isomorphisms and the proved independence of spread topology.

Let K → L be the specified extension of number fields, all in an arbitrary
common universe. Let X be an actual scheme with a specified immersion
j : X → P^n_L. Its structure over L is the composite with the projective
structure morphism, denoted `originalScheme`. Let S and T be arbitrary
finite sets of lower and upper finite places, respectively. Take
`M : NumberFieldExtensionProjectiveModelData K L S T X n j`.
This is actual constructed arithmetic and geometric data: its exceptional
set E contains S, its full upper preimage E' contains T, and its upper
model Y over B = O(L,E') has the specified generic fiber X and the
specified projective immersion. The published constructor
`numberFieldExtensionProjectiveModel` supplies M whenever X is
quasi-compact. Thus this parameter does not assume an adelic comparison.
All infinite factors are present in every adelic ring and every level.

Put A = O(K,E). The definition `lowerModel` is the actual integral Weil
scheme `affineChartWeilRestriction A B Y`. The definitions
`lowerGenericFiberIso` and `upperGenericFiberIso` identify its actual
generic fiber with `affineChartWeilRestriction K L (originalScheme L X n j)`
and the actual generic fiber of Y with the originally specified X.
The lower isomorphism is the previously proved
`numberFieldProjectiveModelWeilGenericFiberIso`; the upper isomorphism
is the one constructed in M's geometric model data. These identifications
use the original integer-ring inclusions into the original fields.

`adelicPointHomeomorph` has the endpoints

    (Res_(L/K) X)(Adeles K) ≃ₜ X(Adeles L).

Both endpoints are actual scheme morphisms over the original field, as
in `NumberFieldAdelePoints`. Each has its own
`numberFieldSpreadAdelePointTopology`, obtained from its specified
integral model's independently defined final topology by its
specified generic-fiber point equivalence. The topology on one endpoint
is not defined using this new Weil homeomorphism.

The construction composes three previously established homeomorphisms:
the inverse lower spread comparison, the original full fixed-model Weil
comparison, and the upper spread comparison. Quasi-compactness of Y's
underlying space follows from its quasi-compact structure morphism over
its affine base. Its projective immersion supplies the required
relative separatedness and underlying quasi-separatedness.
`adelicPointHomeomorph_model` proves that this composite agrees exactly
with the fixed-model map under the two generic-fiber identifications.
`adelicPointHomeomorph_stage` then proves its restriction formula at
every enlarged lower support U and its full upper preimage: applying
the new map to the original lower stage point after inclusion and
spread identification equals applying the original
`adelicLevelPointHomeomorph`, followed by the literal upper inclusion
and upper spread identification. The proof uses the model formula and
the existing fixed-model stage theorem.

`adelicPointHomeomorphOfSpreads` allows arbitrary independently specified
finite-type spreads P and Q of the two original field schemes, over
possibly different finite sets U and V. The assumptions on their
structure morphisms are local finite type and quasi-compactness;
no additional separation hypothesis on P or Q is imposed. Their
generic-fiber isomorphisms are part of their specification. The proof
derives quasi-compactness of the constructed lower Weil model from
`affineChartWeilRestriction_quasiCompact`, using M's finite-affine-
neighborhood property, and applies the two proved spread-independence
equalities to the continuity assertions. It keeps the same underlying
equivalence. Accordingly `adelicPointHomeomorphOfSpreads_apply` proves
pointwise equality with `adelicPointHomeomorph` by reflexivity.

This unit completes this topological assembly for number fields and the
stated actual projective models. Identification of the resulting map
with evaluation of the original field Weil counit along the literal
full-adele inclusion remains a separate host obligation; the stage
formula here records its precise original arithmetic maps. The
function-field analogue and the other assertions of the five-section
paper also remain separate obligations.
