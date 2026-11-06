# Relative parabolic normalizers from explicit generic inputs

`IsReductive.geometricallyConnected` proves geometric connectedness of the
structure morphism of every reductive group scheme over an arbitrary scheme.
For every field-valued point, the published
`IsReductive.isConnectedReductive_baseChange` gives a connected reductive
actual pullback. Its connectedness is exactly the field-test definition of
`GeometricallyConnected`.

The remaining lemmas work over every commutative ring `R` and the original
actual homomorphism `i : P ⟶ G`. They preserve all fields, algebra structures
and test schemes, including nonreduced tests and the empty base.

`RelativeParabolicNormalizerReduction.geometricallyConnected_of_parabolicDynamic`
assumes the exact proposition `ParabolicDynamicStatement`, reductivity of `G`,
and parabolicity after every algebra-valued field base change. It converts
an arbitrary field-valued map into its ring algebra structure using the
published `parabolic_atFieldPoint`. The parabolic-dynamic input gives an
actual cocharacter whose dynamic parabolic is the range of the actual
pullback of `i`. The published `dynamicConnected` then proves connectedness
of its source. Applying this to every field-valued map proves geometric
connectedness of `P`. The parabolic-dynamic theorem remains an explicit
premise: it has not been proved by this construction.

`normalizer_eq_of_statements` additionally assumes the exact propositions
`RelativeSelfNormalizerStatement` and `ParabolicSelfNormalizerStatement`,
smoothness of `P`, and closedness of `i`. The field theorem applies to each
actual connected reductive pullback of `G` and its parabolic subgroup.
The relative field-detection input, together with the geometric connectedness
just obtained, then proves equality of the original all-test normalizer
and range. The equality includes all schemes over the original base; it
is not deduced from a presumed fpqc cover by residue fields.

`properAmbient_of_statements` additionally assumes the exact proposition
`SelfNormalizingProperAmbientStatement`. Reductivity supplies smoothness,
affineness and geometric connectedness of `G`. The preceding two adapters
supply geometric connectedness and self-normalization of the actual subgroup.
The generic input therefore provides an actual proper locally finitely
presented scheme `Y` over `Spec R` and a map `r : G.X ⟶ Y` whose equality
fibres on every test scheme are exactly the right `P`-cosets.

`ProperAmbientMap i` stores the resulting actual ambient scheme, map,
properness, local finite presentation and all-test fibre equivalence.
`properAmbientOfStatements` selects that data by classical choice from
`properAmbient_of_statements` with exactly the same explicit inputs.

This is an internal consequence of the published reductive base-change,
field-test and dynamic-connectedness interfaces, together with the explicitly
supplied generic statements. It introduces no original-literature assertion.
It does not prove any of the supplied statement premises, construct a
parabolic cocharacter without one, or prove the unconditional relative
parabolic quotient existence target. A quotient construction and its
properness remain separate steps.
