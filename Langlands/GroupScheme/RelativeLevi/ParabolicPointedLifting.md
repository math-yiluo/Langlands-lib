# Pointed cocharacter lifting for relative parabolics

`RelativeParabolicPointedDynamicLiftingStatement` says that, over every scheme
`S` and at each point `s`, a relative parabolic `i : P → G` in a reductive group
admits the following data. There is an etale morphism `p : U → S`, a specified
map `b : Spec κ(s) → U` with `b ≫ p = S.fromSpecResidueField s`, and a
cocharacter `χ : G_m,U → P_U`. The actual iterated base change
`(baseChange b).map ((baseChange p).map i)` is a closed subgroup and represents
the dynamic parabolic of `baseChangeCocharacter b (χ ≫ (baseChange p).map i)`.
The universe and base scheme are arbitrary. The closedness assertion concerns
this specified field fibre.

The theorem `relativeParabolicPointedDynamicLifting` proves the statement.
This is an internal consequence of published Library results, with the
following supporting steps in the same module.

1. `IsRelativeParabolicSubgroup.geometricallyConnected` obtains geometric
   connectedness of `P/S` from its residue fibres. Each fibre is parabolic in a
   connected reductive field group, so it is connected. The published theorem
   on smooth connected affine field groups makes that fibre geometrically
   connected. The fibre criterion then applies over `S`.
2. `IsParabolicSubgroup.exists_internal_dynamicCocharacter` starts with the
   published field characterization by a dynamic parabolic. The defining
   cocharacter has range in its dynamic centralizer and hence in the dynamic
   parabolic. The factorization property of a represented subgroup lifts this
   cocharacter to the source `P` of the original inclusion, retaining the
   representation identity.
3. `HomScheme.exists_pointed_etale_cocharacter` applies the published pointed
   split-source Hom lifting construction with source `G_m,S` and target `P`.
   The fibre input is the field cocharacter composed with the canonical
   multiplicative-group base-change isomorphism. The lifted actual Hom is
   converted back to a cocharacter by its inverse. `evaluate_comparison` and
   `Descent.gmBaseChange_tower` prove exact recovery through the canonical
   pullback comparison. The only target hypotheses for this helper are
   smoothness and affineness over `S`.
4. The final theorem applies these constructions to the parabolic residue
   fibre. Naturality of `Descent.pullbackComparison` gives the square for the
   original inclusion. Source and ambient isomorphisms transport field
   closedness to the raw iterated base change. Exact cocharacter recovery,
   dynamic functoriality under an ambient isomorphism, and invariance of range
   under a source isomorphism give the asserted all-test subgroup identity.

No relative closedness is assumed in these arguments. This unit supplies the
pointed fibre data for a subsequent local comparison; it does not yet prove a
local dynamic description on all of `U` or the final relative closedness target.

Shared declarations `IsRelativeParabolicSubgroup.geometricallyConnected` are imported from `Langlands.GroupScheme.RelativeLevi.ParabolicSourceGeometry`; their mathematical hypotheses, conclusions and data are unchanged.
