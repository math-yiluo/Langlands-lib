# Cocenter Kottwitz surjectivity through maximal-torus points

This derived step in the cocenter construction of Kaletha–Prasad, *Bruhat–Tits
theory: a new approach*, §11.5, printed pp.429–430 (PDF pp.460–461), proves
surjectivity of the cocenter Kottwitz composite from explicit torus inputs.
The registered 1 November 2024 corrections, PDF pp.43–45, concern §11.7 and do
not change this passage. The construction uses the existing actual group
schemes and integral inertia targets.

`cocenterTorusRestriction a c` is the actual quotient map `c.quotient`
restricted along the maximal-torus inclusion of the supplied fundamental-group
choice `a`. The source is `a.torus` and the target is the actual cocenter torus.

`torusInertiaMap_surjective_of_geometric_surjective` proves a general
coinvariant fact for actual torus morphisms. A desired target coinvariant is
lifted to a geometric cocharacter, then lifted through the supplied surjective
geometric cocharacter map. Its source coinvariant maps to the desired class by
the representative law of `torusInertiaMap`. These are full integral
coinvariants; no torsion is removed.

`cocenterTorusInertiaMap_surjective` applies that fact to the actual restriction.
The existing `cocenter_cocharacter_surjective` supplies geometric surjectivity
for every cocenter over a field splitting the chosen maximal torus. Over the
supplied separable closure, the torus splits by the published separably closed
splitting theorem and algebraic base change. This argument needs no
simply-connected-derived hypothesis.

`cocenterKottwitzComposite_surjective_of_torus_data` works in the same local-field
coefficient tower as the simply-connected-derived Kottwitz target. It assumes
surjectivity of the selected torus Kottwitz map for `a.torus` and its exact
naturality square for `cocenterTorusRestriction a c`. Given a target class in the
cocenter torus inertia quotient, the preceding theorem lifts its additive class
to the maximal-torus inertia target. Torus Kottwitz surjectivity lifts that class
to a maximal-torus point. Its image under the actual inclusion in the ambient
group is a preimage for the cocenter Kottwitz composite, by the assumed square
and associativity of the actual point maps.

This is a conditional reduction. It does not prove the torus surjectivity or
naturality inputs, nor the unconditional
`SimplyConnectedDerivedKottwitzStatement`. The provenance is an internal
derivation supporting the cocenter construction, with the cocharacter
surjectivity theorem and the stated torus inputs retained explicitly.

`simplyConnectedDerivedKottwitz_of_torus_inputs` combines this result with the
existing cocenter construction and selected-target bijectivity reductions. Its
conclusion is the exact Library proposition
`SimplyConnectedDerivedKottwitzStatement`, with the following premises retained:

- `AlgebraicFundamentalGroupComparisonStatement`;
- `AlgebraicFundamentalGroupMapStatement`;
- `TorusFundamentalComparisonStatement`;
- `FundamentalInertiaMapStatement`;
- `TorusInertiaComparisonStatement`;
- `TorusKottwitzExistenceStatement`;
- the explicit naturality square for the selected torus Kottwitz maps and every
  actual torus morphism in every compatible coefficient tower.

For each field tower and group in the target, the proof chooses a maximal-torus
datum and an actual cocenter using their existing existence theorems. The five
comparison/descent premises make every cocenter target map bijective.
Specializing torus naturality to the induced morphisms between cocenters
supplies square transport. Torus existence supplies maximal-torus Kottwitz
surjectivity, and specializing naturality to the actual restriction supplies
composite surjectivity by the preceding theorem. The existing inverse-map
construction then gives the full target: unique existence for all actual
cocenter squares, specification and surjectivity of the selected map, and
uniqueness from each individual square.

This final theorem is still conditional on all seven listed premises. It does
not supply an unconditional proof of the host task or a new standalone torus
naturality statement.

`cocenterTorusRestriction` is imported from [CocenterTorusRestriction](CocenterTorusRestriction.md), with unchanged definition.
