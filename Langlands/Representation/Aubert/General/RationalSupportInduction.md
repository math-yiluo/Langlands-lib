# Actual induction and subquotients from standard rational data

Worker 158 constructed this internal adapter from published actual induction,
standard-family geometry and subquotient transport. The standard-to-dynamic
closedness proof adapts Worker 480's argument in
[`RationalUnipotentRegularity`](RationalUnipotentRegularity.md). No new external
literature assertion is made.

The setting is the literal rational-point group `RationalPoint k G.X` of a
connected reductive group scheme over an arbitrary nonarchimedean local field
`k : Type u`, with the canonical `pointTopology`, an actual maximal split torus
`i`, and a generic cocharacter `ν`. The displayed standard-cocharacter and
standard-Levi-intersection assertions remain premises. Representation carriers
have universe `max (u + 1) v`, with independent `u` and `v`, matching the support
targets. The ambient point group is locally compact, nonarchimedean and
Hausdorff. The induction statements retain the relevant closed unipotent
subgroups; the stages statements also retain closedness of the coarse Levi.
All finite root subsets are allowed, including empty and full subsets.

`standardParabolic_isClosed_of_standardCocharacterStatement` requires none of
the ambient local compactness, nonarchimedean-group or Hausdorff-group
instances. It obtains the Hausdorff field topology from
`BruhatTits.localField_t2Space`. The standard-cocharacter assertion supplies a
cocharacter `ζ` identifying the standard parabolic subgroup functor with the
dynamic parabolic for `CommGroupScheme.groupHom ζ ≫ i`. Evaluation at the
identity test object changes the desired closedness to the published
`General.isClosed_dynamic_parabolic` at the canonical point topology.

`standardInduction_mapsShortExact_of_standardData` proves
`Derivative.Mirabolic.MapsShortExactIntertwiners` for actual normalized
induction along a standard parabolic. It applies
`General.normalizedInductionFunctor_map_isShortExact`, supplying
`compactOpenCofinal_of_nonarchimedean`, the closedness just proved, and
`RationalPointFamily.continuous_standard_projection`. The proof changes the
order of the injectivity, surjectivity and middle-exactness conjuncts to the
order of the generic exactness predicate. Every smooth short exact sequence is
covered; neither its terms nor their images must have finite length.

`standardInduction_isSubquotient_of_standardData` applies the published
`ExactSmoothTransport.map_isSubquotient` with this exactness theorem.
`SmoothRep.IsSubquotient B A` is the actual invariant-submodule then quotient
relation up to isomorphism. The generic theorem uses its equivalent
injective/surjective intertwiner presentation, so this conclusion concerns
actual smooth objects and maps.

For `K : Finset (SimpleRoot i ν)` and `J : Finset K`,
`standardInductionStagesIso_of_standardData` gives the natural isomorphism from
`leviNormalizedInductionFunctor` for the fine Levi indexed by `leviIndex K J`
inside `levi i ν K`, followed by ambient induction from that coarse Levi, to
direct ambient induction from the fine Levi. It applies the published
`RationalPointFamily.standardInductionStagesIso` without adding any projection
continuity or compact-limit premise. Projection continuity is supplied by
`continuous_standard_projection`; ambient compact-limit conditions come from
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`;
`General.isLimitOfCompactSubgroups_subgroupOf` restricts the fine unipotent
compact-limit property to the closed coarse Levi.

The inner functor includes the published canonical pullback from the fine
Levi to its literal `subgroupOf` copy inside the coarse Levi. The reused
stages theorem already proves the positive Haar-modulus product through
`standardJacquetModulus_stages`, and its underlying
`General.normalizedInductionStagesIso` respects the actual positive-half-modulus
normalizations. No modulus identity or isomorphism is assumed in this adapter.

`standardInduction_stages_isSubquotient_of_standardData` starts with an actual
subquotient `τ` of the inner induction of `σ`. Exact outer induction gives
`i_K(τ)` as a subquotient of that iterated induction. The component at `σ` of
the stages isomorphism and `SmoothRep.IsSubquotient.of_iso_right` give its
subquotient presentation in direct induction from `leviIndex K J`.
`standardInduction_stages_subquotient_transitive_of_standardData` applies
`Langlands.smoothSubquotientTransitivity` to carry every given subquotient `π`
of `i_K(τ)` to the same direct induction.

The direct imports are the rational stages construction, standard projection
continuity, standard unipotent regularity, exact-functor subquotient transport,
and actual subquotient transitivity. The latter two use the presentation
criterion in `Classification.SupercuspidalSupport`; no classification or
support theorem from that module is applied. Induction exactness uses the
published injectivity, middle-exactness and surjectivity results for actual
smooth induction. The stages construction uses actual smooth induction in
stages, the split-quotient comparison, and the character-twist comparison.
This argument applies no Langlands-classification theorem,
character-independence theorem, geometric lemma, or adjointness theorem.

This supporting unit does not prove
`RationalSupportCategoryJacquetVanishingStatement`. It supplies no compactness
of any parabolic quotient, inside-Levi cuspidal-series existence, irreducibility,
cuspidality or association conclusion. The inner subquotient presentation is
an input that must be obtained separately in a full support argument.
