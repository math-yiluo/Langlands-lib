# Cocharacter translations and infinite affine-root fibres for integer valuations

This internal construction works over an arbitrary field `k : Type u`, with an explicit
integer-valued valuation `v`, an affine group scheme `G` and supplied
`B : IntegerValuationBuildingData v G`. All rational points, cocharacters, centralizer data
and apartment actions are the original objects of `B`.

`B.cocharacterCentralizerPoint c t` evaluates an actual integral cocharacter `c` of `B.S`
at a unit `t : kˣ`, then maps the resulting torus point through `B.centralizer.s`.
For every rational character `χ` of the centralizer, its evaluation is
`t ^ latticePairing B.S (Cartan.characterRestriction B.centralizer.s χ) c`.
Applying the supplied integer valuation gives its real order as the order of `t`
times that integral pairing.

`translation_cocharacterCentralizerPoint` identifies the entire centralizer translation
vector as `(-IntegerValuation.order v t) ⊗ c`. To prove the equality, the implemented
proof applies injectivity of the supplied actual restriction-evaluation map, tests
against every rational character, and uses the preceding evaluation formula and
`IntegerValuation.eval_centralizerTranslation`. This proves the vector identity directly,
without choosing character denominators.

For every actual relative root, the root-datum valuation supplies a nonidentity root
element. Published actual rank-one factorization gives an opposite factor pair and
its integral coroot, whose pairing with that root is `2`. Evaluating this coroot at
a supplied unit of order one and using the vector identity gives an actual centralizer
point with root translation value `-2`.
`exists_centralizer_eval_translation_eq_neg_two` states this conclusion.

`exists_conjugateAffineFunctional_eq_add_two` maps that point to the actual normalizer.
Full supplied V6 identifies its apartment action with translation by the computed
vector. The inverse in conjugation therefore adds the constant `2` to every affine
functional having the chosen root derivative.

`infinite_fiber_affineRoots` and `infinite_fiber_extendedAffineRoots` assume only
`∃ t : kˣ, IntegerValuation.order v t = 1` beyond `B` and the indicated root membership.
Actual normalizer conjugation preserves the ordinary and extended affine roots.
Consequently each derivative fibre is closed under addition of the constant `2`.
The published `AffineRootSystem.infinite_fiber_of_add_const_mem` then produces infinitely
many distinct members of that same derivative fibre.

The provenance is an internal generalization of the local-field coroot and
constant-shift arguments in `ValuationAffineRootSystems`. The implementation reuses
the field-independent actual cocharacter evaluation theorem in
`CocharacterUniformizerEvaluation`, actual rank-one factorization, the integer centralizer
adapter and the generic normalizer-preservation and fibre lemmas. No local-field,
topological or completeness structure on `k`, building-data existence, affine-root
discreteness, reflection integrality, complete affine-root-system theorem or affine
Weyl containment is asserted.
