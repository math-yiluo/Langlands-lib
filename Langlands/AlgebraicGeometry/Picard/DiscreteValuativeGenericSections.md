# Generic sections detected by discrete valuative existence

This internal adapter combines the published discrete valuative
closed-image theorem with the published unramified generic-section
extension theorem. Its provenance is composition of existing Library
results and the universal property of a pullback. It introduces no new
translation from the literature.

`DiscreteValuativeCriterion.existence_stableUnderBaseChange` proves that
the published discrete existence predicate is stable under arbitrary
scheme base change. Given a test square for the base-changed morphism,
compose its two horizontal maps with the pullback square's maps. This
gives a test square for the original morphism with exactly the same
valuation ring, fraction field, algebra structure and DVR instance.
Apply the original existence premise, then pair its actual lift with
the original bottom map using the pullback universal property. The
two projection identities prove both triangles for the required lift.
This is the pullback argument used for Mathlib's full valuative
existence predicate, applied to the restricted set of DVR tests.

`DiscreteValuativeCriterion.closedIrreducibleImages_pullback_snd` applies
this stability and `discreteValuativeClosedIrreducibleImages`. For a
separated locally finite type morphism satisfying discrete valuative
existence, it gives closed images of closed irreducible subsets after
every base change whose new base is locally noetherian. Its original
base is arbitrary. It does not assert this image condition for base
changes with a nonnoetherian base.

For the remaining results, let `S` be integral, geometrically unibranch
in the Library's actual-stalk sense, and locally noetherian. Let
`p : X ⟶ S` be separated, locally of finite type and formally
unramified, and assume `DiscreteValuativeCriterion.Existence p`.

`genericSectionRestriction_bijective_of_discreteValuativeExistence`
proves bijectivity of actual generic restriction. Injectivity is the
published separatedness result. For surjectivity,
`discreteValuativeClosedIrreducibleImages` supplies the displayed-base
closed-image condition, and `unramifiedGenericSectionExtension` supplies
the actual section. No closed-image or full arbitrary-valuation
existence premise is assumed.

`discreteValuativeGenericSectionEquiv` packages this bijection between
actual section and actual generic-map subtypes. Its application lemma
identifies its forward function with the existing
`genericSectionRestriction`. The generic map is along
`S.fromSpecResidueField (genericPoint S)`.

`existsUnique_genericSectionExtension_of_discreteValuativeExistence`
unpacks surjectivity into a unique actual morphism `s : S ⟶ X`,
proving both `s ≫ p = 𝟙 S` and the prescribed equality after
restriction to that exact generic residue field. Subtype equality and
restriction injectivity prove uniqueness.

The universe is arbitrary. Local noetherianity remains an essential
input to these generic-section conclusions. This adapter does not
establish a limit reduction for an arbitrary valuation base, construct
a correspondence representer, compare correspondence classes with
actual line bundles, or prove the host two-axis bundle-extension
statement. Those remain separate obligations.
