# Actual restriction of raw full-order Harris levels

This internal construction starts with the actual universe-zero Harris arithmetic data,
an abelian scheme `B` over `S`, a dual witness `W`, a map `lam` to that dual,
two test schemes `T` and `T'` over `S`, a morphism `f : T' ⟶ T`, and a full-order
integral action on the direct family over `T`. It uses the existing named
`Prerequisites`, finite Weil-transition, adelic, torsion, invertible-order,
finite-etale roots-of-unity and finite-fibre assumptions. Both test schemes are
quasi-separated. It does not require faithfulness of the action to define the
raw level restriction.

There are two actual families over `T'`: the direct pullback from `S`, and the
successive pullback through `T`. Their integral and rational actions are compared
by `relativeIntegralActionRationalComparisonIso`. The direct integral action is
literally `(relativeEndRestrict B f).comp a`; its rational action is the existing
rational extension of that action. The successive action is ordinary rational
base change of the source action.

`harrisIntegralCMFullActionRestriction_multiple` proves that this actual family
comparison preserves the canonical pulled-back maps to the dual with multiplier
one. The proof rewrites rational dual pullback of integral maps as integral dual
pullback and applies `dualAbelianBaseChangeMap_relative_comp_pullback`. Thus the
polarization comparison comes from duality coherence, with no separately supplied
pairing equation. This statement concerns the maps to the dual and does not itself
assert that an arbitrary input `lam` is a polarization.

`harrisIntegralCMFullActionRestrictionLevelIso` applies the existing actual Weil
compact-open level isogeny to this comparison. Reindexing by `hodgeLevelFunctor`
retains the original Harris transporter category and its opposite right-action
convention. It identifies the direct restricted raw tower with the successive
raw tower at the same target field-valued point.

`harrisIntegralCMFullActionLevelRestriction` first applies the existing actual
Weil compact-open base-change transformation, then the inverse of that comparison.
Its source is the raw tower on `T` at the composite point `t ≫ f.left`; its target
is the raw tower on the original direct family over `T'` at `t`, with the literal
restricted integral action. This is a natural transformation for every original
Harris level transporter.

The provenance is internal: these constructions specialize and compose the
published integral-action, duality-coherence and Weil-level comparison maps.
They transport supplied monodromy-fixed Weil orbits. They provide no orbit
existence, normalized-class base-change comparison, identity or composition law
in the test-scheme variable, representing scheme, admissibility, smoothness or
division projectivity. Those remain obligations of the surrounding moduli
construction.
