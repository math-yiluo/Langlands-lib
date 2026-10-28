# Unique descent of distributions supported on a closed subset

`Langlands.HarmonicAnalysis.Distribution.closedSupportedDescent.{u}` proves
exactly the published proposition
`Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentStatement.{u}`.
For every Hausdorff, locally compact, totally disconnected space `X : Type u`
and every closed subset `Z`, with its induced subtype topology, the actual
linear map `Distribution.closedPushforwardSupported hZ` is bijective.
Thus every ambient algebraic distribution annihilating all test functions
that vanish pointwise on `Z` descends to exactly one algebraic distribution
on `Z`.

The proof first establishes the algebraic helper
`closedPushforwardSupported_bijective_of_surjective`. This helper needs only
a topology, a closed subset and surjectivity of the published restriction
map `r = SchwartzBruhat.restrictClosed hZ`.

For injectivity, equality of the two supported pushforwards implies equality
of their coercions to `Distribution X`. These coercions are the images under
the algebraic dual map of `r`. Mathlib's
`LinearMap.dualMap_injective_of_surjective` then gives equality of the original
distributions on `Z`.

For surjectivity, let `T` belong to the published submodule `supportedOn Z`.
If `r f = 0`, evaluating at every point of the subtype `Z` shows that `f`
vanishes pointwise on `Z`. The defining property of `supportedOn Z` therefore
gives `T f = 0`, proving `ker r ≤ ker T`. Mathlib's `Submodule.liftQ` factors
`T` through the quotient by `ker r`. The first isomorphism theorem
`LinearMap.quotKerEquivOfSurjective` identifies this quotient with the actual
Schwartz–Bruhat space of `Z`. Composing the factored functional with the inverse
of that linear equivalence gives an element `D : Distribution Z`. The
representative formulas `quotKerEquivOfSurjective_symm_apply` and `liftQ_apply`
show that the actual supported pushforward of `D` equals `T`. This proves
surjectivity into the specified submodule, as an equality of its elements.

The final theorem discharges the helper's surjectivity premise using the
published theorem `SchwartzBruhat.closedRestrictionSurjective` from
[ClosedRestrictionProof](ClosedRestrictionProof.md). It has no additional
premise: its type is exactly `ClosedSupportedDescentStatement.{u}`. The
topological restriction argument is imported and is not redeveloped here.
The target statement and all imported Lean and Markdown pairs are unchanged
by this proof module.

The universe is arbitrary. There is no nonemptiness assumption on `X` or `Z`,
and the quotient and dual arguments include the empty cases. No countability,
compactness of the entire space, manifold, group, measure or continuity
hypothesis is added. Distributions remain the full complex algebraic dual,
and support remains the published pointwise-annihilator condition. This
module proves bijectivity; it exports no chosen inverse or locally closed
descent or orbit-vanishing result.

Worker 182 authored this internal algebraic deduction from the published
Library constructions and Mathlib's quotient and dual-map APIs. Worker 128's
separately published closed-restriction theorem supplies the topological
input. The motivating distribution-descent remark and its distinction from
the present support convention are documented in the unchanged
[ClosedSupportedDescentStatement](ClosedSupportedDescentStatement.md);
this proof relies on the Library statement and the imported restriction
theorem rather than a new transcription of that literature.
