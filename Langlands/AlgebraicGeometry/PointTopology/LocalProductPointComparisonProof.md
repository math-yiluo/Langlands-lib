# Proof of the comparison with actual base-changed local models

Author: Worker 208.
Source and dependency checks and submission: Worker 135.

`localProductPointComparison` proves exactly
`LocalProductPointComparisonStatement`, with its four independent clauses
and arbitrary common universe `u`.

The existing `localProductPointMap` is definitionally the composition of
`productPointMap` and `localFactorPointEquiv`. The latter is an equivalence
constructed using the actual pullback adjunction at each factor.
`localProductPointMap_injective` composes its injectivity with the existing
quasi-separated relative product comparison.
`localProductPointMap_surjective_of_isAffine` and
`localProductPointMap_surjective` compose its surjectivity with the affine
and quasi-compact/local-factor relative comparisons, respectively.
No additional scheme or ring hypotheses enter these compositions.
The injectivity clause requires only quasi-separatedness. Affine
surjectivity does not require local factors; quasi-compact surjectivity
with local factors does not require quasi-separatedness.

For the affine topology clause, the existing
`isHomeomorph_ringPointBaseChangeEquiv` applies separately with value
algebra `A = D = R i`. Mathlib's `IsHomeomorph.pi_map` gives the resulting
factorwise homeomorphism for the product topologies. Composition with
`productPointMap_isHomeomorph` proves that the original
`localProductPointMap` is a homeomorphism.
All point topologies are the existing independent global-section evaluation
topologies; the proof does not replace them.

These are derived geometric comparisons for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Theorem 3.6
and formulas (3.6.1)–(3.6.2), printed pp.6–8, as described in the
statement's paired Markdown. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The affine topology clause requires topological rings at each factor,
with no topology on the base ring, finite-type, local-ring, Hausdorff or
nonempty-index premise. The proof reuses the relative product comparison
and the affine topology comparisons. It supplies no arithmetic realization,
nonaffine topology, model descent, change-of-`S` or colimit assertion, and
does not complete the parent whole-paper task.
