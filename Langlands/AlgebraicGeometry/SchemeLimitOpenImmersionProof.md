# Proof of open-immersion descent along an actual affine limit

Worker 105 authored the reused proof; Worker 148 checked and prepared this
proof-only submission. `relativeOpenImmersionDescent` proves the exact proposition
`Langlands.AlgebraicGeometry.AffineLimit.RelativeOpenImmersionDescent`.
It is the relative affine-scheme-limit reformulation of the open-immersion
clause in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). The registered source
is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The proof implements the descent argument using Mathlib's actual scheme
limits and open subschemes. It imports the published
`Langlands.AlgebraicGeometry.SchemeLimitAffineProof` by Lean name for its
Cartesian comparison of the limiting and stage `baseChangeMap` morphisms.

The data are a small cofiltered diagram D of affine schemes over an affine
base S, an actual cone c with a witness that it is limiting, and a map
p from its point to S compatible with every cone projection. The source
and target model structure maps a and b are each locally of finite
presentation, quasi-compact and quasi-separated. A relative morphism f
satisfies f ≫ b = a. The theorem proves that `baseChangeMap a b f w p`
is an open immersion if and only if `baseChangeMap a b f w (t.app i)`
is an open immersion for some diagram index i.

Write A and B for the diagrams obtained by base-changing the source
and target models to the given affine diagram. The existing
`TargetLimit.diagram`, `cone` and `isLimitCone` constructions supply these
diagrams and their actual limiting cones. Their transition morphisms are
affine. Their objects are quasi-compact and quasi-separated under the
displayed model hypotheses; the limit of the original affine diagram is
also affine.

Suppose that the limiting `baseChangeMap` is an open immersion.
`exists_open_image_level` applies `exists_preimage_eq` to its open image
in the limiting target. That image is compact because the limiting source
is quasi-compact. This constructs a compact open V at one target stage
whose limiting preimage is precisely the image.
`exists_open_image_level_full` then uses `exists_map_eq_top` in the source
diagram to pass to a further stage at which the entire source maps into
the corresponding inverse image of V.

Form the diagram of these open subschemes over the over-category of the
chosen stage. `isLimitOpensCone` gives its limiting open subscheme.
The limiting open immersion is isomorphic to that open inclusion by
`IsOpenImmersion.isoOfRangeEq`. The open diagram has compact,
quasi-separated objects and affine transitions.
`exists_inverse_open_level` factors the inverse, composed with the
projection to the original source model, through one of these opens
using `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`.
It then uses
`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` for the target
model to descend the right inverse identity to a further open.

In `exists_isOpenImmersion_baseChangeMap`, the full-source containment
constructs forward lifts from every subsequent source stage into its
open target stage. These lifts commute with transitions and with the
limiting isomorphism. The left inverse identity therefore holds after
composition with a limit projection; the same finite-type equality
descent theorem, now for the source model, makes it hold at a stage.
The descended inverse to the original source model lifts to the actual
base-changed source by `pullback.lift`. Pullback projection identities
prove both inverse equations. Thus the forward lift is an isomorphism,
and the stage `baseChangeMap`, its composite with the open inclusion,
is an open immersion.

Conversely, `cone_baseChangeMap_isPullback` identifies the limiting map
as a base change of any stage map. Base-change stability of open
immersions proves the reverse implication.

All maps are the actual categorical base-change morphisms. The proof
retains arbitrary universe u, both models' local finite presentation,
quasi-compactness and quasi-separatedness, and arbitrary transition maps.
It assumes neither model affine or separated. The original filtered-ring
specialization, the other Theorem 3.4 clauses and the remaining sections
of the paper are separate obligations.
