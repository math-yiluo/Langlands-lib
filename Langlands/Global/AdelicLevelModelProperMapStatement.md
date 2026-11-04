# Proper maps on actual arithmetic-level model points

This unit states the arithmetic-level step in the proof of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.11, Proposition 4.4, first two paragraphs of its proof. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`CurvePlaceLevelModelProperMapStatement` concerns every function field `F` over
a finite constant field `k`, with the specified compatible rational-function
action, every finite set `S` of the actual curve places, and every proper
morphism `f : X ⟶ Y` over the spectrum of the actual outside-`S` integer ring.
The target structure morphism is locally of finite type, quasi-compact and
separated. Postcomposition by `f` on actual level-ring points is topologically
proper for the already defined `curvePlaceLevelModelPointTopology`.

`NumberFieldLevelModelProperMapStatement` gives the corresponding assertion for
every number field, with `S` a finite set of finite places and the full level
ring `numberFieldAdeleLevel`, which includes every infinite completion. Its
topology is `numberFieldLevelModelPointTopology`. The public statement is the
conjunction of these two clauses, in arbitrary common universe `u`.

Here finite type means local finite type together with quasi-compactness, and
separatedness is relative to the displayed integer base. Properness of `f`
and these properties of `Y` imply that `X` is also separated and of finite
type over that base. Thus the source and target match the separated finite-type
models in Conrad's proof without redundant hypotheses on `X`. Neither model
is required to be affine. The displayed maps are compositions of actual
over-category morphisms from the spectrum of the actual arithmetic level ring.
`IsProperMap` is Mathlib's topological properness, including continuity.

This is a derived, focused ingredient: it isolates the assertion about
`X_S(A_{F,S}) → Y_S(A_{F,S})` after proper models have been chosen. Finite
constants provide compactness of the completed integer rings in positive
characteristic. The supplied rational-function extension need not be separable.
Empty `S` is allowed; the level product argument does not use a nonempty
initial set. In the number-field convention, all infinite places are included
in the coefficient ring regardless of `S`.

The proposed proof uses the actual finite-type level-to-local-product
homeomorphisms. At field factors it uses properness on actual points over a
nondiscrete locally compact field. Outside `S`, the source integral point space
is compact and the target is Hausdorff, so continuity gives properness.
Arbitrary products of proper maps are proper. These facts also justify the
empty-level extension.

The product sentence on printed p.11 writes an identification between the
target's integral and field points outside `S`. That identification does not
hold for arbitrary separated finite-type targets: for the affine line over a
completed valuation ring it is the proper inclusion of that ring into its
fraction field, witnessed by the inverse of a uniformizer. This statement
does not use that identification. The compact integral factors suffice for
the level argument. The valuative criterion gives a different assertion,
equality of the preimage of target integral points with source integral
points for a proper morphism; that is a further ingredient in passing to
all adelic points.

This statement does not assert existence of proper models for arbitrary
field morphisms, the valuative preimage equality, properness on the full
adelic point spaces, or the eventual stabilization conclusion of Proposition
4.4. Those remain separate obligations of the whole-paper program.
