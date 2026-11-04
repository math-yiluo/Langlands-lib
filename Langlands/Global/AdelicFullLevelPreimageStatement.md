# Full-adele preimages of actual arithmetic-level model points

This derived statement isolates the full-level preimage equality used in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.11, Proposition 4.4, second paragraph of the proof. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Fix a finite set `S` and the original outside-`S` integer base `C`. Let `A` be
the existing actual arithmetic-level subring of the full adele ring `B`.
For a proper morphism `f : X → Y` of schemes over `Spec C`, with `Y → Spec C`
quasi-compact and separated, the map `X(B) → Y(B)` pulls the range of
`Y(A) → Y(B)` back exactly to the range of `X(A) → X(B)`.

The points are the existing `RingPoint` morphisms over `Spec C`. The carriers
of the full-adele point spaces are `CurvePlaceFixedModelAdelePoints` and
`NumberFieldFixedModelAdelePoints`; their coefficient algebras are the existing
`curvePlaceAdeleOver` and `numberFieldAdeleOver`, with their original integer-base
actions. In each clause the let-bound algebra homomorphism `ι` is the literal
subring inclusion `A → B`. Its compatibility with the original diagonal scalar
actions is reflexive. All point maps are coefficient extension or postcomposition
by `f`. Ranges avoid adding injectivity assumptions on these point maps.

`CurvePlaceFullLevelPreimageStatement` uses the actual discrete curve places of
arbitrary fields `k` and `F` with an algebra structure. It therefore includes
global function fields over finite constants, without imposing a chosen
rational-function presentation. `NumberFieldFullLevelPreimageStatement` applies
to every number field; the full adele ring and its level include every infinite
completion. Both clauses allow empty `S` and arbitrary nonaffine schemes.
`AdelicFullLevelPreimageStatement` is exactly their conjunction in an arbitrary
common universe `u`.

The scope beyond the literal global-field, separated finite-type setting is
derived as follows. Properness and the target hypotheses make the source
quasi-compact and separated over the affine integer base. Outside `S`, the
existence part of the valuative criterion lifts completion-valued source points
to the completed valuation rings. The product-ring point comparison assembles
these lifts and the unrestricted field factors into an `A`-point. To compare its
image with the original `B`-point, embed `B` into the product of all completion
fields, use the injective product-point comparison, then use separatedness and
reducedness to descend equality along that coefficient inclusion. No finite-type,
finite-constant-field, local compactness or topology assumption is needed for
this algebraic argument.

This statement pair does not supply a proof. Proper spreading, topological
properness on full adelic point spaces, eventual stabilization, and the other
whole-paper results remain separate obligations.
