# The all-test relation of an actual Čech datum

This module constructs the actual equivalence relation associated with a datum
`D : Langlands.GroupScheme.Descent.Datum p G`, where `p : S ⟶ B` is any morphism
of schemes in arbitrary universe `u` and `G` is any group scheme over `S`.
It uses the published definitions in `Descent.Data` without changing them.
There are no flatness, surjectivity, affineness, field, finite-type,
commutativity or smoothness hypotheses.

This is internal derived content: it unpacks the overlap isomorphism and its
triple-overlap cocycle using actual pullback universal properties. It introduces
no additional source theorem or effectivity assumption. All points below are
morphisms from arbitrary schemes in universe `u`, including nonreduced test
schemes.

## Point transport

`pullHom_eval` evaluates the published `pullHom` construction on a test-scheme
point. Pullback comparison isomorphisms preserve the projection to the original
group scheme and, as morphisms in the slice, the base coordinate. These two
projection equations identify the intermediate lifted point. Naturality of the
underlying pullback morphism then gives the stated evaluation equation.

In namespace `Descent.Datum`, `pointOverlap a b h` records the pair
`(a ≫ G.X.hom, b)` in `S ×_B S`, where `h` says that both coordinates have the
same image in `B`. The datum's `move a b h` is the point obtained by lifting
`a` to the first overlap pullback, applying `D.overlap.hom`, and projecting
from the second overlap pullback to `G`. `move_base` proves that its structure
map is `b`.

`pullHom_move` identifies point transport with evaluation of the datum pulled
back through any specified map to the overlap. `move_move` states that moving
a point first to `b` and then to `c` equals moving it directly to `c`.
The proof lifts the three base coordinates to the actual `Triple p`, evaluates
`D.cocycle` there, and uses `pullHom_move` on each of its three factors.

`move_injective` fixes the original base coordinate and the new base
coordinate. Equal transported points then have equal lifted points in the
second pullback. Invertibility of the overlap isomorphism and projection from
the first pullback recover equality of the original points. Applying this
injectivity to the composition law shows that diagonal transport is the
identity (`move_self`). Composition with this identity gives transport back
to the original base coordinate (`move_back`).

## Actual relation scheme and arrows

For `D`, `relationScheme` is the underlying scheme of `(fst p)*G`.
Its `source` is the first pullback projection to `G`; its `target` is the
underlying overlap isomorphism followed by the corresponding projection from
`(snd p)*G`. The map `relationMap` is the pullback projection to `Overlap p`.
The equations `source_base`, `target_base` and `relation_base` give the two
base coordinates and their common image in `B`.

`arrow a b h` is the actual relation arrow whose source is `a` and whose new
base coordinate is `b`. `arrow_source` and `arrow_target` compute its
endpoints. Conversely, `arrow_relation` reconstructs any test-scheme relation
arrow from its source and its target's base coordinate. Hence `move_relation`
identifies its target with point transport of its source.

`relation_hom_ext` proves that both endpoints determine the relation arrow.
The source endpoint determines the first coordinate in the overlap through
`source_base`; the target endpoint determines the second through `target_base`.
Two pullback extensionality arguments then identify the arrows.
`relation_mono` packages this as `Mono (prod.lift D.source D.target)`.

The declarations `relation_refl`, `relation_symm` and `relation_trans` have the
all-test shapes required by the Library's equivalence-relation quotient
interfaces. Reflexivity uses `move_self`. Symmetry constructs the arrow
moving the target back to the source's base coordinate and uses `move_back`.
Transitivity constructs the arrow from the first source to the final target's
base coordinate and uses `move_move` and `move_relation`. Every arrow is
constructed on the same test scheme as its input.

Finally, `source_pullback` is the defining first-overlap pullback square, and
`target_pullback` transports the second-overlap pullback square across the
underlying overlap isomorphism. These are actual `IsPullback` witnesses, with
endpoint maps in the stated orientation.

## Scope

The module constructs the relation and proves its laws. It does not construct
a quotient or a descended group scheme, and it does not establish affine
object effectivity or simply connected cover existence. Those constructions
can use these relation laws and squares as inputs to independently published
quotient and descent results.
