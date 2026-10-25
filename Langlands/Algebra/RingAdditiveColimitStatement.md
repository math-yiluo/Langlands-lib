# Underlying additive colimits of directed rings

`Langlands.Algebra.RingAdditiveColimitStatement` is an internal supporting
proposition. It states that if a cocone identifies a commutative ring with the
direct limit of a nonempty directed system of commutative rings, the same cocone,
viewed additively, identifies its underlying additive group with the additive
direct limit.

The index type `ι`, component rings `A i`, and target ring `R` have three
independent universes. The index is a nonempty directed preorder. The ring maps
`f i j h` satisfy `DirectedSystem`, and the ring homomorphisms `g i : A i →+* R`
satisfy `g j (f i j h a) = g i a`. No injectivity of these component or transition
maps is assumed.

The hypothesis is bijectivity of the actual `Ring.DirectLimit.lift` constructed
from `g` and its compatibility law. The conclusion is bijectivity of the actual
`AddCommGroup.DirectLimit.lift` constructed from the same maps after taking
`toAddMonoidHom`. Each comparison sends the canonical class of `a : A i` to
`g i a`. The additive construction uses `Classical.decEq ι`; this is a choice
of index equality for the construction, not a new hypothesis on the diagram.

This is an internal universal-property consequence for Mathlib's two direct-limit
constructions, not a separately attributed Stacks lemma. Its proof obligation can
be discharged by representing direct-limit elements at a component and using
eventual vanishing to transfer injectivity; no localization, finiteness, locality,
or flatness hypothesis is involved. The relevant existing APIs are in
`Mathlib/Algebra/Colimit/Ring.lean` and
`Mathlib/Algebra/Colimit/Module.lean`.

The intended application is the regular-module adapter for a local algebra
approximation system: bijectivity of its algebra-ring comparison supplies
bijectivity of the underlying additive comparison. This proposition alone makes
no assertion about approximation-system existence or flatness.
