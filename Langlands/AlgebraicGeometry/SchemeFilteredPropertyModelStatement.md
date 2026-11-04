# Smooth and flat models over actual filtered ring stages

This unit gives two derived prerequisites for Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Theorem 3.4(1)–(2),
printed pp. 5–6. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
These are structural model-existence assertions derived from model
existence and property descent; they do not state the whole relative
property-descent theorem for a prescribed pair of models.

`SchemeFilteredPropertyModelExistence P` spells out the shared assertion.
For a small filtered category `J`, an actual commutative-ring diagram
`F`, a cocone `c`, and an `IsColimit c` witness, take a scheme morphism
`g : X → Spec c.pt` that is locally of finite presentation,
quasi-compact and quasi-separated, and satisfies `P`. It asserts the
existence of an actual stage `j`, a scheme `Xj` with structural map
`gj : Xj → Spec (F.obj j)`, and a map `π : X → Xj`. The map `gj` has the
same three finiteness properties and satisfies `P`. The square with
bottom map `Spec.map (c.ι.app j)` is a pullback. In particular this
compares the specified morphism `g` to the base change of `gj` along
the actual cocone map.

`SchemeFilteredSmoothModelExistence` and
`SchemeFilteredFlatModelExistence` instantiate that assertion with
Mathlib's smooth and flat scheme-morphism predicates.
`SchemeFilteredSmoothFlatModelExistence` is their conjunction; the two
models and stages may differ. The generic definition makes no claim
that every morphism property has this existence assertion.

The three finiteness hypotheses implement Conrad's finite-presentation
convention, including quasi-compact affine overlaps. Both models may be
nonaffine and nonseparated. Ring transitions may be noninjective; neither
the stages nor the colimit ring are assumed noetherian. The small filtered
category formulation extends the directed partially ordered set in the
source, and all sizes share an arbitrary universe `u`.

An independent route to these derived targets is noetherian approximation
over lifted integers, smooth or flat descent to a further finitely
generated subalgebra, and factorization through the original filtered
diagram. The integer base ensures finite presentation of that further
subalgebra, even when the original stages are nonnoetherian. No extra
descent hypothesis appears in either concrete target.

This file defines propositions. Eventual smoothness or flatness of a
prescribed model, descent for a relative morphism with nonaffine target,
and the other clauses of Theorem 3.4 remain separate obligations.
