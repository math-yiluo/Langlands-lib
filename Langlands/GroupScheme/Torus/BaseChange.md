# Tori and arbitrary field extension

Worker 1340.

This is an internal consequence of the published definition
`Langlands.GroupScheme.IsTorus` in `Torus/Lattice.lean`. That definition
requires the group scheme to become a split torus over some extension
field of the same universe. The results here retain that definition
and place no algebraicity, separability, characteristic, or perfectness
condition on the fields.

`TorusBaseChange.CommonExtension k K L` records a field of the same
universe, maps from the two extensions `K` and `L`, and their agreement
on `k`. The maps are injective because their source rings are fields.
`TorusBaseChange.commonExtension` constructs these data from the quotient
of `K ⊗[k] L` by a chosen maximal ideal. Nontriviality of the tensor
product supplies that ideal, and its maximality gives the quotient's
field structure. The tensor-product inclusions agree on `k`, so their
composites with the quotient map satisfy the required compatibility.
This construction uses only existing Mathlib algebra results.

`IsTorus.baseChange` proves that a torus stays a torus after an arbitrary
extension of its ground field. Given an extension and a splitting
field, the proof forms their tensor product over the ground field,
uses its nontriviality, and takes the quotient by a maximal ideal. This
quotient is a field of the same universe containing compatible images
of both fields. The existing split-torus base-change theorem then
gives a splitting over this common field. The standard pullback
composition isomorphism identifies the two successive base changes.

`IsTorus.of_baseChange` proves the converse by composing the ground-field
extension with a splitting extension. `isTorus_baseChange_iff` combines
the two implications.

These are proofs about the existing torus predicate, with no added
structural hypothesis. They do not establish existence of a maximal
torus in a group, preservation of maximality under extension, or
containment of a maximal torus in a parabolic.
