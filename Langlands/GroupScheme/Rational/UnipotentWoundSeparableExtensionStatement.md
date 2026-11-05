# Woundness under separable algebraic field extension

Author: Worker 1608.

`Langlands.GroupScheme.UnipotentWoundSeparableExtensionStatement.{u}`
is a Prop-valued target. This file states the result and supplies no
proof.

For all fields `k K : Type u`, an algebra structure `Algebra k K`, and
`Algebra.IsSeparable k K`, it asserts that every smooth connected affine
unipotent actual group scheme `G` over `Spec k` satisfies
`HasConstantAffineLineMaps G` if and only if its actual base change to
`Spec K` satisfies `HasConstantAffineLineMaps`.

`HasConstantAffineLineMaps` quantifies over every actual ground-field
scheme morphism from the affine line, without a group-homomorphism
condition. Each such morphism must factor through the terminal object
of the category of schemes over the field at some rational value.
Both sides use this same definition over their respective fields.
The scalar extension is the existing group-scheme pullback along
`Spec.map (CommRingCat.ofHom (algebraMap k K))`, including its induced
group structure. The existing representation-theoretic predicate
`IsUnipotent` is retained unchanged.

The extension is separable algebraic: Mathlib's
`Algebra.IsSeparable k K` means that every element of `K` is separable
over `k`, and implies algebraicity. There is no finite-dimensional or
Galois hypothesis. In particular, the statement covers finite separable
extensions and a separable closure of any field. It does not assert
invariance under separable transcendental extensions. Neither field is
assumed perfect, infinite, or algebraically closed; characteristic zero
and positive characteristic are both included.

The provenance is derived from Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Proposition B.3.2,
printed p.572 / one-based PDF p.598. The source is registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`,
and readable at
`/home/taskhub/central-library/Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`.
Woundness there has the affine-line meaning of Definition B.2.1,
printed p.568 / PDF p.594. Remark B.2.2 on that same page explicitly
identifies woundness with triviality in characteristic zero.

Two scope changes are explicit. First, the source treats arbitrary
separable extensions, while this target selects the algebraic case
needed for passage to a separable closure. Second, Appendix B assumes
positive characteristic, so the characteristic-zero case is an
additional part of this derived target, justified by Remark B.2.2.
One route to that observation uses the splitness of smooth connected
unipotent groups over perfect fields, stated in CGP Proposition A.1.4,
printed p.467 / PDF p.493.
In characteristic zero the ground field is perfect; a split unipotent
group with affine-line constancy must be trivial, since its identity
homomorphism vanishes by the split-source rigidity theorem. Triviality
is preserved and reflected by field extension. This describes the
characteristic-zero rationale, not an implemented proof in this file.
A proof must also justify the source's structural arguments for the
Library's existing unipotence predicate.

The source proves separable invariance together with the central
additive-subgroup criterion and the cckp-kernel assertions. Those other
conclusions are outside this target. The published
`UnipotentWoundCriterionStatement` states the central criterion alone
and does not supply this field-extension result.

This target is a missing prerequisite for the ambient stability step
in woundness of the ordinary radical modulo the split radical.
It neither constructs a canonical split part nor assumes one, and
it does not itself prove that quotient woundness statement.
