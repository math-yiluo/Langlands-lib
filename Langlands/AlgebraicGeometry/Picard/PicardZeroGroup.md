# The abelian-group presheaf of geometric Picard-zero classes

This module equips the existing geometric Picard-zero classes with their
proved abelian-group structure. Tensor product is addition, the trivial
rigidified class is zero, and actual relative pullback is additive. The
inclusion into all rigidified classes is a natural family of additive
homomorphisms.

## Source and provenance

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI, paragraph
(6.2), printed p.88 (PDF p.92), defines the rigidified classes, tensor
product and parameter pullback. Chapter VII, Corollary (7.22), printed
p.106 (PDF p.110), identifies the field Picard-zero part with the kernel
of the associated homomorphism. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The existing `GeometricPicardZero` and `RelativePicardZero` modules use
translation invariance on every geometric fibre. This contribution
retains that condition and derives its group-valued presheaf from the
published tensor monoid and inverse-closure theorem. It does not prove
the source's identity-component characterization anew or assume a
representing dual scheme.

## Explicit hypotheses

The construction uses the same six mathematical premises as
`RigidifiedClassGroup`: the five fixed tensor/coherence propositions
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`,
`PullbackTensorSymmetryStatement`, and the comparison
`LocallyFreeRankOneIffTensorInvertibleStatement Y` for every scheme `Y`.
Pullback additionally takes `PullbackTensorCompositionStatement`.
These remain explicit hypotheses; this module does not prove them.

The geometric pullback-stability and rigidified pullback-coherence
premises are discharged by the published theorems `picardZeroPullback`
and `RigidifiedModule.pullbackCoherence`.

## Inverses and group laws

`picardZeroClasses_isUnit` proves that every element of
`PicardZeroClasses A T` is a unit for the existing
`picardZeroClassesCommMonoid`. After unpacking the geometric-condition
subtype, quotient induction reduces to a rigidified line bundle `L`
and a proof that it satisfies the geometric condition.

The named local-rank-one comparison supplies a module-sheaf inverse
`N` and evaluation `L ⊗ N ≅ O`. Braiding and the reverse comparison
show that `N` is locally free of rank one. `localizedTensorIso`
converts the evaluation to the explicit sheaf tensor.

The existing `picardZeroInverseClass` then rigidifies this inverse
using the evaluation. Its geometric Picard-zero membership was proved
in `GeometricPicardZeroInverse`: fibrewise pullback preserves the
evaluation, and uniqueness of tensor inverses transfers translation
invariance. The existing `picardZeroClassesTensor_inverseClass`
proves the product equation inside the geometric-condition subtype.
This supplies a unit witness.

`picardZeroClassesCommGroup` applies Mathlib's `commGroupOfIsUnit`.
The tensor multiplication and trivial class are unchanged, and the
inverse law follows from the proved unit witnesses.
`AdditivePicardZeroClasses` is the additive type tag of the same
subtype, and `picardZeroClassesAddCommGroup` transfers this group
structure to additive notation.

## Pullback and inclusion

`picardZeroInclusionAddHom` is the additive conversion of the existing
monoid inclusion. Its underlying function forgets only the geometric
membership proof. `picardZeroClassesPullbackAddHom` is the additive
conversion of actual parameter pullback, using `picardZeroPullback`
to discharge geometric stability. Both maps preserve negatives
because they are additive homomorphisms between groups.

`picardZeroGroupPresheaf` packages these values and pullback maps in
`AddCommGrpCat.{u + 1}`. Its identity and composition laws follow by
evaluating the laws of the existing set-valued `picardZeroPresheaf`.
`picardZeroGroupPresheafForgetIso` has identity components and recovers
that presheaf.

`picardZeroGroupInclusion` packages the additive inclusions into the
rigidified group presheaf. Its naturality is definitional: forgetting
the geometric condition commutes with the same actual pullback.

## Scope

The base is an arbitrary scheme in the fixed universe. The values
remain in universe `u + 1`; no smallness is asserted. The construction
does not prove fppf descent, representability, dual existence, or
independence from the explicit tensor-coherence inputs.
