# The abelian-group presheaf of rigidified line-bundle classes

`classGroupPresheaf` upgrades the existing actual rigidified class presheaf
to abelian groups. Tensor product is the addition, the trivial rigidified
line bundle is zero, and actual pullback supplies the additive maps.
The inverse laws are proved using ordinary tensor inverses and their
evaluation-induced rigidifications.

## Inputs and provenance

The source for the functor is Edixhoven--van der Geer--Moonen,
*Abelian Varieties*, Chapter VI, paragraph (6.2), printed p.88
(PDF p.92). It defines rigidified line bundles, their compatible
isomorphism classes, tensor multiplication, and relative pullback.
Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

This construction is conditional on the already published comparison
`LocallyFreeRankOneIffTensorInvertibleStatement Y` for every scheme `Y`.
That proposition equates local rank one with tensor invertibility for
the existing localized monoidal structure on actual module sheaves.
It has a separate proof obligation. The present module proves the
group construction from that named hypothesis; it does not prove the
comparison or supply its conclusion as an arbitrary chosen group.

The other inputs are exactly those of `RigidifiedClassMonoid`:
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`, and
`PullbackTensorSymmetryStatement`. Pullback additionally uses
`PullbackTensorCompositionStatement`. The existing theorem
`RigidifiedModule.pullbackCoherence` supplies identity and composition
coherence for rigidified pullback.

These are explicit named mathematical hypotheses. No inverse
function or group axioms are supplied by the caller.

## Inverse construction and proof

For `f : X ⟶ S`, a section `ε`, and `T : Over S`, `classes_isUnit`
proves that every element of the existing quotient
`Classes f ε section_eq T` is a unit for `classesCommMonoid`.
Quotient induction reduces this to an actual rigidified line bundle
`L` on `T ×_S X`.

Apply the rank-one comparison to its underlying module sheaf to
obtain an ordinary tensor inverse `N` with evaluation
`L ⊗ N ≅ O`. Braiding makes `L` a right inverse of `N`, so the
other direction of the same comparison proves that `N` also has
local rank one. The ordinary inverse is therefore a line bundle.
`localizedTensorIso` converts the monoidal evaluation to the explicit
sheaf tensor used by the rigidified construction.

The existing `rigidifyInverse` equips `N` with the rigidification
forced by that evaluation and the rigidification of `L`.
`classesTensor_rigidifyInverse` proves that their product is the
trivial rigidified class. This supplies a right inverse in the
commutative class monoid and hence proves `IsUnit` for the class.

`classesCommGroup` applies Mathlib's `commGroupOfIsUnit` to this
proof. Multiplication and the unit are those of the existing
`classesCommMonoid`; the inverse is chosen from the proved unit
witness. Mathlib proves its cancellation law. The construction
does not add an inverse law as a hypothesis.

## Additive notation and pullback

`AdditiveClasses` is the `Additive` type tag of the same quotient.
`classesAddCommGroup` transfers the constructed commutative group
to additive notation. Thus addition is tensor product and zero
is the class of the trivial rigidified bundle.

`classesPullbackAddHom` is the additive type-tag conversion of the
existing `classesPullbackMonoidHom`. Its underlying map is actual
pullback on compatible-isomorphism classes; the tensor and unit
preservation laws were already proved in `RigidifiedClassMonoid`.
As an additive homomorphism between groups it also preserves negatives.

`classGroupPresheaf` packages these groups and maps as a functor
`(Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}`. Its identity and composition laws
are evaluated from the existing set-valued `classPresheaf`.
`classGroupPresheafForgetIso` has identity components and identifies
the underlying set-valued functor with that original presheaf.
The value universe remains `u + 1`; no smallness is asserted.

## Scope

The source imposes additional conditions on `f` for its statements
about automorphisms and comparison with the Picard sheaf. These
conditions are not used for the conditional group construction here,
which works for an arbitrary scheme map with a section.
This module proves neither fppf descent, representability, nor the
rank-one comparison or the named tensor-coherence inputs.
