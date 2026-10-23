# Tensor on relative geometric Picard-zero classes

For an abelian scheme `A/S` and every test scheme `T : Over S`, this module
restricts the actual tensor operation on rigidified line-bundle classes to
`PicardZeroClasses A T`. Schemes and fields use universe `u`.

All constructions assume explicitly
`preservation : Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement`:
the fixed canonical pullback tensor comparison is invertible for every scheme
morphism. The two unit laws additionally assume
`coherence : Langlands.Scheme.Modules.PullbackTensorUnitCoherenceStatement`,
the two specified unit-compatibility diagrams for that same comparison.
These propositions are not proved here.

## Family and class closure

`isPicardZeroFamily_tensor` states that the tensor of two actual rigidified
families satisfying `IsPicardZeroFamily A` again satisfies that predicate.
The rigidified relative family lives on `T ×_S A`, whereas the chosen
base-changed abelian scheme lives on `A ×_S T`. Its `familyLineBundle` is
therefore obtained by pullback along the inverse factor symmetry. The proof
uses `LineBundle.pullbackTensorObjIso` for that symmetry to identify the
underlying bundle of the tensor family with the tensor of the two underlying
fibre families. `isGeometricallyPicardZero_tensor` supplies the geometric
condition on that tensor, and transport along the inverse comparison gives
the result on the original family. Rigidification is retained by the actual
`RigidifiedLineBundle.tensor`; the geometric condition concerns its underlying
line bundle.

`isPicardZeroClass_tensor` descends this closure result to the quotient by
compatible rigidified isomorphism. Quotient induction on both inputs reduces
its proof to the family lemma. The geometric condition on representatives
was already shown to be invariant under compatible isomorphism in
`RelativePicardZero`.

`picardZeroClassesTensor preservation A T` is the resulting binary operation
on `PicardZeroClasses A T`. Its underlying value is exactly
`RigidifiedLineBundle.classesTensor` on the two underlying classes;
`picardZeroClassesTensor_val` proves this formula by reflexivity. The second
component of the subtype is the class-closure proof, so the operation adds
no arbitrary data.

## Unit laws

`picardZeroClassesTensor_left_unit` and
`picardZeroClassesTensor_right_unit` identify tensoring with
`trivialPicardZeroClass A T` on either side with the input class. The canonical
trivial class belongs to Picard zero by the previously proved trivial-family
lemma. Both equations follow by subtype extensionality from the corresponding
unit laws on all rigidified classes, which use the actual compatible sheaf
unitors and retain the explicit unit-coherence hypothesis.

## Provenance and scope

This is a derived restriction of the rigidified tensor construction in
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
literature ID `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Paragraph (6.2), printed p.88 (PDF p.92), gives rigidified line bundles, their
tensor product and compatible isomorphism classes. Printed p.95 (PDF p.99)
gives the point formula for `φ_L`; Corollary (7.22), printed p.106
(PDF p.110), identifies its kernel with `Pic⁰`. As specified by the parent
task, the existing geometric predicate tests translation invariance on each
algebraically closed geometric fibre. The proof here is the direct tensor
closure argument for that predicate, followed by quotient induction and
subtype restriction, rather than a proof of the source's kernel theorem.

The operation and unit equations are objectwise for every test scheme. This
module does not prove associativity, commutativity, existence of inverses, or
compatibility with relative pullback, and hence does not yet construct an
abelian-group-valued Picard-zero presheaf. No noetherian or projectivity
hypothesis is needed for these conditional constructions.
