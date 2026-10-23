# Homomorphism pullback preserves geometric Picard-zero families

`Langlands.AbelianScheme.HomPicardZeroPullbackStatement` is a
proposition definition. For every base scheme `S`, abelian schemes
`A` and `B` over `S`, homomorphism `f : A ⟶ B`, parameter scheme
`T` over `S`, and actual rigidified family `L` on `T ×_S B`,
it asserts that `homFamilyPullback f T` preserves the geometric
Picard-zero condition.

The pullback in the conclusion is the existing actual functor,
using the map `T ×_S A → T ×_S B` induced by `f` and the proved
commuting square of relative unit sections. No arbitrary map on
classes or dual schemes occurs in the target.

## Source and derived provenance

The registered source is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft,
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI paragraph (6.2), printed p.88 (PDF p.92), supplies the
rigidified pullback interpretation. Proposition (7.6) and its proof,
printed p.100 (PDF p.104), give
`t_x^* f^* M ≅ f^* t_{f(x)}^* M` and the resulting formula for
the associated homomorphism. Corollary (7.22), printed p.106
(PDF p.110), gives the field Picard-zero kernel criterion.

The present statement is a derived fibrewise consequence, expressed
in the exact translation-invariance predicate already selected by
the parent task. On each algebraically closed field-valued fibre,
the base-changed homomorphism carries a point `x` to `f(x)`, and
pullback of the translation-invariance isomorphism at `f(x)` gives
translation invariance at `x`. A Lean proof must construct the
required fibre-product identifications and line-bundle pullback
comparisons, including transport from `T ×_S A` to the chosen
`A ×_S T` used by `familyLineBundle`.

Thus arbitrary-base quantification here comes from the explicit
geometric-fibre predicate and this base-change argument, rather
than an extrapolation of a field representability theorem. There
is no projectivity, noetherian, or dual-existence hypothesis.

## Proof obligation

This file supplies a statement, not its proof or a new axiom.
A separate proof task must prove the exact published proposition.
The statement can meanwhile be an explicit hypothesis when restricting
`homClassesPullback` to `PicardZeroClasses` and classifying the
pullback of a chosen Poincaré family. It supplies no tensor law or
additivity statement.
