# Additivity of the actual dual scheme maps over a field

`Langlands.AbelianScheme.FieldDualSchemeMapAdditivityStatement` is the
proposition that the actual dual morphism of a sum is the pointwise
tensor sum of the actual dual morphisms.

For every field `k : Type u`, abelian schemes `A` and `B` over `Spec k`,
proofs `hA : HasDualScheme A` and `hB : HasDualScheme B`, and
homomorphisms `f g : A ⟶ B`, it asserts

`dualSchemeMap (f + g) =
  prod.lift (dualSchemeMap f) (dualSchemeMap g) ≫ dualTensor`.

Here every `dualSchemeMap` uses the published
`homPicardZeroPullback` proof and the displayed representability
witnesses. The equation is in
`Hom_Over(Spec k)(dualScheme B hB, dualScheme A hA)`.
The binary product is the chosen categorical product in `Over (Spec k)`.

## Source and provenance

The original source is Edixhoven–van der Geer–Moonen, *Abelian
Varieties*, preliminary draft, Chapter VII, Lemma (7.16)(i) and
Corollary (7.17), printed p.104 (PDF p.108). The dual-map convention and
the distinction between the two homomorphism assertions appear in
Chapter VI, Definition (6.19) and Remark (6.20), printed p.96
(PDF p.100).

Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`.
Content SHA-256:
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

Lemma (7.16)(i) states that for a line bundle with zero associated
homomorphism, pullback along `f + g` equals the tensor of the two
pullbacks in the relative Picard group. Corollary (7.17) applies this
to the dual and asserts that dualization is a homomorphism on Hom group
schemes. The proposition here is the resulting addition equation for
the Library's actual chosen universal representative, formulated as
an equality of underlying scheme morphisms.

This is a derived statement. To prove it from the source formulation,
one must compare the actual rigidified geometric-fibre Picard-zero
functor with the source's `Pic⁰` on all test schemes, including
nonreduced ones. The rigidification must also be respected when
passing from relative Picard classes to the chosen rigidified
classes. The dual maps classify pullback of the Poincaré family, and
`dualTensor` classifies tensor of its two universal pullbacks. Once
these class comparisons are proved, universal uniqueness gives the
displayed equality. The statement supplies no proof of those
comparisons.

## Explicit hypotheses and scope

The proposition universally quantifies proofs of the existing
`pullbackTensorComparisonIsIsoStatement` and
`PicardZeroPullbackStatement`. These are the hypotheses needed to form
the actual rigidified tensor and its universal classifying map.
No proof of the desired addition equation is included among its
inputs.

`HasDualScheme` supplies existence of an actual universal family for
the specified object; the statement does not assert representability
for every abelian scheme. The target is an equality of actual scheme
maps, so it needs no chosen inverse bundles, abelian geometry for the
duals, or bundled group structures.

The published `dualSchemeMap_tensor` instead says that each fixed
dual map preserves tensor multiplication. The present statement is
additivity as `f` varies, a separate obligation. It is field-only and
does not assert arbitrary-base additivity, a rational extension, or a
proof. Once proved, it can supply the addition law for an additive
dualization map after equipping the chosen duals with the existing
constructed group structures.
