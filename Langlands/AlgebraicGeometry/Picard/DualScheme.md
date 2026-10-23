# A chosen dual scheme and its Poincaré family

For an abelian scheme `A/S`, `HasDualScheme A` is the proposition
that there exist an actual `S`-scheme `P` and an actual rigidified line
bundle `L : RigidifiedFamily A P` satisfying `IsUniversalPicardZero A L`.
The latter predicate requires geometric Picard-zero membership and unique
classification of every geometric Picard-zero class by the actual
rigidified pullback of `L`. No representation equivalence or classification
map is supplied as arbitrary data.

The module works over every `S : Scheme.{u}`, conditional on a proof
`hA : HasDualScheme A`. It does not prove this existence proposition.
The field existence theorem is a separate statement and proof obligation;
the field theorem is not generalized to arbitrary bases here.

## Choice and the actual family

`dualScheme A hA` uses classical choice on the outer existential.
`poincareFamily A hA` chooses its witness family on `dualScheme ×_S A`.
`poincareFamily_universal` is the corresponding choice specification,
so this selection retains the tested universal property.

`poincareLineBundle A hA` applies the existing `familyLineBundle` to that
family. This is actual line-bundle pullback along the inverse canonical
symmetry from `A ×_S dualScheme` to `dualScheme ×_S A`. Thus its total
space has the conventional order used for the Poincaré bundle. The
rigidified family is retained separately in `poincareFamily`;
`poincareLineBundle` is its transported underlying line bundle.
`poincareLineBundle_picardZero` is the first conjunct of its universal
property, expressed on this total space.

## Classification and the distinguished section

`dualClassify A hA T q` selects the unique morphism from the universal
property for the actual Picard-zero class `q` over `T`. Its specification
`dualClassify_spec` says that pulling back the chosen Poincaré family
along this morphism gives `q.val`. `dualClassify_unique` is the other
part of the same unique-existence specification.

For an actual family `L` and its membership proof, `dualClassifyPullbackIso`
converts this equality of classes into existence of a rigidified
isomorphism using `classifyingMap_eq_iff`, then chooses one such
isomorphism. There is no assertion that this bundle-isomorphism witness
is unique.

`dualOrigin` classifies the canonically rigidified trivial bundle over
`S`, regarded as `Over.mk (𝟙 S)`. It is a morphism in `Over S`, hence
an actual section of the chosen dual's structure map. `dualOrigin_spec`
records its classification property. This provides a distinguished
section; identification with the unit of an abelian-scheme structure
requires the subsequent tensor-product group construction.

## Representation and naturality

The remaining constructions retain explicit compatibility proofs where
needed. `dualClassify_poincare` uses
`RigidifiedModule.PullbackCoherenceStatement` and the actual
`classifyingMap_id` law: the identity classifies the Poincaré family
itself, so `dualClassify_unique` identifies it with the chosen classifier.

`dualSchemeRepresentableBy` also takes
`PicardZeroPullbackStatement`. It specializes
`picardZeroRepresentableBy` to the selected universal family, giving
a representation of the actual set-valued `picardZeroPresheaf`.
`dualClassify_pullback` says that classifying the restricted pullback
of `q` along `f : T ⟶ U` gives `f` followed by its classifier over
`U`. The proof applies classification uniqueness, then the ambient
composition law and `dualClassify_spec`.

## Provenance and limits

The registered original source is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft,
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Paragraph (6.2), printed p.88 (PDF p.92), gives the rigidified universal
bundle property by actual pullback. Chapter VI §3, printed p.95
(PDF p.99), restricts to abelian varieties over a field and discusses
the Picard scheme and its Poincaré bundle. Theorem (6.18) and
Definition (6.19), printed p.96 (PDF p.100), establish the field
dual abelian variety and name its restricted Poincaré bundle.
The geometric Picard-zero criterion used here is the existing
translation-invariance condition motivated by Corollary (7.22),
printed p.106 (PDF p.110).

This module is derived infrastructure for selecting and using a
universal family once its actual existence proposition is proved.
It does not assert existence, identify the geometric-fibre predicate
with a scheme-theoretic identity component, construct the tensor group
law, or prove the chosen scheme is abelian. In particular,
`dualScheme` is an `S`-scheme, not yet a value of `AbelianScheme S`.
Those obligations are needed before dual homomorphisms, polarizations,
and the rational homomorphism interface can be supplied.
