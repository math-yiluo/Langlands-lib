# An fpqc isomorphism cover for a generically isomorphic DVR pair

This internal construction combines the published
`strictHenselianDvrExtension` and `strictHenselianGenericIso` theorems.
It derives local isomorphism from the given generic isomorphism without
asserting that the full Isom functor has a representing scheme.

`FpqcGroupIsomorphismCover` records an actual base scheme, a flat,
surjective, quasi-compact morphism to the original base, and an actual
isomorphism between the two pulled-back groups. Its `cover` construction
packages the same morphism as a singleton cover in the fpqc precoverage.

For a domain DVR `R`, a specified fraction field `K`, and reductive
groups with a given generic-fibre isomorphism,
`genericFpqcIsomorphismCover` first chooses the published faithfully
flat strictly Henselian domain DVR extension `A` in the same universe.
Write `L` for the fraction field of `A`. The injection from `R` into `L`
extends uniquely to a field map from `K` into `L`. The two scalar towers
give the same map from `Spec L` to `Spec R`. The published composition
comparisons for base change therefore transport the specified generic
isomorphism to an isomorphism of the generic fibres of the groups over
`A`. The strictly Henselian generic-isomorphism theorem produces an
actual isomorphism over `A`. Faithful flatness supplies flatness and
surjectivity of `Spec A` over `Spec R`, and this affine morphism is
quasi-compact.

The generic isomorphism is used to obtain local nonemptiness; the
isomorphism over `A` need not recover that particular generic
isomorphism. The base `R` has no Henselian, completeness, splitting,
residue-field, or characteristic restriction beyond the stated domain
DVR hypotheses.

`exists_etaleCover` is explicitly conditional on the published
`ReductiveFpqcLocalIsomorphismStatement`. It applies that supplied
fpqc-to-etale assertion to the singleton cover and its isomorphism.
This module does not prove that assertion, etaleness of the strictly
Henselian cover, or representability of the Isom functor. Those remain
separate obligations.
