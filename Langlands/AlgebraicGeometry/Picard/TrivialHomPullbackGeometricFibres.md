# Trivial homomorphism pullbacks on geometric fibres

This module transports actual pullback trivializations to the geometric fibres
used by the existing `IsPicardZeroFamily` predicate. Its final theorem is a
conditional reduction of `FieldTrivialPullbackPicardZeroStatement`, not an
unconditional proof of that statement.

`AlgClosedFieldTrivialPullbackTranslationInvariantStatement` names the
remaining field criterion. For every algebraically closed field `K`, every
isogeny `f : A → B` of actual abelian schemes over `Spec K`, and every ordinary
line bundle `M` on `B`, it asserts that an actual module isomorphism
`f^*M ≅ O_A` implies `GroupScheme.IsTranslationInvariant B.toGrp M`.
This proposition is stated here and remains unproved. It names the explicit
premise of the reduction below, without asserting descent or classification.

`homPullback_familyLineBundle_trivial` starts with an actual rigidified family
`L` on `T ×_S B` and `HasTrivialHomPullback f T (forget L)`. The latter supplies
an isomorphism of the actual module pullback along `f_T` with the structure
module on `T ×_S A`. The published `homFamilyLineBundleIso` compares this
pullback, after changing the product order, with pullback of
`familyLineBundle B L` along the actual homomorphism
`(AbelianScheme.baseChange T.hom).map f`. Forgetting its line-bundle
isomorphism, pulling back the supplied trivialization along the inverse
`relativeSpaceSymmetry` for `A`, and using `pullbackUnitIso` gives the claimed
ordinary module trivialization on `A ×_S T`.

`homPullback_fibreLineBundle_trivial` has no field or isogeny assumption.
For any base change `s : V → S`, the actual base-changed homomorphism satisfies

```text
f_s ; pr_B = pr_A ; f.
```

The proof checks this identity from the slice pullback functor, applies
module-pullback composition and congruence to this square, then pulls back the
original trivialization along `pr_A`. The final pullback of a structure module
is identified with the structure module on `A ×_S V`. Thus the result concerns
the precise `fibreLineBundle` chosen by the Library, rather than a replacement
fibre.

`fieldTrivialPullbackPicardZero_of_algClosed_translationInvariant` retains an
explicit geometric input: for every algebraically closed field `K`, every
isogeny of actual abelian schemes over `Spec K`, and every ordinary line
bundle on its target, triviality of its actual homomorphism pullback implies
translation invariance. The proof applies the first lemma over an arbitrary
test scheme `T`, then the second lemma at every geometric point
`s : Spec K → T`. Isogeny stability under the two actual base changes supplies
the geometric input's isogeny hypothesis. Its conclusion is exactly the
translation invariance tested by `IsPicardZeroFamily`.

The original field `k` and test scheme `T` remain arbitrary. The transport
lemmas work over every base scheme and make no reducedness, separability,
characteristic, projectivity or dual-existence assumption. No descent or
character-classification theorem is proved here; the algebraically closed
field input remains an obligation before the final exact target can be
proved.

The provenance is internal and derived. The field criterion is the precise
sufficient input isolated by the reduction, rather than a separately numbered
literature assertion. The transport proofs compose the published
actual product-order comparison `homFamilyLineBundleIso`, module-pullback
composition and unit isomorphisms, and `IsIsogeny.baseChange`. The reduction
then unfolds the unchanged Library definitions of `familyLineBundle`,
`fibreLineBundle` and geometric Picard zero. No separately numbered
literature theorem is asserted for these transport lemmas.
