# Open Picard-zero loci and restriction of universal families

This is derived categorical and open-subscheme infrastructure over an arbitrary
`S : Scheme.{u}` and `A : AbelianScheme S`. It defines an all-test-scheme open-locus
criterion and proves that restricting an actual universal rigidified family to
such a locus gives the existing `IsUniversalPicardZero` property. Both ambient
universality and the open-locus criterion are explicit hypotheses.

## The actual open parameter scheme

For `P : Over S` and `U : P.left.Opens`, `openLocusParameter P U` has underlying
scheme `U.toScheme`, namely the restriction of `P.left` to `U`, and structure map
`U.ι ≫ P.hom`. The morphism `openLocusInclusion P U` in `Over S` has underlying
scheme morphism `U.ι`, the canonical open immersion. It is a monomorphism, and
`openLocusInclusion_range` identifies its range with `U`.

`openLocusLift` uses Mathlib's `IsOpenImmersion.lift` to factor a map `h : T ⟶ P`
whose topological range is contained in `U`. The factor is an actual morphism of
schemes over `S`: its structure-map equation follows from `lift_fac` and the
structure-map equation of `h`. `openLocusLift_fac` proves that composing it with
the inclusion recovers `h`. Conversely, `range_comp_openLocusInclusion` shows
that every composite through the inclusion has image in `U`.
`existsUnique_openLocusLift_iff` combines these facts and monomorphism cancellation
to characterize image containment by unique factorization in `Over S`.

## The all-test-scheme predicate and the restricted family

For an actual `L : RigidifiedFamily A P`, `IsPicardZeroOpenLocus A L U` is the
proposition that for every `T : Over S` and every `h : T ⟶ P`,

```text
IsPicardZeroClass A (RigidifiedLineBundle.classifyingMap … L T h)
  ↔ Set.range h.left ⊆ U.
```

Here `classifyingMap` is the existing map induced by the actual rigidified
relative pullback of `L`. `isPicardZeroClass_classifyingMap_iff` identifies its
class predicate with `IsPicardZeroFamily` on that actual pulled-back family;
this is definitional equality of the quotient operations.
`isPicardZeroOpenLocus_iff` expresses the entire predicate in those family terms.
All test schemes are retained, including nonreduced schemes. Although the
existing family predicate tests geometric fibres, the quantifiers in the locus
criterion and classification property range over all schemes and all maps.

`restrictedRigidifiedFamily A L U` is the actual `relativePullback` of `L` along
`openLocusInclusion P U`. `restrictedRigidifiedFamily_classifyingMap` identifies
its actual classifier with the original classifier after composition with the
inclusion. The proof uses `RigidifiedLineBundle.classifyingMap_comp`, supplied
with the published theorem `Langlands.SchemeModule.RigidifiedModule.pullbackCoherence`;
there is no additional coherence hypothesis.

## Conditional universality

`restrictedRigidifiedFamily_picardZero` applies the open-locus criterion to the
inclusion itself. Its range is `U`, so the actual restricted family satisfies
`IsPicardZeroFamily`.

`restrictedRigidifiedFamily_universal` assumes the existing ambient `IsUniversal`
predicate for `L` and `IsPicardZeroOpenLocus A L U`. For each test scheme `T` and
`q : PicardZeroClasses A T`, ambient universality provides the unique classifier
`h : T ⟶ P` with pullback class `q.val`. The locus criterion forces its image into
`U`, so `openLocusLift` gives a classifier into the actual open parameter scheme.
The composition law for actual rigidified pullbacks proves its classification
property. Any other classifier composes to the same ambient classifier by
ambient uniqueness, and cancellation of the open inclusion proves equality of
the two maps. The conclusion is exactly
`IsUniversalPicardZero A (restrictedRigidifiedFamily A L U)`; no restricted
classifier or representation equivalence is supplied as data.

`hasDualScheme_of_isPicardZeroOpenLocus` packages this parameter scheme, actual
restricted family and universal property into the existing `HasDualScheme A`.
The unique object in these arguments is the classifying map, not a choice of
rigidified bundle isomorphism.

## Provenance and scope

The registered original is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, source ID `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Paragraph (6.2), printed p.88 (PDF p.92), formulates the rigidified universal
bundle property by actual pullback. Chapter VI §3, printed p.95 (PDF p.99),
discusses the ambient Picard scheme and its rigidified Poincaré bundle over a
field. Theorem (6.18) and Definition (6.19), printed p.96 (PDF p.100), establish
the dual abelian variety and describe its Poincaré bundle as the restriction of
the ambient one. Corollary (7.22), printed p.106 (PDF p.110), motivates the
translation-invariance criterion used in the existing geometric Picard-zero
predicate.

The all-test-scheme open-locus predicate above is an internal interface, not a
quoted theorem from that source. The bridge is derived from the existing actual
universal-property interfaces, the proved rigidified pullback coherence, and
Mathlib's universal property of an open immersion. This module proves neither
existence of an ambient Picard scheme nor existence or openness of its
Picard-zero locus. It does not identify that locus with the connected identity
component, construct an abelian-scheme structure on the open parameter scheme,
or prove unconditional field dual-scheme existence. No field, reducedness,
smoothness or finiteness hypothesis is added to the base or to the test schemes.
