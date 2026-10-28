# Actual dual-kernel points and trivial-pullback bundle classes

This module compares the existing Poincaré representative of a point in the
scheme-theoretic dual kernel with actual line-bundle isomorphism classes
whose homomorphism pullback is trivial. It works over any base scheme `S`
for actual abelian schemes `A`, `B` and a homomorphism `f : A → B`.
It constructs no character in place of the existing normalized character.

The module supplies a comparison equivalence under an explicit geometric
Picard-zero criterion, and an assembly lemma under that criterion and
bijectivity of the existing class character. It proves neither geometric
hypothesis. In particular, it does not prove the final field kernel-duality
statement. The separate field prerequisites must be proved before this
assembly can discharge that statement without extra assumptions.

## Rigidifying an ordinary bundle with trivial pullback

`trivialHomPullbackRigidifiedFamily` takes an actual line bundle `L` on
`T ×_S B` and the existing condition `HasTrivialHomPullback f T L`.
Choose an actual module trivialization `α : f_T* L ≅ O_(T ×_S A)` from
that existence condition. Pull back `α⁻¹` along the identity section of
`A_T`. The homomorphism carries this section to the identity section of
`B_T`, so the canonical pullback comparisons give the rigidification
`O_T ≅ e_B* L`. The underlying bundle remains exactly `L`, as recorded by
`trivialHomPullbackRigidifiedFamily_forget`.

`trivialHomPullbackRigidifiedFamilyPullbackIso` proves that the resulting
rigidified family's homomorphism pullback is trivial as a rigidified
family. It uses the published adjustment of a module trivialization along
a section with a retraction. No descent argument enters this construction.

## Actual kernel points and injectivity

The dual constructions use the exact existing `HasDualScheme` witnesses,
Picard-zero pullback stability, tensor comparison and coherence
propositions, and inverse line bundles with evaluation isomorphisms.
These are the constructor inputs of the existing dual group-scheme map.
Both kernels are the existing scheme-theoretic kernels.

`dualKernelPointOfOrigin` lifts an actual dual point satisfying the origin
equation into this actual kernel by `GroupScheme.kernelPointsEquiv`.
Its inclusion is the original point, by `dualKernelPointOfOrigin_ι`.
The proof identifies the group unit with the chosen dual origin through
the canonical terminal map.

`dualKernelPointPullbackClass` sends a kernel point to the underlying
Poincaré bundle class with trivial homomorphism pullback. Its definition
uses exactly `dualKernelPullbackClass`, with the origin equation already
proved for actual kernel points.

`dualKernelPullbackClass_injective` first considers dual points satisfying
that equation. Equality of their bundle classes gives an isomorphism of
underlying line bundles by effectiveness of the isomorphism-class quotient.
The published `RigidifiedLineBundle.isoOfCarrierIso` adjusts it to an
isomorphism of rigidified bundles, using the relative projection as a
retraction of the identity section. Their Picard-zero classes are equal,
so injectivity of Poincaré classification identifies the dual points.
`dualKernelPointPullbackClass_injective` then uses the monomorphic kernel
inclusion to identify the actual kernel points. These injectivity lemmas
require no isogeny or descent hypothesis.

## Surjectivity under the geometric criterion

For a fixed test scheme `T`, the explicit geometric hypothesis is:

```text
for every actual rigidified family L on T ×_S B,
  HasTrivialHomPullback f T (forget L) implies IsPicardZeroFamily B L.
```

`exists_dualKernelPullbackClass` applies quotient induction to an arbitrary
trivial-pullback bundle class. Rigidify its representative by the first
construction, apply the stated criterion, and classify the resulting
Picard-zero family using the actual chosen dual. The universal property
gives an isomorphism between its Poincaré representative and the rigidified
family. Its homomorphism pullback is therefore trivial as a rigidified
family. The published `dualSchemeMap_eq_origin_iff` turns that
trivialization into the required origin equation. Forgetting rigidification
shows that the original unrigidified bundle class has been recovered.

`dualKernelPointPullbackClass_surjective` lifts that origin equation into
the scheme-theoretic kernel. Together with injectivity, it constructs
`dualKernelPointPullbackClassEquiv`. Its forward map is the actual class
map just described; the inverse is obtained from its proved bijectivity.
No arbitrary comparison equivalence is supplied as data.

## Comparison with the normalized character

`dualKernelPointCharacter_eq_classCharacter` records that the existing
`dualKernelPointCharacter` is definitionally the existing normalized
`trivialHomPullbackClassCharacter` composed with the actual class map.
Thus the orientation and normalization remain those of the imported
intrinsic character.

`dualKernelPointCharacter_bijective_of_classification` composes the
comparison equivalence with bijectivity of that specific class character.
This is a conditional assembly lemma: its two geometric/descent premises
are explicit. Applying it with independently proved field prerequisites
is separate work. The module imposes no restriction on the test scheme,
so this comparison preserves nonreduced parameters and inseparable field
extensions whenever the premises hold there.

## Provenance and limits

These are derived comparison constructions using the published module
pullback, rigidification adjustment, effective isomorphism-class quotients,
scheme-kernel point equivalence and universal Poincaré classification.
The motivating source is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft built 2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VII, proof of Theorem (7.5), printed p.100 / PDF p.104, uses the
representatives with trivial isogeny pullback. Here rigidification and the
actual representing universal property implement that representative
comparison. The implementation uses the existing section retraction to
adjust bundle isomorphisms; it does not formalize the source's ordinary
relative-Picard quotient argument.

Effective descent, bijectivity of the intrinsic class character, and the
geometric Picard-zero criterion are not proved in this module. There is no
new axiom, final duality proof, dual existence result, dual-isogeny theorem,
arbitrary-base kernel-duality assertion or pairing-perfectness claim.
