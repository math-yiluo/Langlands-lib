# Valuation axioms under actual derived pullback

Authors: Worker 27 and Worker 1631. Worker 1631 supplied the
`DerivedRootTransport` support and the earlier central-isogeny transfer
infrastructure used in this construction.

Over a field `k : Type u`, let `d : D ⟶ G` be a supplied actual derived
inclusion. The group `D` is affine and locally of finite type, and `G` is
affine and smooth. Retain the supplied split tori `T`, `S`, `A`, maps
`e : T ⟶ S`, `c : A ⟶ S`, `j : T.toGrp ⟶ D`, `i : S.toGrp ⟶ G`, and
commuting square

`j ≫ d = CommGroupScheme.groupHom e ≫ i`.

The underlying scheme maps of `j` and `i` are monomorphic. The ambient
embedding `i` is assumed to be a maximal split torus. The actual product
of `e` and `c` is flat and surjective on schemes, and the composite of
`c` with `i` is central in `G`. These structural objects and properties
are inputs; their existence is not proved here.

The definition `derivedValuationPullback` sends an actual ambient
valuation, expressed as a subtype of `RootFunctionFamily S G`, to an
actual source valuation in the corresponding subtype of
`RootFunctionFamily T D`. Its underlying family is the existing
normalized `RootFunctionFamily.derivedPullback`.
The theorem `derivedValuationPullback_val` proves this formula by
reflexivity. The source valuation proof is
`IsRootDatumValuation.derivedPullback_isRootDatumValuation`, which
establishes every field of the original V0–V5 predicate.

The character-comparison helper
`derivedRoot_mem_iff_of_central_vanishing` preserves and reflects actual
root membership for any ambient character trivial on the central factor.
For reflection, use the actual root bijection; for the converse comparison,
the product detects a character whose restriction to both factors is zero.
The evaluation lemma `derivedPullback_apply_character` extends the
original root-value formula to such characters outside the root support,
using normalization. This is used for negative roots and root combinations.

V0 and V1 follow from the original root-point equivalence, exact filtration
images and the ambient valuation. The value images on corresponding root
groups agree. Identity, multiplication and inversion transfer through the
original group homomorphism, and the infinity criterion uses injectivity
on root points. The definition `derivedPullbackRootFiltration` bundles
the resulting actual filtration as a subgroup.

The normalizer-action helpers compare the actual chosen torus
automorphisms and derive compatibility of their character Weyl actions
and full real cocharacter actions. The lemma
`realizesReflection_derivedNormalizerMap` sends a source reflection to an
ambient reflection. To check the full fixed hyperplane, decompose every
ambient real cocharacter into retained and central images. The source
reflection fixes the retained component in the kernel of its root, and
the ambient normalizer fixes the central component. Thus the transferred
reflection satisfies both clauses of the original `RealizesReflection`
predicate.

V2 now uses that actual forward normalizer and the ambient valuation's
constant reflection displacement. V3 maps the source commutator subgroup
and its generating filtrations into their exact ambient counterparts.
Character restriction carries any ambient negative-ray relation to the
source, so the source side condition implies the needed ambient one.
Positive root combinations vanish on the central factor, allowing their
root membership and filtration images to be compared exactly.
Injectivity of the actual derived rational-point map then reflects
membership in the generated subgroup.

V4 transfers the double-root equation using the original positive-multiple
root-group inclusion and the character-comparison helper. V5 maps the
given opposite-root factors and their actual normalizer product into the
ambient group. The negative character is nonzero and centrally trivial,
so the existing all-test derived root-point equivalence applies to it
without assuming a separate root-negation theorem or existence of pairs.

Finally, every source root is a restriction of an actual ambient root.
The full predicate is assembled from the corresponding local proofs.
No additional valuation axiom is assumed for the source.

This is an internal transfer of the published valuation predicate,
adapting the earlier central-isogeny construction to the actual monic
derived inclusion. The original tori and product, full-centralizer V6
compatibility, a source apartment, opposite-pair
existence, and the final simply connected normalizer theorem remain
separate obligations.

`IsSplitTorusCompatible.derivedPullback` transfers the split-torus part of
V6 with the same scalar function `ω : kˣ → ℝ`. It needs the supplied
derived diagram and split central-complement product; the two acting maps
need not be monic for this lemma. The proof preserves source root-group
membership under torus conjugation, maps conjugation through the commuting
square, and uses naturality of the actual character evaluation.
`DerivedApartment` imports this result for its apartment construction.

The integrated valuation map and V0–V5 helpers retain the published
implementations and signatures. The accepted alternative character helpers
are represented by the existing `derivedRoot_mem_iff_of_central_vanishing`
and `RootFunctionFamily.derivedPullback_apply_character`; their central
vanishing hypotheses and conclusions coincide.
