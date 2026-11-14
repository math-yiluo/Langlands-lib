# KP Proposition 11.6.1 from its Kottwitz and normalizer inputs

This is internal proof infrastructure for Task 6549. It follows
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 11.6.1,
printed page 432, PDF page 463. It is **not** an unconditional proof of
`UnramifiedChamberExactSequenceStatement`. The main theorem
`Kottwitz.unramifiedChamberExactSequence_of_statements` derives that statement
from three explicit premises:

- `ReductiveKottwitzExistenceStatement` (only its surjectivity conjunct is used);
- `UnramifiedZeroKernelStatement` (KP Proposition 11.5.4 over the maximal
  unramified field);
- `MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement` (normalizer
  elements of a simply connected group act through the affine Weyl group).

All three premises remain unproved here.

KP proves surjectivity from transitivity of `G_sc(K)` on chambers and triviality
of κ on `G_sc(K)`. They prove the second assertion from Proposition 7.6.4,
`G(K)^0_C = G(K)_C ∩ G(K)^0`. The Lean proof below does not use `G_sc(K)` or
Proposition 7.6.4 directly. It works with the Library's zero subgroup
`E.zeroPoints` of any `UnramifiedZeroDatum`. The premise
`UnramifiedZeroKernelStatement` identifies that subgroup with ker κ.

## The predicate `Kottwitz.ChamberExactSequence`

`Kottwitz.ChamberExactSequence B κ Cch` names the two conclusions of KP
Proposition 11.6.1 in the form used by `UnramifiedChamberExactSequenceStatement`.
Here `B : MaximalUnramified.BuildingData F H`, `κ : H(K) →* M` is a
homomorphism into a `MulOneClass`, and `Cch` is a subset of the reduced
building of `B`. The predicate is the conjunction of:

- surjectivity of `κ.domRestrict P`, where `P` is the setwise stabilizer
  `MulAction.stabilizer (rationalPoints H) Cch` (KP's `G(K)_C`);
- `E.zeroPoints ⊓ B.pointwiseFixer Cch = κ.ker ⊓ P` for every
  `E : UnramifiedZeroDatum F H`.

KP state the second conclusion as `G(K)_C / G(K)^0_C ≅ π₁(G)_I`, and the
target statement's equality is its kernel form. The left side,
`E.zeroPoints ⊓ B.pointwiseFixer Cch`, is the Library's form of `G(K)^0_C`.
This form follows the target statement verbatim. For
`H = baseChanged F (inertiaFixedField F) G` and
`κ = reductiveKottwitzOnBaseChange F G hG`, the target statement's conclusion
is this predicate. The predicate itself does not require `Cch` to be a chamber
or κ to be a Kottwitz map. Those are hypotheses of the lemmas below.

## Building lemmas (namespace `IntegerValuationBuildingData`)

These lemmas concern `IntegerValuationBuildingData v G` over a field `k`. In the
lemmas that mention it, `Z` is a normal subgroup of `G(k)` that contains the sharp
fixer `B.apartment.sharpFixer Ω` of every apartment subset Ω. Three of the lemmas,
the type-preservation lemma and the two transitivity lemmas, also take the
valuation hypothesis

    hunit : ∃ t : kˣ, IntegerValuation.order v t = 1,

that some unit of `k` has valuation order exactly one. This is not a field of
`IntegerValuationBuildingData`. It is used to obtain
`B.isAffineRootSystemWithRankZero_affineRoots hunit`, the input of
`affineChamberSimpleTransitivity`, and in the transitivity lemma also
`B.sharpFixer_sup_normalizer_eq_top hunit`. The two facet lemmas and
`affineWeylGroup_le_map_subgroupOf` do not take `hunit`.

- `exists_normalizer_sharp_eq_on_translated_facet`. Let `Fa` be an apartment
  facet, `a ∈ Fa`, and `g • apartmentMap a = apartmentMap b`. Then some
  normalizer element `n` has `n • a = b` and `g⁻¹ n ∈ sharpFixer Fa`. Also
  `g • apartmentMap y = apartmentMap (n • y)` for every `y ∈ Fa`. The proof reads
  `n` off the quotient relation `ApartmentQuotient.mk_eq_mk_iff`. The facet
  version `sharpFixer_eq_singleton_of_isFacet` of the sharp fixer then shows that
  `g⁻¹ n` fixes every point of `Fa`.
- `exists_normalizer_mem_stabilizes_eq_on_translated_facet`. Suppose `g ∈ Z`
  stabilizes, as a set, the translate `h • apartmentMap '' Fa` of a facet. Then
  some normalizer element `n ∈ Z` satisfies `n • Fa = Fa` and agrees with `g` on
  that translate after conjugation by `h`. Apply the previous lemma to `h⁻¹ g h`,
  which lies in `Z` by normality. Then `n = (h⁻¹ g h) · (sharp fixer element)`
  lies in `Z`. Two facets sharing a point are equal, so `n • Fa = Fa`.
- `mem_pointwiseFixer_of_mem_of_stabilizes_chamber` (type preservation). Assume
  `hunit` and `hNW`: every normalizer element in `Z` acts on the apartment
  through the affine Weyl group. Then every `g ∈ Z` that stabilizes a building
  chamber as a set fixes it pointwise. The previous lemma gives `n ∈ Z` with
  `n • Ca = Ca` that agrees with `g` on the chamber. By `hNW`, the action of `n`
  lies in the affine Weyl group. The uniqueness part of
  `affineChamberSimpleTransitivity` (from `Ca` to `Ca`), applied with the
  affine-root-system hypothesis `B.isAffineRootSystemWithRankZero_affineRoots hunit`,
  forces that action to be the identity. So `n`, and hence `g`, fixes the
  chamber pointwise.
- `affineWeylGroup_le_map_subgroupOf`. Every element of the affine Weyl group is
  the action of a normalizer element lying in any subgroup `Z` that contains all
  sharp fixers. The proof applies `exists_sharpFixer_normalizer_eq_affineReflection`
  with `Ω = ∅` to the generating reflections.
- `exists_mem_smul_chamber_eq_apartmentMap_image` and `exists_mem_smul_chamber_eq`
  (transitivity). Assume `hunit`. Then `Z` acts transitively on the chambers of
  the building. Let `g • apartmentMap '' Ca` be a chamber and `C₀` an apartment
  chamber. Then `sharpFixer_sup_normalizer_eq_top hunit` writes `g = z n` with
  `z ∈ Z` and normalizer element `n`. Simple transitivity of the affine Weyl group
  on apartment chambers (`affineChamberSimpleTransitivity` with
  `B.isAffineRootSystemWithRankZero_affineRoots hunit`) moves `n • Ca` to `C₀`.
  The previous lemma lifts that Weyl element to `m ∈ Z`. Then `m z⁻¹ ∈ Z` carries
  the given chamber onto `apartmentMap '' C₀`. For two chambers, compose one such
  element with the inverse of the other. Besides the building data, `Z`, its
  normality, the sharp-fixer containment and `hunit`, these lemmas need no
  Kottwitz input and no simply connected input.

## The exact sequence for an abstract κ (namespace `UnramifiedZeroDatum`)

`chamberExactSequence_of_zeroPoints_eq_ker` works over the maximal unramified
field. It takes building data `B` for a group `H`, any homomorphism
`κ : H(K) →* M` into a `MulOneClass`, and one zero datum `E₀`. It assumes that κ
is surjective and that `E.zeroPoints = ker κ` for every zero datum `E`. With
`hsc`, it proves `Kottwitz.ChamberExactSequence B κ Cch` for every chamber
`Cch`. The valuation hypothesis `hunit` of the building lemmas is not a premise
here: the proof obtains it from `MaximalUnramified.exists_order_eq_one F`, which
gives a unit of the maximal unramified field of valuation order one.

- Surjectivity. Given `t = κ x`, transitivity with `Z = E₀.zeroPoints` gives
  `z ∈ E₀.zeroPoints` mapping `x • Cch` back to `Cch`. This uses the Library
  facts `sharpFixer_le_zeroPoints` and `normal_zeroPoints`. Then `z x` lies in
  the stabilizer of `Cch`, and `κ (z x) = κ x` because `z ∈ ker κ`.
- Kernel equality. Fix a zero datum `E` and rewrite `ker κ` as `E.zeroPoints`.
  The pointwise fixer lies in the setwise stabilizer
  (`smul_image_eq_of_mem_pointwiseFixer`). Conversely, type preservation with
  `Z = E.zeroPoints` shows that an element of `E.zeroPoints` stabilizing `Cch`
  fixes it pointwise. The hypothesis `hNW` there is
  `E.normalizer_mem_affineWeylGroup_of_mem_zeroPoints B hsc`.

## Plumbing (namespace `Kottwitz`)

- `surjective_reductiveKottwitzOnBaseChange`: the fourth conjunct of
  `hexist F F G hG` composed with surjectivity of `baseChangeCoeffEquiv`.
- `zeroPoints_eq_ker_reductiveKottwitzOnBaseChange`: `hkernel F F G hG E`
  together with `MonoidHom.comap_ker`.
- `nonempty_unramifiedZeroDatum_baseChanged`: a zero datum built by
  `UnramifiedZeroDatum.ofDerivedCover`. It uses the published theorems
  `simplyConnectedDerivedCoverExistence` and `connectedReductiveFieldExtensionStatement`.
- `unramifiedChamberExactSequence_of_statements` introduces the data of
  `UnramifiedChamberExactSequenceStatement` and applies the abstract lemma to
  κ = `reductiveKottwitzOnBaseChange F G hG`.

The private instance `unramifiedChamberExactSequenceReductionAffineHom` repeats
the statement module's private instance: the base change of an affine group
scheme is affine. A private declaration cannot be imported, so the instance is
restated here. The three plumbing lemmas are separate declarations only to keep
each elaboration within the default heartbeat limit.

Provenance: Kaletha–Prasad, registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Proposition 11.6.1 (printed p. 432 / PDF p. 463), together with Proposition 11.5.4.
The route through sharp fixers, normalizer lifts and simple transitivity of the
affine Weyl group is an internal decomposition. It replaces KP's appeal to
`G_sc(K)` and to Proposition 7.6.4.
