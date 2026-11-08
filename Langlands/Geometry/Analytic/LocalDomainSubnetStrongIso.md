# Direct strong isomorphism for arbitrary local-domain subnets

Author: Worker 36.

Fix a literal net `σ` of local affinoid domains of an actual atlas `A`.
This module constructs an actual isomorphism in the category of saturated
affinoid atlas presentations. It goes from the full recognition atlas of the
selected local-domain subnet presentation to the full recognition atlas of
`A`. Both directions have a bounded pullback on every admissible pair of
recognized charts, and both ambient maps are the literal identity of
`A.space`. Both compositions equal the entire strong identity, including all
bounded algebra maps.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are:

- Definitions 1.2.7 and 1.2.9, printed pp.18–19 / PDF pp.15–16, defining
  strong morphisms and quasi-isomorphisms through actual affinoid charts and
  affinoid domains;
- the passage after Proposition 1.2.10, printed p.20 / PDF p.17. It defines
  analytic spaces as the category of fractions with respect to
  quasi-isomorphisms. It writes `σ ≺ τ` when `σ` is a net contained in the
  local-domain enlargement of `τ` (the bar notation), and states that such a
  net gives an atlas with net `σ` and a canonical quasi-isomorphism to the
  original;
- Proposition 1.2.13, printed p.21 / PDF p.18, on recognized affinoid domains
  of subnets, canonical restrictions and recognition idempotence.

Proposition 1.2.13(i) identifies the recognized families of `σ` and `τ`.
For the stated subnets, this module upgrades that identification to an
explicit strong isomorphism of the constructed full recognition presentations.
It is a derived construction. Its inputs are the recognition equivalence and
the two natural isomorphisms of bounded affinoid diagrams from
`LocalDomainSubnetRecognition`, together with the saturated strong category
from `FullRecognitionStrongInverse`. It is not a verbatim source formula, and
it does not claim the unrestricted morphism correspondence of
Proposition 1.2.15.

## Inputs and notation

Let `K : Type u` be a complete ultrametric normed field and let `A` be an
`AffinoidAtlasPresentation.{u,v,w} K`. Let
`hσ : A.atlas.IsLocalDomainSubnet σ`, meaning that `σ` is a net on `A.space`
contained in `A.atlas.localDomainFamily`. The module writes

- `S` for `A.localDomainSubnetPresentation σ hσ`, the canonical inherited
  presentation with chart family exactly `σ`, on the unchanged ambient space;
- `F` and `G` for the forward and inverse functors of the actual equivalence
  `A.localDomainSubnetRecognitionEquivalence σ hσ` between recognized subsets
  of `S.atlas.saturatedAtlas` and of `A.atlas.saturatedAtlas`.

The imported locus lemmas give `(F V).locus = V.locus` and
`(G W).locus = W.locus`. Both sides of the final isomorphism are
`SaturatedAtlasPresentation.ofFullRecognition` objects, in
`SaturatedAtlasPresentation.{u,v,v} K`. Their charts are all recognized
subsets, with their actual finite presented algebras, Banach spectra and full
bounded restriction maps. Each carries its proved full local-domain closure.

## Forward bounded comparison

`forwardAlgebraEquiv V : V.algebra ≃ (F V).algebra` is the bounded algebra
equivalence formed from the mutually inverse components of
`A.localDomainSubnetRecognitionAffinoidNatIso σ hσ` at `V`.
`forwardAlgebraEquiv_naturality` restates naturality of that natural
isomorphism as an equality of entire bounded algebra maps for every
inclusion `U ⟶ V`.

`forwardNatIso_over_ambient` proves that the comparison lies over the
identity ambient map: on spectra, it is compatible with the two charts.
The proof composes the existing ambient formulas for the general
recognized-image comparison and for full-recognition idempotence;
`forwardAlgebraEquiv_chart` restates it through the contravariant spectrum
homeomorphism.

For every source `V`, every target `W` and every inclusion
`V.locus ⊆ W.locus`, `forwardPullback V W` is

```text
forwardAlgebraEquiv(V).symm ∘ restriction(F V, W) : W.algebra → V.algebra.
```

The restriction exists because `F V` has the same locus as `V`.
`forwardPullback_chart` proves `W.chart (comap p x) = V.chart x` for every
spectrum point. It uses the canonical restriction chart equation, the
ambient formula above, and cancellation of the spectrum homeomorphism.
`forwardPullback_naturality` quantifies over all nested sources `U ⊆ V` and
targets `W ⊆ Z` with both admissibility inclusions, and proves the equality of
bounded algebra maps

```text
restriction(U,V) ∘ p(V,Z) = p(U,W) ∘ restriction(W,Z).
```

At each algebra element, injectivity of the comparison at `U` reduces it to
whole-map naturality, the inverse laws and two canonical
restriction-composition laws. No algebra-map equality is inferred from
spectrum points. `forwardPullback_represents` transports the full
restriction universal property through the bounded equivalence using
`Represents.postcomp_equiv`, on the domain `W.chart ⁻¹' V.locus`. This
retains closedness, the exact spectrum image, and unique bounded
factorization for every presented-affinoid coefficient test.

The lemmas `ambient_image_range_chart`, `locus_subset_of_ambient_image` and
`ambient_image_subset_forward_range` identify the identity-map image of a
chart range with the recognized locus. They are needed because the selected
space is definitionally, though not syntactically, the original space.

`forward` is the resulting
`StrongHom S.fullRecognitionPresentation A.fullRecognitionPresentation`.
Its base map is `ContinuousMap.id A.space`, recorded by `forward_baseMap`.
Its chosen containing target for `V` is `F V`, and its pullback on every
admissible pair is `forwardPullback`. `forward_isQuasiIso` combines the
identity homeomorphism with the representation law at every admissible pair.

## Reverse bounded comparison

`reverseAlgebraEquiv W : W.algebra ≃ (G W).algebra` comes in the same way from
`A.localDomainSubnetReverseRecognitionAffinoidNatIso σ hσ`. That natural
isomorphism was built from the inverse forward comparison and the actual
counit of the equivalence. `reverseAlgebraEquiv_naturality` is its whole-map
naturality.
`reverseAlgebraEquiv_chart` proves the identity-ambient chart equation. It
identifies the reverse spectrum map definitionally with the counit spectrum
map after the inverse forward spectrum map. It then applies the counit chart
naturality and `forwardAlgebraEquiv_chart` at `G W`.

`reversePullback W V = reverseAlgebraEquiv(W).symm ∘ restriction(G W, V)` is
defined for every inclusion `W.locus ⊆ V.locus`. Its chart equation,
all-pair naturality and full representation on `V.chart ⁻¹' W.locus` are
proved as in the forward case: `reversePullback_chart`,
`reversePullback_naturality` and `reversePullback_represents`. The reverse
image lemmas `reverse_ambient_image_range_chart`,
`locus_subset_of_reverse_ambient_image` and
`reverse_ambient_image_subset_range` play the same role as above.

`reverse` is the resulting
`StrongHom A.fullRecognitionPresentation S.fullRecognitionPresentation`, with
base map `ContinuousMap.id A.space` (`reverse_baseMap`), containing target
`G W` and pullback `reversePullback` on every admissible pair.
`reverse_isQuasiIso` proves that it is a quasi-isomorphism.

## Entire strong inverse identities

`reversePullback_inverse` proves that the reverse pullback at the pair
`W, G W` is the entire bounded map `reverseAlgebraEquiv(W).symm`, since the
canonical self-restriction is the identity.

`reverse_comp_forward` proves that `reverse` followed by `forward`, under the
saturated strong composition, equals
`StrongHom.id A.fullRecognitionPresentation`. The ambient maps agree
definitionally. `StrongHom.ext_of_saturated` reduces equality of strong maps
out of the saturated source to one admissible target per source chart. For
`W`, the target is `W` itself through the intermediate chart `G W`, computed
by `saturatedComp_pullback`. The resulting bounded map is the counit
restriction after the forward comparison, its inverse, and the restriction
from `F (G W)` to `W`. The inverse law and the restriction-composition law
identify it with the identity restriction of `W`. Extensionality then
recovers every other admissible pullback.

`forward_comp_reverse` proves the other entire identity,
`StrongHom.id S.fullRecognitionPresentation`. It postcomposes by the forward
quasi-isomorphism and uses associativity, the preceding identity and the two
unit laws. It then applies `IsQuasiIso.cancel_saturatedComp`. That
cancellation rests on the full relative-domain uniqueness property and
saturated-source extensionality, so all bounded algebra information is kept.

`strongIso` packages these as the categorical isomorphism

```text
SaturatedAtlasPresentation.ofFullRecognition S ≅
  SaturatedAtlasPresentation.ofFullRecognition A
```

with `hom = forward` and `inv = reverse`. The simp lemmas
`strongIso_hom_baseMap` and `strongIso_inv_baseMap` record that both ambient
maps are `ContinuousMap.id A.space`.

## Scope

The only inputs are the actual atlas `A`, the set `σ` and the proof `hσ`.
There is no closure, local refinement, directedness, cofinality, global
Hausdorffness, nontrivial-valuation, reducedness or nonemptiness premise.
Neither the original atlas nor the subnet needs closure under local domains;
only the constructed full recognition atlases supply it. No composite
recognition iteration is introduced, because the comparison is built
directly from the `LocalDomainSubnetRecognition` diagrams.

The construction concerns the canonical inherited presentation of the subnet.
Comparisons for arbitrary equivalent nets or for arbitrary alternative
algebra assignments on the same subsets are not claimed here. Maximal-atlas
uniqueness, unrestricted analytic morphism identification, the analytic étale
and quasi-étale sites and Harris specializations also remain further work.
