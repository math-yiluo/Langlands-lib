# Actual target-sieve gluing and chosen atlas pullback

Author: Worker 56.

Let `K : Type u` be a complete ultrametric normed field,
`A,B : AffinoidAtlasPresentation.{u,v,w} K`, and `e : A ≅ B` a full chosen
atlas isomorphism. Let `D : Type z` be an arbitrary coefficient type. This
module constructs the matching family and source glue for the functorial
pullback of any actual target covering sieve on an image domain. It proves
that the resulting glue is exactly the pullback of the original target-site
glue, recovers every original target local value after transport back, and
commutes with coefficient postcomposition.

## Internal provenance

This is an internal companion to `ChosenAtlasLocallyConstantTransport`.
That module constructs the actual section equivalences and natural
transformation, and constructs gluing for image-domain sections indexed by
an arbitrary source covering sieve. The present module starts instead with
an arbitrary sieve on the actual target domain and its full original target
matching family. No new literature theorem is asserted.

Mathlib's `Presieve.FamilyOfElements.functorPullback` evaluates the target
family at mapped arrows; its compatibility theorem applies the original
matching equation to the mapped commuting square. Mapping through the
existing natural section comparison gives a genuine matching family on the
source. The existing covering equivalence supplies the covering condition,
and the existing locally constant gluing construction gives its source
glue. Uniqueness from the preceding image-section gluing construction
identifies its transport back with the literal original target glue. The
section equivalence then gives the forward comparison. All coefficient
equations follow from actual pointwise postcomposition and the proved
coefficient compatibility of the original target gluing.

## Actual pulled-back matching family

Write `F := (isoOriginalDomainEquivalence e).functor`, let `S` be an
original-chart domain of `A`, and let `R` be any sieve on
`isoOriginalDomain e S`, which is definitionally `F.obj S`. For a full
Mathlib family `p` in `locallyConstantPresheaf B.atlas D` on `R.arrows`,
`isoOriginalDomainLocallyConstantPullbackFamily e p` is a family in
`locallyConstantPresheaf A.atlas D` on `(R.functorPullback F).arrows`.

It is constructed by `p.functorPullback F` followed by the forward natural
section transformation from `ChosenAtlasLocallyConstantTransport`. For an
arrow `f : T ⟶ S` of the pulled-back sieve and an actual point `x : T`, its
`_apply` theorem states the literal value

```text
(p (F.map f) hf) (isoOriginalDomainHomeomorph e T x).
```

This is precomposition by the actual restricted chosen base map, with no
replacement of the original target family or restriction maps.
`isoOriginalDomainLocallyConstantPullbackFamily_compatible` derives
compatibility from that of `p`, first by Mathlib's functorial pullback
and then by naturality of the section transformation.

`isoOriginalDomain_functorPullback_isCovering` derives the covering
condition for `R.functorPullback F` directly from the proved
`isoOriginalDomain_functorPullback_mem_iff` and the original `IsCovering R`.
The covering condition retains the original quasinet topology; it is not
replaced by pointwise surjectivity.

## Constructed glues and exact comparison

For `hp : p.Compatible` and `hR : IsCovering R`, the selected entry
`isoOriginalDomainLocallyConstantPullbackGlue e p hp hR` is the existing
`locallyConstantSieveGlue` applied to the constructed source matching
family, its derived compatibility and the derived source covering proof.
It is an actual element of `LocallyConstant S D`. Its `_apply` theorem
recovers the displayed local value along the literal source inclusion
`Set.inclusion (leOfHom f)` for every member of the pulled-back sieve.

`isoOriginalDomainLocallyConstantImageGlue_eq_target` first identifies two
actual functions on `isoOriginalDomain e S`. The first is the preceding
module's image-section glue for `p.functorPullback F` on the source sieve;
the second is the literal original `locallyConstantSieveGlue p hp hR` on
the target site. For every mapped source arrow, the target glue's original
recovery law makes it an amalgamation of that image-section family.
The preceding module's uniqueness theorem therefore proves equality of
these complete functions.

`isoOriginalDomainLocallyConstantSieveGlue_functorPullback` applies the
actual section equivalence to this equality and uses the preceding
module's exact source-glue pullback law. It proves

```text
isoOriginalDomainLocallyConstantEquiv e S
    (locallyConstantSieveGlue p hp hR)
  = isoOriginalDomainLocallyConstantPullbackGlue e p hp hR.
```

`isoOriginalDomainLocallyConstantPullbackGlue_descend` applies the inverse
section equivalence and its inverse law, recovering the entire literal
original target glue from the constructed source glue.

The `_target_apply` theorem uses this equality to recover `(p f hf) x`
for every original target arrow `f : T ⟶ isoOriginalDomain e S` in `R`
and every `x : T`. The target domain `T` is arbitrary; the theorem does not
require it to be presented as the direct image of a source domain. Its
proof rewrites to the original target glue and uses that glue's original
local recovery law.

## Coefficients and empty cases

For every function `φ : D → E`, with `E : Type z`,
`isoOriginalDomainLocallyConstantPullbackFamily_map` proves equality of
whole matching families: changing target coefficients before pullback is
the same as pulling back and changing source coefficients. Evaluating any
member at any point gives `φ` applied to the same original local value.

`isoOriginalDomainLocallyConstantPullbackGlue_map` proves the analogous
equality of complete constructed source glues. The proof uses the exact
target-to-source gluing comparison for both coefficient types, evaluates
at the actual image point, and applies the existing target theorem
`locallyConstantSieveGlue_map`. Thus no gluing compatibility is assumed
for either coefficient system.

The coefficient universe is independent of the field, point and chart
index universes. No coefficient topology, default value or nonemptiness
hypothesis is added. Empty domains, coefficient types and covering sieves
remain permitted exactly when the imported covering and matching-family
definitions permit them. The construction uses all locally constant
functions and all original target covering sieves on each image domain.

The input is a full chosen atlas isomorphism, and both sites are the
existing fixed-original-chart quasinet sites. General sheaf-category
comparisons, non-isomorphic atlas refinements, the full analytic and etale
sites, and the Harris tower remain separate constructions.
