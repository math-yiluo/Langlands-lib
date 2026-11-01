# Concrete locally constant sheaf transport by chosen atlas isomorphisms

Author: Worker 56.

Let `K : Type u` be a complete ultrametric normed field,
`A,B : AffinoidAtlasPresentation.{u,v,w} K`, `e : A ≅ B` a full chosen
atlas isomorphism, and `D : Type z` an arbitrary coefficient type. This
module identifies all locally constant functions on each actual image domain
with those on its source domain. The comparison is natural under actual
domain inclusions and coefficient functions. It gives an isomorphism of the
corresponding actual sheaves on the source original-domain quasinet site and
constructs their arbitrary-sieve gluing explicitly.

## Internal provenance

This is an internal construction from `ChosenAtlasDomainPresentation` and
`OriginalDomainLocallyConstantLocalization`. The first supplies the actual
restricted homeomorphism, derived from the complete bounded presentation
isomorphism on each actual original-chart domain and its image. The second
supplies the full locally constant section presheaves and sheaves, coefficient
postcomposition, and the constructed gluing on every covering sieve. No new
literature theorem is asserted.

The construction applies Mathlib's `LocallyConstant.congrLeft` to the inverse
of that actual restricted homeomorphism. It proves the restriction equations
pointwise and uses them to build a natural isomorphism. The already proved
source sheaf condition transports through this explicit isomorphism. Finally,
it maps the full compatible family through the same section maps, constructs
its source glue and applies the inverse section map. The original gluing
evaluation law and point coverage give value recovery and uniqueness.

## Actual section functions and restrictions

For an original-chart domain `S` of `A`, write `H_S` for
`isoOriginalDomainHomeomorph e S : S ≃ₜ isoOriginalDomain e S`. Its point
functions are restrictions of `e.hom.baseMap` and `e.inv.baseMap`. The complete
bounded domain presentation isomorphism constructed in the imported module
has exactly this base homeomorphism.

`isoOriginalDomainLocallyConstantEquiv e S` is the equivalence

```text
LocallyConstant (isoOriginalDomain e S) D ≃ LocallyConstant S D.
```

Its forward function sends `f` to `x ↦ f (H_S x)`; its inverse sends `g` to
`y ↦ g (H_S.symm y)`. The two evaluation lemmas record these actual values.
The inverse laws come from the homeomorphism, without choosing coefficients
or restricting the set of locally constant functions.

`isoOriginalDomainLocallyConstantEquiv_restrict` proves that restricting a
target-image section to the image of `S ≤ T` and then pulling it back equals
pulling the section back on `T` and restricting along `S ≤ T`. Both sides
evaluate at the same actual point. The `_symm_restrict` theorem proves the
inverse square by the same pointwise argument. All restrictions are the
literal subset inclusions from the existing domain presheaves.

## Presheaves, sheaves and coefficients

`isoOriginalDomainLocallyConstantPresheaf e D` assigns to `S` the full set
`LocallyConstant (isoOriginalDomain e S) D`, with actual image-domain
inclusion pullbacks. Its `_eq` theorem identifies it definitionally with

```text
(isoOriginalDomainEquivalence e).functor.op ⋙
  locallyConstantPresheaf B.atlas D.
```

`isoOriginalDomainLocallyConstant e D` packages the section equivalences and
the forward restriction equation as a natural isomorphism from this presheaf
to `locallyConstantPresheaf A.atlas D`.

`isoOriginalDomainLocallyConstant_isSheaf` transfers the already constructed
source sheaf condition through this explicit isomorphism.
`isoOriginalDomainLocallyConstantSheaf` bundles the image-domain presheaf with
that proof on the unchanged source quasinet topology. The selected entry
`isoOriginalDomainLocallyConstantSheafIso` is its isomorphism with
`locallyConstantSheaf A.atlas D`; its underlying maps are precisely the
constructed section transformations.

For every function `φ : D → E`,
`isoOriginalDomainLocallyConstant_coefficient_naturality` equates the two
natural transformations obtained by changing coefficients on the target
before pulling back or changing them on the source after pulling back.
Both orders evaluate to `φ (f (H_S x))`. The coefficient universe is independent
of the field, point and chart-index universes; the presheaves take values in
`Type (max v z)`.

## Constructed gluing on every covering sieve

Let `R` be any covering sieve on a source domain `S`, and let `p` be a full
Mathlib compatible family in the image-domain presheaf on `R`.
`isoOriginalDomainLocallyConstantSieveGlue` maps every section of `p` through
the natural comparison, obtains compatibility by naturality, constructs the
existing source locally constant glue, and applies the inverse section
equivalence on `S`. Its output is an actual locally constant function on
`isoOriginalDomain e S`; no target glue is supplied as input.

For any `f : T ⟶ S` in `R` and `x : isoOriginalDomain e T`, the `_apply`
theorem states that evaluating this glue at the literal image-domain
inclusion of `x` recovers the original value `(p f hf) x`. Its proof evaluates
the source gluing law at `H_T.symm x` and uses the homeomorphism inverse law.
The `_pullback` theorem proves that pulling the constructed image glue back
is exactly the constructed source glue of the mapped family.

The `_unique` theorem considers any amalgamation of the original full
family. At an arbitrary image point `x`, point coverage supplies a sieve
domain containing `H_S.symm x`. Its image contains the same point `x`.
Evaluating the proposed amalgamation and the recovery law there gives the
same original local value, proving equality of the entire functions.

## Scope and empty cases

No nonemptiness or coefficient topology is assumed. The imported gluing
construction obtains coefficient values from actual local sections only at
actual target points. Empty domains, empty coefficient types and the empty
covering sieve therefore remain permitted exactly when the original sheaf
and covering definitions permit them. The new equivalences introduce no
default value or extra existence assumption. No strict-radius, reducedness
or nontrivial-valuation hypothesis is added.

The input is a full chosen atlas isomorphism. These are concrete sheaf and
function comparisons on its fixed-original-chart domain sites. Arbitrary
refinement comparisons, a general equivalence of sheaf categories,
identification with a categorical constant sheaf, the full analytic or etale
sites, and the Harris tower remain separate constructions.
