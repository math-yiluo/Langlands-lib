# Actual saturated domain objects and image-only codomain restriction

This module constructs the literal subspace object of an original-chart
analytic domain in a saturated atlas presentation, and proves its unique
factorization property in the category with source-refinement quotient Homs.
It constructs the additional source refinement and all bounded algebra maps.
The factor object, the localized lift and their universal properties are
outputs of the construction.

The coefficient field `K : Type u` is complete, normed and nonarchimedean.
The ambient spaces and chart indices have independent universes `v` and `w`.
All spectra and full affinoid-domain tests remain those of the imported
positive-polyradius presented affinoid algebras. Reducedness, strictness and
ambient Hausdorffness are not assumed.

## Source and scope

The original geometric convention is Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`, Definition 1.3.1 and the paragraph immediately
after it, printed p.23 / PDF p.20. There an analytic domain has finite relative
neighborhoods formed by contained affinoid domains. Its contained affinoid
domains supply an atlas, and its inclusion has unique factorization for every
morphism whose image is contained in the domain.

The implementation is a derived construction in the current model. Here
`S : B.presentation.atlas.OriginalChartDomain` uses the contained **original**
charts and their finite relative neighborhoods. `B.hasAllLocalDomains` asserts
closure under every full local affinoid domain of an original chart. It does
not assert maximality under finite affinoid gluing. Consequently the theorem
here establishes the image-only universal property for these concrete domain
objects in `SourceCategory`; it does not identify that category or this domain
class with the complete category and domain class of the cited literature.
The atlas and full strong-map conventions are inherited from the imported
modules, corresponding to Berkovich Definition 1.2.3, Remark 1.2.4(i), and
Definition 1.2.7, printed pp.16 and 18 / PDF pp.13 and 15.

## The actual domain atlas

`IndexedAffinoidAtlas.subspaceAtlas_hasAllLocalDomains` proves that the existing
subspace atlas retains closure under full local domains. A local domain of a
contained original chart is also a local domain of that same ambient chart.
Ambient saturation supplies an original index with the required range, which
is contained in `S`. The corresponding subspace chart has exactly the local
domain's range. The reverse containment of the families uses whole-chart
domains.

`SaturatedAtlasPresentation.originalDomain B S` bundles the existing literal
subspace presentation with that proved saturation. Its space is `S.carrier`
with the induced topology. Its indices are exactly the original indices whose
chart ranges lie in `S`; each algebra and each bounded restriction is the
original one at the underlying index.

`originalDomainInclusion` is the existing full strong subspace inclusion. Its
continuous map is subtype inclusion, and its pullbacks are all admissible
original bounded restrictions. `originalDomainInclusion_comp_pullback` proves
that composing any full strong map into this domain with the inclusion
recovers the entire original pullback at each contained target chart. The
proof applies the constructed saturated composition formula, then the bounded
restriction identity and bounded algebra homomorphism identity law.

## Constructing a source refinement from the image condition

For a full strong map `f : A ⟶ B` and only the point-image condition
`∀ x, f.baseMap x ∈ S`, `sourceSelectionForDomain_locallyRefining` proves that
the source charts whose images fit in a target chart contained in `S` form a
locally refining selection.

Fix a source chart and one of its admissible target charts `j`. Intersect
`S` with the range of `j`. The original-domain condition supplies a finite
family of contained target charts, each containing the image point, whose
union is a relative neighborhood. Pull each member back and intersect with
the fixed source chart. Each resulting set is a full local domain by the
previously constructed inverse-image domain theorem. Source saturation
realizes it as an actual original source chart with the required target
containment. Continuity pulls the finite target neighborhood back to a
relative source neighborhood. This proves the refinement condition without
assuming any codomain-restricted strong map.

`domainSourceSelection` packages this selection and its downward closure.
`domainBaseMap` restricts the continuous map's codomain to `S.carrier`.
`domainBaseMap_admissible_iff` identifies chart admissibility for this subtype
map with the original admissibility at the underlying target index.
`domainFactor` now constructs a full strong map from the same-space refining
subpresentation to `B.originalDomain S`. Target-chart existence comes from
the selection; every admissible pullback is literally `f.pullback` at the
underlying indices, as stated by `domainFactor_pullback`. Full two-variable
naturality is inherited from `f`.

`domainFactor_comp_inclusion` proves equality of the complete strong arrows:

```text
domainFactor f S himage ≫ originalDomainInclusion B S
  = refiningSubatlasInclusion A (domainSourceSelection f S himage) ≫ f.
```

The proof compares the continuous maps and, at each source chart, the whole
bounded pullback to a selected contained target chart. The inclusion formula
and the identity restriction on the source give the same bounded map. The
previous saturated full-map extensionality theorem then gives equality.
`originalDomainInclusion_mono` uses the same pullback formula to cancel the
inclusion. It compares full bounded maps, including any information their
maps on spectrum points do not determine.

## Unique factorization after source localization

`sourceHomComp_ι_strong` proves that postcomposing a source representative by
an original full strong map retains the same source selection and composes
its numerator. The proof uses the Hom comparison with the path localization,
functoriality, and its inverse laws.

`SourceCategory.domainInclusion` is the actual full inclusion mapped into the
source-quotient category. `domainInclusion_mono` proves it is monic there.
Choose representatives for two arrows; equality after postcomposition gives
equality of their complete strong numerators on a common source refinement.
Strong monicity cancels the inclusion on that refinement. The proved
common-source criterion then gives equality of the quotient arrows.
Faithfulness of the original localization functor is not a premise.

`exists_domainFactor` takes any quotient arrow `F` with
`∀ x, spaceFunctor.map F x ∈ S`. Quotient induction gives a source selection
`P` and a full numerator `f`. Since the denominator has the literal identity
map on the ambient space, the image condition is exactly the one for `f`.
Apply the constructed domain source selection once more, obtaining `Q`.
The resulting right fraction has denominator the composite of the `Q` and
`P` source inclusions and numerator `domainFactor f S himage`.
`sourceHomOfFraction` normalizes it to an original-source quotient class.
The Hom comparison, cancellation of the localized denominator, the full
factorization triangle and the right-fraction inverse law prove the desired
quotient triangle. `existsUnique_domainFactor` then uses the proved quotient
monicity for uniqueness.

`domainLift` chooses this proved factor; `domainLift_comp_inclusion` is its
triangle. `domainLift_apply` proves that the lift's underlying continuous
map is exactly the subtype-valued original map. Finally `domainHomEquiv`
identifies arrows into the constructed domain with the subtype of ambient
arrows whose image lies in `S`. Its forward map is postcomposition with the
actual inclusion, its inverse is `domainLift`, and monicity and the triangle
prove the inverse laws.

This unit constructs no new finite-gluing saturation, analytic gluing,
etale or quasi-etale morphism class, site, equivariant site, compact or
distinguished domain class, or Harris tower specialization. Those remain
obligations of the surrounding task.
