# Finite original local-domain refinements inside recognized charts

Author: Worker 36.

This module constructs a finite cover of every full affinoid domain in a
recognized chart by actual local domains over the supplied atlas. Applied to
the recognition atlas of the enlarged full local-domain atlas, it constructs
pieces over the original input atlas, with unchanged intersection quotient
algebras and explicit bounded structural maps.

The original motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Proposition 1.2.13(ii)–(iii), printed p.21 / PDF p.18,
for domain inclusions and iteration of recognition, and Definition 1.3.1
and the following paragraph, printed p.23 / PDF p.20, for contained affinoid
domains and their induced atlases. Registered source
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These original pages were read for this unit; no source-specific errata file
was found in the available project and Library locations.

This is a derived finite-refinement construction from the existing full
affinoid-domain intersection and relative-representation constructions.
It is not a separately numbered theorem in the source, and it does not
establish the source's entire recognition closure or idempotence assertion.
The hypotheses are the three existing recognition conditions, not an assumed
cover of the new domain by original local domains.

For `V : a.RecognizedSubset`, put `A = V.algebra`, and let
`D : Domain K A`. The recognition witness supplies a finite cover by full
domains `Cᵢ = V.property.componentDomain i`, whose algebras are the original
`a.algebra (V.property.cover.index i)`. Its structural bounded maps recover
those original charts under `V.chart`.

`domainAmbientMap` composes the actual structural spectrum map of `D` with
`V.chart`; `domainLocus` is `V.chart '' D.locus`. The range theorem uses the
full representation's range equality. The embedding theorem composes the
proved full-domain spectrum embedding with the recognized chart embedding.

`domainComponentIntersection` constructs `D.inter Cᵢ` using the imported
affinoid pushout quotient of the actual bounded maps from `A`. It represents
the literal intersection `D.locus ∩ Cᵢ.locus`. The two relative
representations keep exactly that quotient algebra:

- `domainFiniteCover` regards it as a full domain over `D.algebra` using
  the left quotient leg.
- `domainLocalPiece` regards it as a full domain over the unchanged original
  component algebra using the right quotient leg, and bundles its original
  chart index as a `LocalDomain a`.

The finite cover is a `Domain.FiniteCover` of the whole domain over
`D.algebra`. Its coverage proof takes a component containing the image of a
given spectrum point and uses the proved inverse-image formula for relative
domains. No extraction from an arbitrary compact cover is used.

`domainFiniteCover_obj_algebra`, `domainLocalPiece_baseMap` and
`domainFiniteCover_restriction` expose the unchanged quotient algebra and
both actual bounded maps. `domainLocalPiece_baseMap_comp` is equality of
the entire bounded composites over `A`, obtained from the pushout relation;
it preserves algebraic information invisible on spectrum points.

`domainLocalPiece_locus` proves the precise ambient formula

```text
(V.domainLocalPiece D i).locus =
  V.domainLocus D ∩ range (a.chart (V.property.cover.index i)).
```

The proof first moves the image through the component's actual spectrum map,
using the original chart recovery formula. The relative-image theorem then
identifies that image with the intersection locus. The component locus is
the inverse image of its original chart range, yielding the displayed
formula. `domainLocalPiece_over_ambient` separately identifies the actual
ambient map with the composite through the cover piece over `D.algebra`;
its proof applies the full bounded pushout relation to spectrum evaluations.
`domainLocalPiece_covers` uses the finite recognition cover to prove that
the union of the ambient piece loci is exactly `V.domainLocus D`.

For `V : a.saturatedAtlas.RecognizedSubset`, hence an index of
`a.fullRecognitionAtlas`, `fullRecognitionDomainPiece` extends each such
local piece through the chosen saturated representative to its original
chart. It uses `saturatedDomainToLocal`, which composes actual full-domain
representations. The algebra is still exactly the same intersection
quotient, as `fullRecognitionDomainPiece_algebra` states.
`fullRecognitionDomainPiece_baseMap` displays the entire bounded composite
to that quotient from the original chart algebra.
`fullRecognitionDomainPiece_locus` and
`fullRecognitionDomainPiece_over_ambient` retain the literal subset and
actual ambient map. `fullRecognitionDomainPiece_covers` proves that these
finitely many original local domains cover the whole ambient locus of `D`.

The coefficient field, ambient-space and original-index universes are
independent. The field is complete and ultrametric; its valuation may be
trivial. No ambient Hausdorff hypothesis, reducedness or nonzeroness
assumption is added. Empty spectra and zero-size witness covers are allowed.
The imported `Domain` carries the full universal property against all
presented affinoid test algebras.

This unit supplies a finite cover with actual algebras and maps. It does
not construct recognition data for the domain's entire section algebra,
prove maximal recognition closure, invariance or idempotence, or identify
the unrestricted analytic morphism category. The special-intersection
statement and closed-ideal effectiveness are not assumed. Analytic étale
sites and the Harris specialization remain separate obligations.
