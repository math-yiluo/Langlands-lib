# Actual special covers of recognized-chart domains

Author: Worker 36.

This module proves specialness of the finite cover constructed for an
arbitrary full affinoid domain in a recognized chart over the saturated
atlas. It identifies the actual completed-tensor overlap maps with genuine
affinoid pushout quotient maps followed by constructed bounded
equivalences. It proves surjectivity and positive uniform quotient-norm
comparison for these maps and constructs the resulting literal special
subset.

The source motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), the definition of a special subset and a special
cover before Lemma 1.2.12, printed p.20 / PDF p.17, and the recognition
conditions and Proposition 1.2.13(ii)–(iii), printed p.21 / PDF p.18.
Registered source `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These original pages were read for this construction. No source-specific
errata file was found in the available project and Library locations.

This is a derived construction toward closure of the recognized atlas
under full affinoid domains. The source requires a compact finite union
with represented pairwise overlaps and admissible epimorphisms from the
genuine completed tensors of the component algebras to the overlap algebras.
The imported `IsSpecialCover` expresses these requirements, including the
Hausdorff topology of the actual compact union. This module constructs
these properties for the particular finite cover already built from a
given full domain. It does not prove the general special-intersection
lemma or assume its missing ideal-effectiveness input.

Fix `V : a.saturatedAtlas.RecognizedSubset` and
`D : Domain K V.algebra`. Write `d` for the existing
`fullRecognitionDomainGluing V D`, and `Eᵢ` for its canonical full component
domains over `D.algebra`. Their algebras are the actual saturated-atlas
presentations of the finite local pieces, and their structural bounded
maps are canonical full-domain factors.
For a pair `i,j`, the actual intersection
`Q = Eᵢ.inter Eⱼ` is the affinoid pushout quotient of those two structural
maps. The existing local overlap `L` is obtained by regarding `Q` as a
relative domain over `Eᵢ.algebra` and extending it through the original
local representative of that component. Its algebra is literally the
pushout algebra, and its locus is exactly the ambient intersection.

`fullRecognitionDomainOverlapEquiv` constructs the actual bounded
equivalence `e` from this unchanged quotient algebra to the presentation
chosen by the saturated atlas for the same overlap locus. It uses the
already constructed local-domain comparison, whose maps are mutually
inverse entire bounded restrictions.

`fullRecognitionDomainGluing_leftRestriction` identifies the first stored
atlas restriction with `e` composed with the actual left pushout leg.
The inverse of the local-domain comparison is an inclusion from the chosen
overlap representative to `L`. Composing it with the local extension
inclusion gives an actual arrow to the first component representative.
Full-domain uniqueness makes this composite equal to the saturated-atlas
inclusion between the same two objects. Applying the restriction field
to this arrow equality gives the required equality of full bounded
algebra homomorphisms.

`fullRecognitionDomainGluing_rightRestriction` proves the analogous
identity for the second leg. It cancels the entire structural map of
`Eⱼ` by its full represented-domain uniqueness theorem. After this
cancellation, compatibility of the constructed affinoid realization
identifies the two stored composites over `D.algebra`; the first-leg
identity and the actual pushout equation identify them with the second
pushout leg. The proof evaluates these full equalities on arbitrary
algebra elements. It never infers algebra-map equality from equality
on spectrum points.

`fullRecognitionDomainGluing_overlapTensorMap` applies the genuine
completed tensor's bounded-map uniqueness theorem to both complete leg
identities. It proves that `d.overlapTensorMap i j` equals `e` composed
with the actual `AffinoidPushout.tensorMap`. Thus the map whose
admissibility is required by specialness is exactly the map proved
admissible here.

`fullRecognitionDomainGluing_tensor_isAdmissibleEpi` uses the imported
admissibility theorem for that actual pushout quotient. The bounded
equivalence `e` is itself admissible because its bounded inverse supplies
a bounded section. Composition preserves surjectivity and the positive
uniform comparison between the quotient seminorm and the unchanged
target norm. These are the actual `IsAdmissibleEpi` properties, rather
than algebraic surjectivity alone. The argument uses the constructed
quotient lifts and bounded inverse; it does not invoke an open mapping
theorem requiring a nontrivial valuation.

`fullRecognitionDomainGluing_isSpecialCover` combines this tensor
admissibility with the Hausdorff topology obtained from the actual
affinoid realization's homeomorphism from the finite union to the
spectrum of `D.algebra`. Compactness is already proved from the finite
union of original component charts. The ambient space need not be
Hausdorff.

`fullRecognitionDomainSpecialSubset` constructs the resulting
`a.saturatedAtlas.SpecialSubset` with literal subset `V.domainLocus D`
and the constructed special finite covering. Its value theorem records
this literal equality.

The coefficient-field, ambient-space and original-index universes are
independent. The coefficient field is complete and ultrametric, including
trivial valuations. No reducedness, nonzero-algebra or nonempty-cover
hypothesis is added. Component representations retain their full
universal properties against every presented affinoid test algebra.

This unit establishes specialness for the constructed cover and packages
the actual special subset. Recognition of the whole domain and its
section presentation, maximal local-domain closure, idempotence and the
unrestricted morphism-category identification remain later constructions.
Analytic étale and equivariant sites and the Harris tower specialization
are not asserted by this unit.
