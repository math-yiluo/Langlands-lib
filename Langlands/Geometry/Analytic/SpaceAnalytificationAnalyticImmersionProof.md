# Open and closed immersions under algebraic-space analytification

`spaceAnalytificationAnalyticImmersion` proves
`Langlands.Analytic.SpaceAnalytification.SpaceAnalytificationAnalyticImmersionStatement.{u}`
for every universe `u`. It applies to the two supplied analytifications
of separated algebraic spaces locally of finite type, and to a map
compatible with their finite polynomial tests.

For open preservation, the images of the source's affine étale
tests make the image of the analytic map open. The factor through
that domain gives the domain the analytification tests of the
algebraic source. Affinoid point comparison and chart gluing prove
that this factor is an isomorphism. For open reflection, the
one-point affinoid comparison converts lifts through the analytic
open immersion into lifts of finite local algebra tests. These
lifts give the truncation criterion on represented affine tests.
Algebraic monicity and descent along the étale target atlas give
the reflected open immersion.

For closed preservation, the algebraic pullback over a ring-valued
point is the spectrum of a quotient. Affinoid tests of the
analytifications give the corresponding analytic quotient pullback.
For a general affinoid test, a finite domain cover realizes the test
by ring-valued points. The closed quotient ideals agree on overlaps
and descend to the original affinoid algebra. The quotient spectra
represent the analytic pullbacks. The closed immersion criterion
then recognizes the inverse image of every target affinoid domain
and identifies its bounded map with an admissible quotient map.

For closed reflection, the analytic closed immersion is proper
and monic. The comparison detects algebraic monicity and reduces
the algebraic question to represented affine étale target tests.
Quasi-compactness gives finite-type test morphisms. A finite open
factorization and compact affine analytic slices show each
projection is a finite monomorphism. Algebraic descent along
the étale target atlas yields the original closed immersion.

The source context for the statement is Conrad–Temkin 2009,
Theorem 2.3.1 and §§4.1–4.2, together with the Berkovich comparison
and immersion definitions cited in the paired statement Markdown.
The implemented preservation proof uses finite affinoid domain
descent of the closed ideals and the Library's categorical
affinoid test comparison.
