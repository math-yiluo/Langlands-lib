# The restriction paired with absolute separable-unit corestriction

For a finite separable extension \(L/K\), restricting to the
open fixing subgroup of the embedded copy of \(L\) and transporting
to the chosen upper closure yields the ordinary restriction along
the corresponding embedding of separable closures. The cochain
maps agree because the composite group map is restriction of
automorphisms and the composite coefficient map is inclusion of
the actual units.

In degree two this restriction coincides with the
canonical restriction `separableRestriction` of the actual Brauer
comparison (`Langlands.Algebra.BrauerComparison.Naturality`). The naturality of the actual Brauer
comparison identifies the two maps on all classes. Thus absolute
unit corestriction after the canonical restriction multiplies by
\([L:K]\), by the open-subgroup index computation.
`separableH2Corestriction` expresses the continuous transfer in the
additive groups appearing in the actual Brauer comparison.

This is the degree identity for the continuous transfer of
Serre, *Local Fields* (1979), Chapter XI, §§1–2, pp. 166–168,
on the actual degree-two continuous unit cohomology.
