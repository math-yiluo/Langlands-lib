# Affine neighbourhoods from stalk-intersection localizations

This internal adapter connects the algebraic valuation intersection to the
geometric construction for Bosch–Lütkebohmert–Raynaud, *Néron Models*,
§6.4 Lemma 4.

`StalkIntersectionLocalizations E` is the algebraic condition that every
maximal localization of the actual intersection is presented by one of
the selected stalks, with its canonical inclusion.
`affineNeighbourhoodOfStalkIntersectionLocalizations` takes this condition
and the fact that `X.functionField` is the intersection's fraction field
and constructs an actual common affine neighbourhood of finite `E`.
Here `X` is integral and separated, locally of finite presentation over
an affine base. The constructor supplies all base, generic and local
maps canonically, builds the affine stalk model, and applies finite-type
approximation and prime avoidance. The two algebraic hypotheses remain
explicit inputs, rather than conclusions from normality in this module.

`affineNeighbourhoodOfSubsetGenericPoint` handles empty selected sets
and those consisting only of the generic point directly by choosing an
affine neighbourhood of that point.

For a locally noetherian integral scheme,
`normalStalkValuations` constructs the family of actual valuation
subrings at a selected set of normal points with dimension at most one.
Their underlying intersection is definitionally `stalkIntersection`.
For separated `X` the family is injective; after excluding the generic
point, every member is a DVR.

`stalkIntersection_localization_of_valuation` transports the localization
of a member of this valuation family back to the original stalk. The
canonical ring equivalence from the stalk to its image is an algebra
equivalence over the intersection, because both maps into the function
field agree. Localization transfers along its inverse.
All declarations work in every universe.
