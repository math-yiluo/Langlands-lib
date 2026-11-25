# The opposite Borel theorem from Lie-containment spreading

`relativeOppositeBorel_of_lieContainment` has the unchanged
`RelativeOppositeBorelStatement` as its conclusion and the single explicit
premise `RelativeParabolicLieContainmentStatement`, in every universe.
It supplies `relativeBorelDynamicPresentation` (proved in
`BorelDynamicPresentationProof`) to the existing two-input global reduction.

Thus the local construction, intersections, field uniqueness, overlap matching,
effective subgroup descent and relative Borel transport have been discharged
from the opposite Borel proof. The Lie-spreading premise is not proved here;
it is `relativeParabolicLieContainment` in `ParabolicLieContainmentProof`, and
this theorem by itself remains conditional on it.
