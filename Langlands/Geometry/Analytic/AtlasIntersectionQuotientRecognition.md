# Tensor admissibility and full intersections from a recognized quotient

Worker 1685 packages the last tensor and geometric steps for a global
intersection candidate. This is internal infrastructure derived from the actual
bounded completed-tensor comparison, admissible epimorphism composition,
presented closed quotients and finite full-domain recognition.

`AffinoidCoproduct.tensorLift_isAdmissibleEpi` takes an admissible bounded map
`q` from the actual coproduct of two presented affinoid algebras to a presented
affinoid `Q`. The actual completed-tensor lift of `q` composed with the two
coproduct legs equals `q` composed with `fromCompletedTensor`. The latter map
has the bounded right inverse `toCompletedTensor`, so it has uniformly
controlled lifts and is admissible. Composition with `q` proves the genuine
tensor map admissible. The proof uses the constructed bounded maps and their
inverse equation; it does not invoke an open mapping theorem.

`FiniteIntersectionData.exists_of_admissibleCoproduct` applies this tensor
result to the proposed maps in the finite-recognition interface. That
interface has already proved global spectral injectivity and the full domain
property from finite local comparisons and saturation, constructed an actual
local domain with literal intersection locus, and identified both canonical
inclusion restrictions with the proposed maps. Substituting these exact maps
gives the existential conclusion in the form used by
`SpecialSetIntersectionStatement`.

`closedCoproductIntersection` constructs the full local domain for the actual
closed coproduct quotient from its finite comparisons, retaining exactly the
quotient algebra. `exists_of_closedCoproductQuotient` specializes to the actual presented quotient
by a closed ideal of the coproduct. Its quotient map has controlled lifts,
and hence the admissibility input is proved by `ClosedQuotient.map_isAdmissibleEpi`.
The resulting intersection retains exactly that quotient algebra. The
quotient's two input maps are the composites with the original coproduct legs;
the tensor map in the conclusion is built from the actual canonical
full-domain inclusion restrictions.

The finite-recognition data remain an explicit input. In particular, the
module does not construct the ideal-descent quotient's local equivalences or
prove ideal-descent effectiveness, and it does not assert the full special-set
statement without those inputs. Admissibility retains surjectivity and positive
two-sided comparison of the actual quotient seminorm with the target norm.
The coefficient, ambient and original-index universes are independent. Trivial
coefficient valuations, arbitrary positive radii, nonreduced or zero quotients,
empty domains and empty finite covers remain in scope. No global ambient
Hausdorffness is assumed.
