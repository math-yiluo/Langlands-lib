# Exact upper cuspidal Jacquet counts

Authors: Worker 500, using the finite-family counting theorem of Worker 496.

`Langlands.glUpperCuspidalJacquetMultiplicityFromFiltration` proves exactly
`Langlands.GLUpperCuspidalJacquetMultiplicityFromFiltrationStatement`, with
independent field, source-carrier and test-carrier universes. The full
associated-filtration proposition remains an explicit premise, as required
by that statement.

Admissible cuspidality supplies smoothness and quasicuspidality. The proof
bundles the source as `SmoothRep.of ρ` and applies the associated-filtration
premise. It obtains an actual zero-to-full filtration and an equivalence
from its graded-quotient indices to the existing
`MinimalConjugatingPermutations B C` type. Every quotient is equivalent to
the actual whole-Levi transport of `ρ` at the indicated index.

The family used for counting is exactly
`w ↦ Rep.of (transport B C w.val.val w.property ρ)`. The published
`CuspidalSupport.JacquetLength.isIrreducible_transport` proves that each
family member is irreducible. Applying
`finiteFamilyFiltrationMultiplicity` to the supplied filtration gives its
composition-series length and every multiplicity biconditional. That
theorem constructs the realizing count from the supplied series and uses
Jordan–Hölder independence to exclude all other counts.

Both remaining identifications are definitional. The normalized smooth
functor object used by the filtration premise is exactly the target's
bundled `upperJacquet` of `induced`, with the same carriers and module
structures. The matching-family-index subtype is exactly
`AssociatingPermutations B C ρ τ`. Thus repeated isomorphic Weyl factors
are counted separately, and no extra quotient of the permutation index
type or semisimplicity assumption is introduced.

The proof covers rank zero and arbitrary target representations, matching
the adapter statement. It changes no normalization, assumes no Langlands
classification or generic relative comparison, and constructs no geometric
filtration. The complete upper-and-opposite theorem still needs the
independently proved associated filtration and actual opposite transfer.
