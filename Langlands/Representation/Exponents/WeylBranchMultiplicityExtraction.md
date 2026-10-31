# Actual subquotients selected by multiplicity excess

This internal construction isolates the composition-series argument needed for
the supported excess-multiplicity branch proof. It works for any group and
complex representation, with independent universes for the group, ambient
carrier, comparison carrier and constituent carrier.

`WeylBranchPieces.excessGradeSubquotientWitness` takes an actual finite invariant
filtration of `A`, a designated grade `i₀`, an actual representation equivalence
from that grade to `B`, actual Jordan–Hölder multiplicity witnesses `b` in `B`
and `M` in `A` for the same representation `τ`, and `b < M`. It returns an index
different from `i₀`, an actual subrepresentation of that grade and an actual
surjective intertwiner onto `τ`. The choice is noncomputable and need not be
canonical.

The proof first uses the published
`jordanHolderFiltrationDecomposition` to obtain actual finite composition
series for every grade, with multiplicities summing to `M`. Their finite series
are consequences of the supplied ambient series. No separate finite-length,
irreducibility or admissibility assumptions on the grades are imposed.
Transport along the designated equivalence and
`HasJordanHolderMultiplicity.unique` identify the designated count with `b`.
If all other counts vanished, the ambient sum would equal `b`, contradicting
the strict excess. Hence another grade has positive multiplicity.

`isSubquotient_of_positive_multiplicity` turns this positive count into quotient
data. The definition of `factorMultiplicity` as the finite cardinality of
matching composition-factor occurrences supplies a matching index and an actual
equivalence of that factor with `τ`. The published
`isSubquotient_graded` and equivalence transport then exhibit `τ` as an actual
quotient of a subrepresentation. `excessGradeSubquotientWitness` exposes the
index, subrepresentation and surjective map by classical choice.

`grade_multiplicities` records the decomposition step. The companion theorem
`IsGluedFrom.exists_isSubquotient_piece_of_multiplicity_excess` applies the same
argument at an object of a natural filtration and transfers the selected index
through the permutation in `IsGluedFrom`. It returns a named piece different
from the designated named piece, independently of their filtration order.

The provenance is internal: the argument uses the published actual-filtration
definitions, multiplicity decomposition and transport proofs, and actual
subquotient laws. It assumes no geometric lemma. Applying it to a geometric
filtration still requires constructing that filtration and proving the
designated contribution is the inner Jacquet module. It does not establish
whole-Levi branch identification, noncoarse minimality, localization or
continuation, and it does not prove the closed supported obstruction theorem.
