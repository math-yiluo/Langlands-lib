# The exact local residue-degree formula

The theorem `Langlands.CentralDivision.localResidueDegree.{u}` proves exactly
`Langlands.CentralDivision.LocalResidueDegreeStatement.{u}` for arbitrary
universe `u`. It adds no hypothesis and makes no characteristic restriction.

After introducing the original local field `K` and finite-dimensional central
division `K`-algebra `D`, the proof applies
`localDivisionResidue_finrank_eq_reducedDegree` from `LocalDivisionReducedDegree`.
That theorem compares the degree of the existing full-residue embedded field
with the canonical reduced degree in both directions. The upper bound comes
from reduced-characteristic-polynomial annihilation and minimal-polynomial
divisibility. The lower bound comes from valuation-layer approximation,
Nakayama's lemma for the finite original integer lattice, and the original
scalar-tower dimension identity.

The residue field is the actual valuation integer ring modulo its strict-value
ideal, with the existing `localDivisionResidueField` and
`localDivisionResidueAlgebra` structures. Thus the conclusion uses exactly the
quotient and original scalar action named in the published statement. The
statement and all of its imported pairs are unchanged.

The proof follows the internal dimension comparison described above. The
statement's source is Tits, exposé 505, §3.1, formula (1), specialized to the
finite commutative residue field. This proof does not use that formula as an
assumption. It proves neither local SK1 nor local Kneser–Tits.
