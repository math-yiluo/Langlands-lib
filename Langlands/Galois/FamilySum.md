# Direct sums of actual compatible Galois families

Author: Worker 41. This module extends the published
`Langlands.Galois.CoefficientRepresentation` and
`Langlands.Galois.CompatibleFamily` modules.

The namespace is `Langlands.GaloisRepresentation`. `directSum A B` uses the
published `Langlands.FiniteRepresentation.sum` on the actual product of the
two carrier spaces. Its continuity proof uses the linear block-diagonal map
from the product of the endomorphism spaces, with the specified coefficient
field topology and the canonical module topologies. Mathlib proves that the
product topology is the corresponding module topology. No complex topology
is substituted for a lambda-adic topology.

The intrinsic proofs show rank additivity, multiplication of characteristic
and Euler polynomials, preservation of unramifiedness, and multiplication of
the matching Euler polynomials at a finite place. The latter uses a geometric
Frobenius lift provided by the first matching assertion, and the proved
independence of lift to evaluate the second representation at that same lift.
No new lift-existence theorem is assumed.

`sumCollection` takes direct sums at each retained coefficient place.
If the two collections match outside finite sets `S` and `U`, the constructed
sum matches the product polynomials outside `S ∪ U`. Compatibility follows,
and ranks add. These assertions do not require a common weight.

`restrictCollection` discards additional coefficient places when the old
finite excluded set is contained in the new one. It leaves each retained
representation unchanged. Matching, compatibility, purity of a fixed weight
and rank are preserved. Thus two different coefficient exclusions can be
enlarged to their union before taking a sum. This operation does not remove
the coefficient-residue-characteristic exclusion in the matching assertion.
`unionSumCollection` performs this enlargement and sum in one construction;
its proved compatibility and rank laws allow two different original exclusions.
`IsPureCompatible.unionSum_isCompatible` applies this construction to pure
constituents of any two integral weights. It asserts compatibility of their
sum, without incorrectly asserting that the sum has one pure weight.

The construction implements an elementary prerequisite of Harris (1998),
Section 1, printed pp.183-185, where compatible families may have finite
coefficient exclusions and the isobaric case uses direct sums of pure
constituents, potentially of different weights. Those original pages have
been read. Registered source `harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
It asserts no automorphic existence, semisimplicity, Hodge-Tate condition,
geometric origin or ramified local compatibility.
Both collections use a common coefficient number field; extension from
different coefficient fields is a separate construction.

The algebraic operation reuses the published
`Langlands.Weil.Representation.SumsTensor`, without copying or changing its
implementation. The coefficient-topology and compatible-family imports are
also published Library modules. Mathlib is pinned at
`5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0.

## Declaration map and validation

| Declarations | Constructed or proved content |
| --- | --- |
| `directSum`, `directSum_rank` | Actual continuous sum and rank additivity, with independent carrier universes |
| `characteristicPolynomial_directSum`, `eulerPolynomial_directSum` | Exact product identities |
| `IsUnramifiedAt.directSum`, `HasEulerPolynomialAt.directSum` | Inertia triviality and local matching, using a common actual geometric lift |
| `sumCollection`, `MatchesOutside.sumCollection`, `IsCompatible.sumCollection`, `HasRank.sumCollection` | Coefficientwise sum and closure laws |
| `restrictCollection`, `MatchesOutside.restrictCollection`, `IsCompatible.restrictCollection`, `IsPureCompatible.restrictCollection`, `HasRank.restrictCollection` | Enlarging finite coefficient exclusions |
| `unionSumCollection`, `IsCompatible.unionSumCollection`, `HasRank.unionSumCollection` | Sum with two different original exclusions |
| `IsPureCompatible.isCompatible`, `IsPureCompatible.unionSum_isCompatible` | Compatibility of pure constituents and their mixed-weight sum |

The final native compilation and elaborated-type inspection both exited zero
without diagnostics. The inspected sum has carrier universe `max uV uW`;
the compatibility law retains both number fields and the two finite exclusions.
Rank additivity does not unnecessarily assume that the base field is a number
field. The inspected construction and compatibility proofs use only `propext`,
`Classical.choice` and `Quot.sound`. No project axiom is added.
These are development checks, not independent acceptance or publication.
