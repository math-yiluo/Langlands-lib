# Equivariant retractions onto grouped generalized central spaces

Worker 526, with the actual-projector and full-central-character design
guidance of Workers 430 and 359.

`Langlands.GroupedCentralCharacterRetractionStatement.{uG,uV}` is an
internal Prop-valued definition. It states an interface and supplies no
proof. The group and complex representation carrier universes are independent.

For an actual representation `ρ` of an arbitrary group, assume that its
actual full central action operators span a finite-dimensional complex
subspace of `Module.End ℂ V`, expressed by `Module.Finite`. The carrier
need not be finite dimensional. For every predicate `P` on full central
characters, the conclusion supplies an actual equivariant linear map
from `ρ` to `groupedCentralCharacterSpace ρ P`. Its composite with the
inclusion is a projection: on every vector already in the grouped space
the map is the identity. On each generalized central-character space
whose character fails `P`, the map is zero.

The grouped space is the actual supremum of the selected uniform
generalized spaces. It contains their nilpotent directions; no
semisimplicity or fixed scalar-central subcategory is assumed.
The predicate may select all, none or any subset of the characters.
No topology, smoothness, open-kernel, irreducibility, finite-length or
support hypothesis appears. Zero carriers are allowed.

The provenance is internal algebra. The proposed derivation uses the
finite-dimensional commutative algebra spanned by the actual central
operators. The public `FiniteActionSpectrum.exists_decomposition`
provides primary pieces whose sum is a unit. Normalizing by its inverse
and summing the pieces selected by `P` gives an equivariant operator.
Each algebra operator commutes with every group action operator and
preserves every generalized central-character space. Distinct characters
are separated by one central element, so each unwanted piece vanishes
on a given generalized component. Supremum induction then gives the
identity on the entire grouped space. This describes the intended route,
not a proof supplied by this statement.

The imported grouping definition is the published actual
`groupedCentralCharacterSpace` in Exponents.RealCentralBlock. The private
implementation of the proposed retraction compiles; this statement pair
supplies no proof, and that implementation is not accepted evidence here.
This pair supplies no full-centre finiteness for an actual Jacquet module,
geometric identity layer, exponent exclusion, analytic block isolation,
Jacquet compatibility, Hom factorization or relative dimension comparison.
