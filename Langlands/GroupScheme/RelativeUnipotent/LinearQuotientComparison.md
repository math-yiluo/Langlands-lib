# Linear comparisons of common-weight vector quotients

This internal adapter for Task 7200 constructs actual quotient comparisons from
compatible isomorphisms of consecutive terms, proves their equivariance, and
extracts actual linear equivalences between finite free vector quotients.
The commutative base ring and universe are arbitrary, and the two finite
vector ranks are independent, including rank zero.

The generic construction takes inclusions `i : K → G`, `i' : K' → G'`, actual
isomorphisms `e : G ≅ G'` and `eK : K ≅ K'`, and the commuting square
`i ≫ e.hom = eK.hom ≫ i'`. The supplied maps `q : G → Q` and `q' : G' → Q'`
satisfy the unchanged full `RelativeRoot.IsFppfQuotient` predicate for the
represented ranges of those inclusions.

`precomp_iso` transports the second full quotient across the source
isomorphism. `range_comap_of_compatible_isos` identifies its kernel range
with the first range on every scheme test. The existing canonical full
fppf quotient isomorphism then constructs `isoOfCompatibleTerms`, with
the exact recovery equation
`q ≫ iso.hom = e.hom ≫ q'`. No quotient comparison map is supplied as an input.

`isEquivariant_of_fac` proves that an actual quotient comparison is equivariant
when both quotient maps and the comparison of their sources are equivariant.
It assumes the first quotient map is quasi-compact, in addition to its full
fppf quotient predicate. This condition holds for the intended maps between
affine filtration terms and affine vector groups. The proof uses the existing
local quotient-lift equality criterion. It pulls an arbitrary quotient point
back to a flat surjective cover where it lifts, checks the equivariance equation
using the commuting square there, and reflects the equality to the original
test. It does not assume surjectivity on points over the original test scheme.

For vector quotients, `VectorGroup.powerWeightAction n d` is the existing
actual scalar action through `Gm.powerHom (Spec R) d`. The algebra-valued
formula `affinePointsEquiv_powerWeightAction` follows from the existing
all-test coordinate formula for `weightAction`. The actual
`Corepresented.affineSectionsIso` transports global sections back to the
coefficient algebra; the character at the unit point `t` then has value `t^d`.
Consequently `hasScalarWeight_of_equivariant` derives the precise all-algebra,
all-unit premise of `VectorWeightLinearity` from actual action equivariance.

The final constructors take actual rank-one actions on `G` and `G'`, the
equivariance of `q` and `q'` for the common power character, and equivariance
of `e.hom`. `isoOfCompatibleTerms_hasScalarWeight` derives the quotient
isomorphism's scalar weight. For `0 < d`,
`linearEquivOfCompatibleTerms` returns an actual linear equivalence over
each coefficient algebra, using the genuine inverse of the constructed
quotient isomorphism. Its apply theorem states that its function is exactly
the induced quotient map in affine coordinates.

`isoOfCompatibleTerms_eq_matrixHom` identifies the actual quotient homomorphism
with one base-ring matrix. `coordinates_isoOfCompatibleTerms` gives that same
matrix formula on every scheme test, including non-affine and nonreduced tests.
No field, characteristic, smoothness, reducedness, connectedness, fixed-rank
or inverse-equivariance premise is introduced.

The provenance is internal: this combines existing full fppf quotient
uniqueness, actual action naturality and local lift descent, the actual
affine/global-section coordinate comparison, and the arbitrary-ring
`VectorWeightLinearity` construction. This unit supplies no root charts or
different-torus comparisons.
The compatible term isomorphisms, their actual equivariance, and equivariance
of the geometric quotient maps remain explicit inputs. Linearity of the
induced quotient transition is proved.
