# Finite-product Weil restriction on field-valued points

This internal supporting construction combines the full-test finite-product
Weil comparison with the finite-product theorem for etale-chart topologies
and the published local Weil point comparison.

First, for any finite family of commutative `A`-algebras `B i` and an
algebraic space `X` over their product, `productFanIsLimit` proves that the
explicit dependent product of factor Weil presheaves has the ordinary
product universal property. The lift acts componentwise on every test
scheme. Naturality and uniqueness follow from the component maps.

Suppose the Weil restriction along the product algebra and each factor
Weil restriction are algebraic spaces. `spaceProjection` constructs the
actual space projection using the full-presheaf comparison.
`spaceFanIsLimit` transports the dependent-product universal property
along that comparison. The full-presheaf limiting fan is proved, rather
than added as an extra hypothesis.

For a henselian nontrivially normed field `K` and a finite family of
henselian nontrivially normed finite extensions `L i`, assume each
`L i` has its specified `K`-algebra structure, continuous scalar
multiplication, and the `K`-module topology. No preservation of the
separately specified norms is required. The theorem also retains the
algebraicity witnesses just described, quasi-separated local finite
type of each factor space over `L i`, and quasi-separated local finite
type of the total and factor Weil spaces over `K`.
`finiteProductWeilRestrictionPointHomeomorph` gives the homeomorphism
from rational points of the product-base Weil restriction to the product
of rational points of the original factor spaces.

It first applies `finiteProductSpacePointHomeomorph` to the proved
full-presheaf limiting fan. It then applies
`ringWeilRestrictionPointHomeomorph` to every factor and takes their product.
All topologies are the independently defined etale-chart topologies.
The component formula is exactly the original factor space projection
followed by `ringWeilRestrictionBasePointsEquiv`.

This unit does not supply the geometric hypotheses or identify a global
completed tensor algebra with the product. The specified tensor base-change
construction and the arithmetic tensor equivalences provide that preceding
step. Complete local fields supply the module-topology premise; the
unrestricted incomplete-field version is not used.

Worker 113 generalized the original scalar-action premise from normed
algebras to continuous scalar multiplication. The same full-presheaf
product proof applies, and the local comparison now needs only the
continuous original algebra maps together with the retained module
topologies. This is an internal generalization of the construction.
