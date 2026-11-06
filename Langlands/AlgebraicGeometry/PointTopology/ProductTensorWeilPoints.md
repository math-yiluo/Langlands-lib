# Actual Weil points over products from the original local tensor comparisons

This derived construction assembles the local coefficient comparisons for
Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
Example 4.2, printed pages 9–10. It supplies a product-point bijection without
assuming quasi-compactness of the constructed Weil scheme.

Let A to B be an actual finite projective commutative algebra extension.
Let C be an arbitrarily indexed family of A-algebras. For each lower index i,
let D be a family of local rings with both their original C i-algebras and
their original B-algebras. Suppose a specified C i-algebra tensor equivalence
identifies C i tensored with B over A with the product of these upper factors,
and its right tensor coefficient is the original B coefficient map.
The local equivalences are explicit inputs of this generic assembler; the
intended original-place arithmetic equivalences are proved separately.

`productTensorWeilFactorEquiv` exchanges tensor factors and regards each local
equivalence as a B-algebra equivalence. Its coefficient compatibility is proved
from the stated right-factor identity.
`productTensorWeilCoefficientEquiv` uses the proved arbitrary-product
finite-projective tensor equivalence, these original local equivalences, and
currying of the product indices. The result is a B-algebra equivalence from B
tensored with the entire lower product to the product over the actual
dependent pairs of lower and upper indices. The pure-tensor formula is
exactly the given local tensor map on each original lower component.

`productTensorWeilFactorTestMap` is the actual morphism from each upper
factor's spectrum to the original global Weil test pullback. It uses the
constructed coefficient equivalence and the canonical spectrum-of-tensor
pullback isomorphism. Its local comparison identity proves equality with the
original local completed-tensor factor test followed by restriction to the
chosen lower coordinate. The proof checks the two pullback projections. The
first is the original lower algebra map, by the local equivalence's algebra
law; the second follows from the B-structure equations.

For a locally finite type separated upper B-scheme Y that is quasi-compact
and quasi-separated and has finite affine neighborhoods,
`productTensorWeilPointEquiv` constructs the global product-point bijection.
It composes the actual all-test Weil representing equivalence, the canonical
tensor-spectrum isomorphism, change of coefficients by the constructed
algebra equivalence, and the proved product-point bijection for the upper
quasi-compact quasi-separated model and the upper local rings.

The counit identity proves that every upper component is the original global
relative Weil counit on its actual factor test spectrum. The local identity
then proves that restricting a global Weil point to one lower coefficient and
taking the original local upper component gives that same upper point. Its
proof uses the factor test identity and naturality of the original counit.

All rings and index types share an arbitrary universe. No finiteness
assumption is imposed on either product index family. The upper factors are
local rings; the lower factors need not be local for this set-theoretic
construction. There are no field or separability assumptions. This module
constructs a bijection and its original-map comparisons; topological
compatibility, actual arithmetic level instantiation and the full adelic
Weil comparison remain host obligations.
