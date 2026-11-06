# Original product topology of the assembled Weil point comparison

This derived construction supplies the product topology step for Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), Example 4.2,
printed page 10.

Retain the actual finite projective algebra A to B and the specified original
local tensor equivalences from `ProductTensorWeilPoints`. The upper model Y
is locally of finite type, separated, quasi-compact and quasi-separated,
with finite affine neighborhoods. Assume now that each lower coefficient
ring C i is a local topological ring with open units. Each upper local
coefficient ring D i j has open units, is finite projective over C i, and its
given topology is the finite-module topology. Each upper index family is
finite; the family of lower indices can be arbitrary.

`productTensorWeilLocalPointHomeomorph` first uses the original base-change
point homeomorphism in every lower factor, taking points of the actual
base-changed local model to points of the original Weil model. It then applies
the proved original completed-tensor Weil point homeomorphism at each lower
index and uncarries the dependent product. All factor point topologies are
the existing `schemePointTopology`; both product spaces have their product
topologies.

The compatibility theorem proves that this product homeomorphism, composed
with the original global local-model point map, equals the set-theoretic
`productTensorWeilPointEquiv` at every upper component. The proof cancels the
original base-change point equivalence and uses the original local counit
identity, followed by the global-to-local identity already proved in
`ProductTensorWeilPoints`.

`productTensorWeilPointHomeomorph` uses the existing
`localProductPointTopology` on the actual global Weil point space. This
topology was defined by the original map to independently topologized
base-changed local-model points. Consequently that map is inducing.
Composing it with the product of local homeomorphisms is inducing as well.
The proved compatibility identifies this composite with the already
constructed global point bijection. An inducing bijection is a
homeomorphism, giving the required comparison to the product of the original
upper point topologies. The final apply identity retains exactly that
original global point bijection.

All rings and index types share an arbitrary universe. No topology is
defined by pulling back through the asserted Weil comparison. No
quasi-compactness or finite type of the constructed Weil scheme is assumed;
quasi-compactness and quasi-separatedness are imposed on the given upper Y,
as in the independently proved product-point bijection. The given local
tensor equivalences and local module topologies are inputs to this generic
assembler. Their original arithmetic instances have been proved separately;
actual adelic-level instantiation and the full adelic Weil comparison remain
host obligations.
