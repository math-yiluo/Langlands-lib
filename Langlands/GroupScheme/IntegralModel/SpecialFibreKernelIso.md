# Special-fibre kernels under compatible model isomorphisms

This internal construction implements the presentation-change step needed
by `UnramifiedModelKernelStatement`. It uses the published generic rigidity
of flat integral models, functorial base change and the actual kernel
comparison `kernelSquareIso`. It does not prove the unramified kernel
statement or assume any unproved statement as a hidden input.

For arbitrary integral domains `R` with fraction field `K`,
`IntegralModel.Iso.hom_square` considers two source models of a `K`-group
`G`, two target models of a `K`-group `H`, and compatible source and target
model isomorphisms whose generic maps are the respective identities. Any
two model homomorphisms extending the same `f : G → H` then form a
commutative square with those isomorphisms. The proof compares their
generic fibres and applies the published `hom_eq_of_generic`. No smoothness
or point-image equality is needed for this step.

When `R` is local, `Iso.specialFibreIso` base-changes a compatible integral
model isomorphism to its actual residue field. `Iso.specialFibreKernelIso`
base-changes the commuting square above and identifies the two
scheme-theoretic kernels. `Iso.specialFibreKernel_properties` therefore
transfers the full conjunction of smoothness, connectedness and unipotence
from one kernel to the other.

For the intended application, one must still construct compatible
isomorphisms between the arbitrary supplied smooth models and models with
known kernel geometry, and prove that geometry. Neither equality of
integral-point images nor the existence of these comparison isomorphisms is
proved here. The root-group models, their ordered open cell and the
smooth connected kernel result for their depth maps remain separate
mathematical obligations.
