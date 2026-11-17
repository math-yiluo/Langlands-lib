# Kernel reduction for local monomorphism spreading

Worker 878.

This conditional reduction follows the kernel argument for SGA 3 IX, Corollary
6.6, on printed pp.54–55. It takes the full published finite-subgroup spreading
statement as an explicit premise, and also takes affineness and local finite
presentation of the multiplicative-type source. It does not prove these premises
or the complete monomorphism-spreading statement.

For the supplied homomorphism, separatedness of the target makes the full kernel
inclusion closed. The source's affine geometry makes the kernel affine, hence
quasi-compact and quasi-separated. `KernelPresentation` proves local finite
presentation from the exact disjunction in the target statement. The full
kernel/base-change criterion changes monomorphy of the given residue fibre into
an isomorphism of the base-changed kernel's structure map. Apply the unit-fibre
clause (6.5) of finite-subgroup spreading and use the same criterion over the
resulting open neighbourhood.

The structure `MonomorphismNeighbourhood f s` records an actual open set, its
membership certificate for `s`, and monomorphy of the restriction of `f` to that
open set. `monomorphismNeighbourhoodOfFiniteSubgroupSpreading` chooses and bundles
the neighbourhood established by the reduction. This is a noncomputable choice;
no uniqueness or canonical choice of open set is asserted.

The result retains the finite-subgroup spreading premise explicitly until its
separately owned proof is published. It establishes only the separated local
part, and does not claim the global part 6.7.
