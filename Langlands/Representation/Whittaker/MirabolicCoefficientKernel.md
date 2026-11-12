# The mirabolic coefficient map and its kernel

Author: Worker 5165. This is an internal construction and reduction for Task
5546, derived from the published matrix-coefficient, character-localization
exactness, and full quotient-dual interfaces.

`mirabolicCoefficientFunctionMap` maps an original representation vector to its
Whittaker coefficient on the actual mirabolic subgroup. It is an intertwiner
for right translation on all scalar functions on that group.
`mirabolicCoefficientKernel` is its actual invariant kernel, with the original
restricted action on its carrier. The membership theorem identifies it with
the vectors whose restricted coefficient function vanishes at every group
element. Evaluation at the identity shows that the specified functional
vanishes on this kernel.

Over every nonarchimedean local field, if all standard Whittaker functionals
on the ambient generic representation are scalar multiples of the specified
one, then the kernel's full upper-unipotent character quotient is zero.
The proof includes the following steps.

1. Restrict smoothness to the mirabolic subgroup. The upper group is a limit
   of compact subgroups by the all-field compact open containment
   construction. Its standard character is continuous and locally constant:
   actual GL is nonarchimedean for the valuative topology, this passes to
   subgroups, and continuous complex characters have open kernels.
2. Extend any equivariant functional on the kernel along its injective
   inclusion, using the published smooth functional-exactness theorem.
   The mirabolic upper group is identified with the ambient upper group by
   its actual multiplicative equivalence.
3. The extended functional is a scalar multiple of the specified ambient
   functional. Its restriction is therefore zero, so every equivariant
   functional on the kernel is zero.
4. The published quotient-dual equivalence identifies these functionals with
   the full algebraic dual of the character quotient. A vector space with
   zero full dual is zero, without any finite-dimensionality assumption.

The final implication takes the independently stated all-field multiplicity
one and mirabolic nondegeneracy propositions as explicit hypotheses.
Nondegeneracy kills the kernel just constructed, and a linear map with zero
kernel is injective. Field and vector-space universes remain independent;
all ranks and positive characteristic are included.

This module does not prove either prerequisite and does not supply an
unconditional proof of `MirabolicRestrictionInjectivityStatement`.
The main target and its published import closure are unchanged.
