# The integral weight image of character-kernel invariants

This internal contribution constructs an actual universal point of the
scheme-theoretic character kernel and proves the reverse integral-weight
support inclusion. It derives these results from the existing character-kernel
point equivalence, the quotient universal monomial character, the Lie
coefficient maps, and the split-torus weight decomposition. It does not invoke
a smoothness theorem or assume a Lie-image conclusion.

For a field `k`, a split commutative torus `T`, and any character `a`,
`Diagonalizable.kernelUniversalPoint T hT a` is a point of the actual
`RelativeRoot.characterKernel a` over the group algebra
`k[X*(T)/ℤa]`. The definition transports the quotient monomial character
through the inverse global-sections equivalence for the affine test scheme,
then through `kernelCharacterPointsEquiv`. The lemma
`characterValue_kernelUniversalPoint` proves that a character `b` evaluates
at this point as the monomial unit at the class of `b` in that quotient.
The quotient is by all integer multiples of `a`, without saturation, and
retains torsion even in the characteristic of `k`.

For an affine group `G` locally of finite type over `k`, an arbitrary group
homomorphism `i : T.toGrp ⟶ G`, and any `a`,
`RelativeRoot.kernelLieInvariants_le_integralWeightSpan G T hT i a` proves
that vectors fixed by the character kernel over every coefficient algebra
belong to the sum of the weight spaces at all integer multiples of `a`.
In particular, weight zero is included. The theorem assumes neither
smoothness of `G` nor a monomorphism condition on `i`; it also allows `a = 0`.
No reducedness or smoothness assumption is imposed on the kernel.

The implemented proof chooses the internal character-weight decomposition
provided by `isInternal_weightSpace_of_isSplitTorus`. Each Lie vector is a
finite sum of components in their respective all-test weight spaces. At the
universal kernel point, each component is multiplied by its quotient-class
monomial. Kernel invariance says that their sum equals the constant original
vector. For a character `b` outside `ℤa`, its quotient class is nonzero.
Reading the corresponding Lie coefficient and then projecting to the
original `b`-weight component gives that component itself on the left and
zero on the right. Components sharing the same quotient class are separated
by this original weight projection. The remaining finite sum consists only
of integral `a`-weights and hence belongs to `integralWeightSpan i a`.

Together with the existing
`RelativeRoot.integralWeightSpan_le_kernelLieInvariants`, this identifies
the kernel-invariant submodule exactly with that complete integral weight
span. This unit does not construct a centralizer representative or prove
its smoothness; those are separate steps in the host task.
