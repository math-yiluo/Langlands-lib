# Integral weights and the actual character kernel

This internal development supplies part of the Lie comparison in
`RelativeRoot.KernelCentralizerStructureStatement`. It uses the existing
scheme-theoretic character kernel and the adjoint action on actual dual-number
identity kernels.

`kernelLieInvariants i a` is the submodule of vectors whose images under every
change of coefficient algebra are fixed by the adjoint action of every point
of the actual kernel of `a`. It imposes no smoothness, reducedness or
primitivity condition on that kernel.

The implementation first proves that character evaluation turns integer
multiples into integer powers. The kernel point equivalence then shows that
`a`, and hence each integer multiple of `a`, takes the value one on every
kernel point. The defining all-algebra weight equation therefore makes each
`n • a` weight space kernel invariant. The supremum property of submodules
gives `integralWeightSpan_le_kernelLieInvariants`, including the zero weight.

These are derived consequences of the published constructions. This file does
not yet identify the invariant submodule with the tangent image of the
all-refinement kernel centralizer or prove existence or smoothness of a
representative.
