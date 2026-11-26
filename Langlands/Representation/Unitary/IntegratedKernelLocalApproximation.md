# Commutation and local approximation by integrated kernels

`Langlands.Analysis.integratedKernelLocalApproximation` proves
`IntegratedKernelLocalApproximationStatement` for a Bochner integrated
isometric action on a complete complex normed space. With left and right
invariant measure, a kernel invariant under conjugation by `k` acts by an
operator commuting with the action of `k`. For a real nonnegative kernel of
integral one, the error at a vector is bounded by an orbit error bound on
the nonzero set of the kernel.

The commutation proof moves the bounded translation operator into the
integral and applies Haar invariance to the left and right translations in
conjugation. The approximation bound integrates the difference of the
orbit vector and the original vector, then uses the scalar integral one.
These are direct consequences of the Bochner integral formulas for
integrated isometric actions.
