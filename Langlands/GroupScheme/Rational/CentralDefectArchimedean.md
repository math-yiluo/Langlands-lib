# Vanishing of the unit-valued central defect

Let a central isogeny over a number field `F` and a natural cocycle on
a finite Galois cover `L/F` be given, with central lift data over `L`.
A character of the kernel gives the relative unit class
`kernelUnitObstruction`. A trivialization of the cocycle over an
infinite completion of `F` kills the invariant of this unit class at
each place of `L` above that completion.

At an infinite place `w` of `L`, the reciprocity formula uses a
nontrivial automorphism fixing `w` when one exists. Such an
automorphism acts as complex conjugation under the embedding of `w`.
The map `complexCompletionConjugation` transports complex conjugation
across the canonical identification of the completion with `ℂ`. It fixes
the completion of `F`, by continuity and the dense image of `F`. The local primitive theorem
provides a central cochain after a finite Galois refinement of this
completion extension. The coefficient completion at `w` is
algebraically closed, so the refinement is isomorphic to it and the
extended conjugation still acts as complex conjugation.

Apply the kernel character to the primitive. Its coboundary formula
at the conjugation pair and the identity pair makes the product in
the reciprocity formula a complex norm. The sign invariant of this
norm is zero. When the stabilizer is trivial, the archimedean
invariant is zero by its definition.

For an everywhere locally trivial cocycle, the finite-place result
and this archimedean result supply all the hypotheses of global
injectivity for relative unit classes. The theorem
`kernelUnitObstruction_eq_zero` then concludes that the class is zero.
