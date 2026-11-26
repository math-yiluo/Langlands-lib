# The Weil representation cases of cyclic descent

This module supplies the restriction decompositions used in
[one-step numerical descent](HenniartDescentStepProof.md). It identifies
`W_M` with the open normal kernel of `W_L → Gal(M/L)` using
`finiteGaloisQuotientKernelEquiv`. The conjugation through this equivalence
agrees with `Numerical.weilConjugate` on classes.

`Langlands.Henniart.DescentWeil.extensions` starts with an invariant
irreducible class of `W_M`. A lift of a generator of the cyclic quotient
has an invertible intertwiner on the representative. The quotient order
power of that operator differs from the action of the corresponding
kernel element by a scalar, by Schur's lemma. Rescaling by a complex root
makes the two operators equal. The representation of the semidirect
product with the infinite cyclic group then factors through `W_L` and
restricts to the given representative. Continuity follows from continuity
on the open kernel, and irreducibility follows from irreducibility there.
Twisting by the complex characters of the finite quotient gives a family
indexed by `Fin [M : L]`. Every twist has the original restriction. An
intertwiner between two twists restricts to a scalar on the common kernel
representation, so an invertible intertwiner forces the two characters to
coincide.

`Langlands.Henniart.DescentWeil.induction` starts with a class that moves
under Weil conjugation. The stabilizer of the class contains the kernel
and has trivial image in the prime-order quotient. Thus distinct cosets
give inequivalent irreducible blocks in the restriction of finite-index
coinduction. In coset coordinates a commuting endomorphism is scalar on
each block by Schur's lemma. Right translation makes these scalars equal.
Semisimplicity of the coinduced representation gives a projection onto
any subrepresentation, and the scalar property of the projection implies
irreducibility. The restriction is the direct sum indexed by the cosets,
including the original class at the identity coset. The proof transports
the induced action to the finite product indexed by `Fin [M : L]`, so the
Weil carrier remains in its original universe even if the field universe
is larger.

## Provenance

The two arguments implement the cyclic extension and induction assertions
used in Guy Henniart, *La conjecture de Langlands locale numérique pour
GL(n)*, §6.8, p. 521 (PDF p. 26), registered as `henniart-1988-numerical`,
SHA-256 `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
They are the Weil-side assertions in cases (a) and (b) of Lemma `lem:step`
in §6.6 of `operator-numerical-llc-route-2026-11-16`,
`numerical-LLC-route.tex`, SHA-256
`b57ba9428a0d664d0c6beed75bbc2a2d0d73638718a8080c2f913b75acbbb3c8`.
