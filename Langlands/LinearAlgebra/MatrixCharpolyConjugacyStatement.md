# Finitely many conjugacy classes with a given characteristic polynomial

`Langlands.MatrixCharpolyFiniteConjugacyStatement.{uK}` is the following
proposition. This module defines the proposition and supplies no proof. The
published theorem `Langlands.matrixCharpolyFiniteConjugacy.{uK}` in
`Langlands.LinearAlgebra.MatrixCharpolyConjugacyProof` proves it.

## Statement

For every field `K : Type uK`, every natural number `n` and every polynomial
`c : Polynomial K`, there is a finite set `s` of matrices in
`Matrix (Fin n) (Fin n) K` (a `Finset`) with the following property. For every
matrix `x : Matrix (Fin n) (Fin n) K` with `x.charpoly = c` there are `y ∈ s`
and an invertible matrix `g : Matrix.GeneralLinearGroup (Fin n) K` with

`(g : Matrix (Fin n) (Fin n) K) * x * (g⁻¹ : Matrix (Fin n) (Fin n) K) = y`,

where `g⁻¹` is the inverse in `Matrix.GeneralLinearGroup (Fin n) K`.

`x.charpoly` is Mathlib's characteristic polynomial `det (X • 1 - x)`. The
field is arbitrary, the polynomial `c` is arbitrary (for a polynomial that is
not a characteristic polynomial, `s = ∅` works), and `n = 0` is allowed. The
matrices `x` and `y` need not be invertible. The proposition does not assert
that the elements of `s` are pairwise non-conjugate or have characteristic
polynomial `c`.

## Provenance

The registered original is Bernstein and Zelevinsky, *Representations of the
group GL(n,F), where F is a non-Archimedean local field (survey)* (1976),
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

In Section 7.3 (printed pp.57–58) the source verifies constructiveness of the
conjugation action of `GL(n,F)` on itself, condition a) of Theorem 6.13, from
Section 6.15 (Theorem A) and Example 6.16 (printed pp.56–57). Remark 7.4 (printed p.58) says that
constructiveness can also be verified directly and leaves this to the reader.

The present proposition is an internal prerequisite and not a source
statement. It is the finiteness behind such a direct verification. The
published proof `Langlands.generalLinearConjugationDistributionTranspose` of
`Langlands.GeneralLinearConjugationDistributionTransposeStatement`, in
`Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof`, uses it to
see that each fiber of the characteristic-polynomial map on the general linear
group is a finite union of conjugacy classes. It is classical linear
algebra and is stated over an arbitrary field. Mathlib, at the pinned commit,
contains no rational canonical form from which it could be read off directly.

## Why the proposition is true

This sketch explains why the proposition is true; it is not the Lean proof.
The published proof differs from it; see the end of this section. Make
`K^n` a finitely generated torsion module over the principal ideal domain
`K[X]`, with `X` acting by `x`; by Cayley–Hamilton it is killed by
`x.charpoly`. By Mathlib's `Module.equiv_directSum_of_isTorsion`, it is
isomorphic to a finite direct sum of modules `K[X]/(p_i^(e_i))` with `p_i`
irreducible. The characteristic polynomial of the sum is the product of the
normalized `p_i^(e_i)`, so each of them is a monic divisor of `c`, and there
are at most `n` nonzero summands. Hence only finitely many isomorphism classes
of such `K[X]`-modules occur. Two matrices whose `K[X]`-modules are isomorphic
are conjugate by the matrix of a `K`-linear isomorphism intertwining them.
Choosing one matrix in each occurring class gives `s`.

The published proof `matrixCharpolyFiniteConjugacy` does not count
prime-power summands and uses no characteristic-polynomial formula for a direct
sum. For nonzero `c`, Cayley–Hamilton shows that `c` annihilates every matrix
in the fiber.
The published `Langlands.polynomialModuleBoundedCyclicDecomposition` then
presents each such polynomial module as a product of at most `n` cyclic
quotients by monic divisors of `c`. Finitely many such tuples occur. One
matrix is chosen for each tuple realized in the fiber. The published
`Langlands.matrixAEvalConjugacy` turns the resulting polynomial-module
equivalence into a conjugating matrix. For `c = 0` the fiber is empty, and the
empty set is used.
