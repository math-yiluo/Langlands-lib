# The unramified Rankin–Selberg projection formula for weak induction

`WeakInductionPairEulerStatement` takes spectra `s` and `b` over `F` and
spectra `t` and `b'` over an extension `E`. Suppose `s` is an arithmetic
weak induction of `t`, and `b'` is an arithmetic weak base change of `b`.
At almost every finite place `v` of `F`, the pair Euler denominator of
`s` and `b` is the product of the pair Euler denominators of `t` and `b'`
at all places over `v`. Each upper polynomial is evaluated at `X^f`, where
`f` is that place's residue degree. The field universes are independent.

The proof writes the pair denominator as a product of the first Euler
denominator rescaled by each eigenvalue of the second spectrum. The
induced Euler denominator is already a product of substitutions. For a
second eigenvalue `z`, the substitution `X ↦ zX` changes the argument
`X^f` of each factor to `z^f X^f`. Thus the same product can be obtained
by taking the `f`th powers in the second spectrum upstairs and then
substituting `X ↦ X^f`. This comparison uses the enumerated spectrum formula
for `pairEulerPolynomial` and retains every multiplicity. The intersection
of the two cofinite comparison sets gives the result at the arithmetic
places.

This is the unramified polynomial form of the tensor-induction projection
formula used in Henniart–Herb (1995), Lemma 8.13, printed p. 179
(PDF p. 49), and §8.16(1), printed p. 180 (PDF p. 50). Their application
pairs two induced representations and expands the base change of the
second induction into its Galois orbit. The Lean result takes the weak base
change as a separate input and proves the polynomial step directly.
