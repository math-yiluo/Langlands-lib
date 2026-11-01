# Literal model-star determinant coefficients

This derived prerequisite connects the fixed-character model-star diagonal
restriction with the actual transformed before-shell kernel. It implements
the substitution on printed p.437 of JPSS Section 6.3 preceding formula (14).
The original is `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.404–405 and 427–439 were read in preceding work; p.437 was
visually reread for this calculation. The earlier bounded registered-source
and correction-note audit found no JPSS-specific registered erratum.

For actual inner rank `n=r+1`, let `c=-I_n`, let `PhiHat` be the full plus
square Fourier transform using the supplied character `psi` and the supplied
self-dual scalar Haar `mu`, and put `PhiD(X)=PhiHat(-X)`. The definition
`adjacentRankReflectedTest` constructs this reflection as a Schwartz test by
pullback along the negation homeomorphism. Its group multiplication lemma
identifies `PhiD(h*g)` with `PhiHat(h*c*g)`.

`adjacentRankModelStarScalar F chi r` is exactly
`chi^-1(det c)`, kept as the literal character scalar from the model-star
sign matrix. No scalar from a Haar comparison is introduced.

Write `WD(x)=W(w_n*iota(x))` for the actual dual model vector recast as a
standard vector for `psi.scale(-1)`, and let `aD(h)` be
`chi^-1(det h) |det h|^(r/2)`. The weighted diagonal theorem proves

```text
M(w_(n+1)*iota(diag(g,1))) |det g|^(s-1/2)
  = chi^-1(det c) |det g|^s
    * integral PhiD(h) phiHat(lastRow(g*h^-1)) WD(g*h^-1) aD(h) dh.
```

The proof applies the already proved literal fixed-`psi` model-star
restriction. It reflects the square test, identifies the determinant of
`zeta*diag(g,1)` with that of `c*g`, and proves that the determinant weight
of `c` is one. Right translation in the same general-linear Haar measure
changes `h*g` into `h`; multiplicativity of the character weight gives the
integral transformation. Exponent addition cancels the two half-weights,
exactly as for the original model. The Fourier action remains the original
fixed-`psi` action before the resulting scalar function is recast. The
weighted identity itself is a totalized integral equality and asserts no
additional convergence.

For an actual Whittaker function `U` explicitly realized by the separated
model, the slice theorem uses
`UD = inverseAsScaledStandard psi (dualFunctionEquiv psi (r+1) U)`.
Its underlying function is exactly `U(w_(n+1)*iota(-))`. The theorem
identifies its actual corank-one integrand at parameter zero on every
determinant slice with the inner integral of the transformed
`adjacentRankBeforeShearKernel`, multiplied by `chi^-1(det c)`.
The second function is any inverse Whittaker function for `psi.scale(-1)`.
The proof passes to a quotient representative, applies the weighted
identity at zero, and moves the second function into the group integral.
On the complement of the determinant slice both expressions vanish.

The first representation has full Whittaker type and may be reducible.
The specified functional may be zero. Its carrier has only algebraic
additive and complex-module structures and retains an independent
universe. All natural `r`, including actual inner rank one, and all
canonical p-adic field structures are retained. Model realization is
explicit intermediate data; this module neither constructs it nor adds it
to either parent gamma/L statement. Global rational products, matrix
analytic witnesses, functional equations and parent factor conclusions
remain separate.
