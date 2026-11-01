# Scalar regularity of whole adjacent-rank test tensors

This internal helper defines two scalar functions for an arbitrary algebraic
test tensor `Psi`, quasicharacter `chi` and complex exponent `s`:

```text
Source(Psi)(h) = Eval(Psi)(K(h), h^-1) * chi(det h) * |det h|^s,
Target(Psi)(h) = Eval(Psi)(K(h), w * inverseTranspose(h^-1))
                  * chi^-1(det h) * |det h|^s.
```

The coefficient space and its standard additive character are the original ones
in both definitions. No Fourier action is included in these definitions: an
acted or Fourier-transformed test tensor may simply be supplied as `Psi`.

For a canonical p-adic field in universe uF and a smooth representation on
any complex module in independent universe uV, both functions are continuous
with compact support. All natural `r`, zero functionals and arbitrary finite
tensors are included. The result needs no topology or norm on the module or
the coefficient image and no irreducibility assumption.

The proof uses `adjacentRankTestSpace_induction`. For a pure tensor, the kernel
and the displayed group argument are continuous. Smooth coefficients,
quasicharacters and the canonical determinant weight are continuous, so their
product is continuous. The published `adjacentRankPure_hasCompactSupport`
gives the source support, and the imported
`adjacentRankTransformedPure_hasCompactSupport` gives the target support.
Multiplication by the two scalar weights preserves compact support.
Linearity of tensor evaluation proves additivity of both scalar functions;
finite addition preserves continuity and compact support.

The provenance is internal: these are consequences of the existing test
evaluation, coefficient continuity and the original and transformed pure
support results. The helper supplies the regularity hypotheses of the
unipotent-orbit integration adapter. It asserts neither a Fourier equality
nor the adjacent-rank model-star identity.
