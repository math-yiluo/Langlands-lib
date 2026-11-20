# Direct weak induction under a Hecke determinant twist

`Langlands.Automorphic.HeckeDeterminantTwistWeakInductionStatement`
concerns any actual cuspidal spectral presentation over `E` and any
Hecke character `ξ` of `E'` that induces its Euler system in the sense
of `SpectralSystem.IsWeakInductionOf`. If `ν` is a Hecke character of
`E`, the actual twisted presentation weakly induces
`ξ * HeckeCharacter.normComp ν`. The field universe follows the
existing norm-pullback implementation. The presentation carrier
universe is independent.

The determinant twist of the presentation is
`CuspidalSpectralPresentation.heckeDeterminantTwist`. Its construction
multiplies the finite slice and local factors, transports the tensor
presentation, and enlarges the exceptional set by the integral tail
for `ν`. Its Euler polynomial is obtained by substituting
`ν_v(π_v) X` for `X` in the original polynomial.

For the inducing-side comparison, work on the cofinite intersection
of the source comparison, the unramified places of `ν`, and the
complement of the presentation's exceptional set. At each such `v`
and each `w` above `v`, the ramification index is one. Use
`valuation_completionMap` to see that the image of the chosen lower
uniformizer `π_v` is an upper uniformizer. For an arbitrary chosen
upper uniformizer `π_w`, the quotient of `π_w` by this image is an
integral unit. Its local norm is an integral unit by
`localUnitNorm_integral`, so `ν_v` is trivial on that norm.
The norm of the image of `π_v` is `π_v` to the local degree, which
equals the residue degree `f(w | v)` by `localDegree_eq`. Therefore
`HeckeCharacter.normComp_finiteComponent` multiplies the coefficient
of `X ^ f(w | v)` by `ν_v(π_v) ^ f(w | v)`. This works for every
uniformizer family and gives the same substitution on the product
over `w`. Unramifiedness above `v` follows from
`HeckeCharacter.normComp_isUnramifiedAt` and closure under products.
The rank remains `[E' : E]`.

The class corollary uses `isWeakAutomorphicInductionOf_iff` at a
supplied representative to obtain its presentation. For untwisting,
apply the statement with `ν⁻¹` and cancel the two norm-pullback
factors pointwise.

## Provenance

The Euler comparison is derived from the rank-one inducing case of
Harris's Definition 1.3(b), printed p. 186, and the determinant
twist in Henniart, §2.2, printed p. 444. The local norm calculation
applies directly to the Euler denominators used to define weak
induction in the Library.
[Harris 1998](https://arxiv.org/abs/math/9611226), [Henniart 2000](https://doi.org/10.1007/s002229900033)
