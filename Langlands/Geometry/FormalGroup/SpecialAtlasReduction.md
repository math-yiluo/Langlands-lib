# Reduction of actual special formal division-order atlases

This internal construction specializes `SpecialAtlasBaseChangeAlong` and
`AtlasOrderReduction` to the canonical quotient of a nilpotent coefficient
algebra. It makes no new assertion from the original literature.

Let K be a nonarchimedean local field, D a finite-dimensional central
division K-algebra, and `iota : L →ₐ[K] D` an embedded field. Each special
atlas supplies the existing unramified full-degree integer-subfield
certificate and the geometric tangent-character condition. Write d for
`CentralSimple.reducedDegree K D`; the coordinate type is `Fin d`.
Existence of the embedded unramified subfield and specialization to
invariant 1/d remain separate.

Let R be a commutative O_K-algebra, r an element of R, and A an object of
`Nilp R r`. The actual coefficient ring of X is A. Its reduction is the
principal-ideal quotient A/(r), with the structural composite O_K-algebra.
This quotient need not be a residue field or a reduced ring. No flatness
or injectivity is assumed. K and D have universe u, R has universe v,
A and its coefficient tests have universe w, and L has universe s.
Complete compatible families have universe w+1. Covers may be infinite.
The special tangent condition uses its existing field-test universe
`max u w`.

`reduction X` extends all the actual special data along
`Nilp.quotientO O_K A`. The atlas and order projection laws identify it
exactly with the existing ambient and full-order reductions. Its
principal generators are precisely the images of the original
generators. The supplied embedded unramified subfield certificate is
retained, and the existing special base-change construction extends the
geometric tangent characters along each chosen chart coefficient map.

`reduction_height` retains `HasHeightSquared pi`. Its input requires
irreducibility of pi in O_K, nilpotence of its actual image in A, and
actual scalar-kernel height d² certificates on every original chart,
with `Nat.card` of K's residue field as q. This theorem applies to any
such pi; no relation between pi and the distinguished element r is
required. The quotient map preserves the input nilpotence certificate,
and the existing coefficient-extension theorem extends the actual chart
kernel certificates. Specialness alone supplies no height certificate.

`reductionPointEquiv` is linear over the entire division order
`IntegerRing K D`. It identifies complete compatible families on every
quotient-algebra test with the original families on that test restricted
along the quotient map. Its forgetful equation gives exactly the
ambient quotient family comparison. Its naturality equation and
`reductionPointFunctorIso` concern all further coefficient-test maps.
They do not identify points on A with points on A/(r).

`reductionHom` reduces actual same-cover full-order formal maps.
`reductionHom_val` identifies their underlying ambient formal maps.
The forward and inverse family equations specialize the existing
full-order reduction squares for this same actual formal map.
`reductionIso` reduces both actual formal maps and their two inverse
equations; its projection laws expose precisely the reductions of the
original hom and inv. Its forward family equation evaluates this
constructed isomorphism. The original and target covers must agree for
these map operations.

All constructions are direct specializations of the imported operations;
the proofs are their projection and naturality laws. This module does not
descend reduction to comparison classes, compare changing Nilp bases,
construct a framing or polarization, or assert representability.
