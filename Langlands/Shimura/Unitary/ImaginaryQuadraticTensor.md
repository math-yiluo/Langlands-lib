# Imaginary quadratic tensor splitting

This internal algebraic prerequisite constructs the actual evaluation
homomorphism from `K ⊗[ℚ] L` to `K × K`, for a CM number field `L`
and a characteristic-zero field `K` containing it. Its formula on a pure tensor is
`(k * incl(r), k * incl(conj_L(r)))`, using Mathlib's actual CM
complex conjugation. No algebra equivalence is supplied as input.

Surjectivity holds without the quadratic-degree hypothesis. Nontriviality
of complex conjugation gives an element `t` with different natural and
conjugate images `a` and `b`. For a prescribed pair `(x,y)`, put
`c = (x-y)/(a-b)` and `d = x-c*a`. The tensor
`d ⊗ 1 + c ⊗ t` maps to `(x,y)`.

Under `IsQuadraticExtension ℚ L`, both source and target have dimension
two over `K`. The finite-dimensional injectivity-surjectivity criterion
therefore proves evaluation bijective. `tensorEquiv` is the resulting
actual algebra equivalence, with the same pure-tensor formula.

For every commutative `K`-algebra `R` with the compatible rational
algebra structure, `algebraEquiv` constructs
`R ⊗[ℚ] L ≃ₐ[R] R × R`. It composes cancellation of iterated base
change, scalar extension of `tensorEquiv`, distribution over a binary
product, and the two tensor unitors. Its pure-tensor formula is the same
evaluation formula, with the two field images mapped into `R`. The ring
`R` may have nilpotents or be the zero ring; no reducedness or additional
flatness assumption is imposed.

This is a derived algebraic construction for the natural/conjugate
characters in the Harris geometry development. It asserts no identification
of Lie eigensubsheaves with scalar-extension tensor factors, no geometric
rank or compatibility assertion, and no moduli representability result.
