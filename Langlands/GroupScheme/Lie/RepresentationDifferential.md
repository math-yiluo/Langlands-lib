# Actual tangent matrices for algebraic representations

For an arbitrary actual group scheme `G` over `Spec R` and a finite coordinate
representation `ρ : G → GL_n`, `ρ.tangentMatrix A X` extracts the matrix of
the actual image of `X` in the dual-number identity kernel of `GL_n(A)`.
`pointKernelEquiv_tangentMatrix` recovers the actual image point. The raw
kernel identity maps to zero, multiplication to addition, and epsilon scaling
to scalar multiplication. For affine `G`, `kernelDifferential` bundles this
construction as an `A`-linear map. Coefficient extension acts entrywise, and
restriction of representations agrees with composition of actual tangent maps.

This is a derived extension to arbitrary source group schemes of the existing
`MatrixRepresentation.differential` construction for general linear source.
Every proof uses actual point maps and the published dual-number matrix
coordinate equivalence. It is the representation differential used in the
semisimple-element discussion of Milne, *Algebraic Groups* (2017), Proposition
17.74 and the definition preceding Proposition 17.76, printed p.377 / PDF
p.393. No Lie-bracket preservation or classification of representations is
claimed by this file.
