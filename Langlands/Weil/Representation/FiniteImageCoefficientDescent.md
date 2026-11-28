# Coefficient descent for irreducible representations of finite image

`Langlands.FiniteRepresentation.finiteImageCoefficientModel` takes
an extension \(E/k\) with \(k\) algebraically closed of characteristic
zero and an irreducible finite-dimensional \(E\)-representation \(A\)
of a group \(G\) with finite image. It constructs an irreducible
representation \(B\) over \(k\) with finite image and the same kernel
in \(G\). The `scalarEquiv` field is an invertible intertwiner from
\(E\otimes_k B\) to \(A\). Thus \(B\) has the rank of \(A\), and its
kernel inherits openness whenever the kernel of \(A\) is open.

`exists_extendCoefficients_of_finiteGroup` supplies the finite-group
step with the hypothesis that the group order is invertible in \(k\).
For a nonzero vector \(v\) of the target representation, evaluation of
the regular \(k[G]\)-module at \(v\) gives a nonzero module map.
Maschke's theorem makes the regular module the sum of its simple
submodules, so evaluation is nonzero on some simple submodule.
The proof lifts this restricted map to an \(E\)-linear intertwiner on
the tensor product. Absolute irreducibility keeps its source irreducible
after scalar extension, and Schur's lemma makes the lifted map invertible.
[Absolute irreducibility](AbsoluteIrreducibility.md)

For arbitrary \(G\), the construction applies the finite-group result
to the image of \(A\) in the units of its endomorphism ring. Inflation
of the model kills the kernel of \(A\). In the other direction, an
element acting by the identity on the model acts by the identity after
scalar extension and hence on \(A\).

The model over an algebraically closed subfield is the algebraic
ingredient in Henniart's change of coefficients for finite-image
representations. His argument uses the algebraic closures of
\(\mathbb Q\) inside the complex and \(\ell\)-adic coefficient fields.
See `henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§4.2, printed p. 510 (PDF p. 15), for this application.
