# Equality of the half moduli on the outer positive split component

`Langlands.Global.standardNestedHalfModulusCompatibility` proves
`Langlands.Global.StandardNestedHalfModulusCompatibilityStatement`. Let
\(Q\subset P\) be nested standard parabolics. If an adelic point of the positive
split component of \(P\) and one of the positive split component of \(Q\) have the
same image in \(G(\mathbb A_F)\), their half moduli agree. This is the modulus
comparison used when restricting normalized exponents in Delorme,
*On the spectral theorem of Langlands* (2023), §3.2, equations (3.5)–(3.6).

Write \(j\) for the injective map of the Lie algebras of \(Q\) and \(P\) over the
adeles. The adjoint actions \(f\) and \(g\) of the two points intertwine along
\(j\). On dual numbers, the action of \(g-1\) is a commutator with the split
component of \(P\), up to inversion. This commutator lies in the unipotent
radical of \(P\), which is contained in \(Q\). Reduction to the identity on the
dual numbers therefore puts the image of \(g-1\) in the range of \(j\). Lifting
through that range gives a linear map \(q\) with \(g=1+jq\) and \(f=1+qj\).
In finite coordinate bases `Matrix.det_one_add_mul_comm` gives equal
determinants over the adeles. The adjoint determinant characters, normalized
idele norms and positive square roots then give the equality of half moduli.
