# The trace form and the matrix conjugation conormal

The internal bilinear form `matrixTraceBilin` is \((A,B)\mapsto\operatorname{tr}(AB)\) on square matrices over a field. Matrix units detect every entry, giving nondegeneracy. Cyclicity of trace gives symmetry and invariance under conjugation. Applying transpose to both variables also preserves the form.

For a fixed matrix \(C\), `matrixConjugationTangent C` sends \(X\) to \(XC-CX\). Over the reals this is the derivative at zero of \(\exp(tX)C\exp(-tX)\). Its image has trace annihilator exactly the centralizer of \(C\). Indeed, pairing \(XC-CX\) with \(A\) gives the trace pairing of \(X\) with \(CA-AC\), and nondegeneracy detects when the latter commutator vanishes.

More generally, for any subspace \(W\) of matrices, the trace form identifies its trace orthogonal complement with the algebraic dual of the quotient by \(W\). The induced functional at the class of \(X\) is \(X\mapsto\operatorname{tr}(AX)\).
