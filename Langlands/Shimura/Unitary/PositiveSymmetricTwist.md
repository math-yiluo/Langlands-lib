# Positive symmetric twists preserve real signatures

Let \(F/E\) be an extension of number fields with \(F\) totally real. Suppose an \(E\)-algebra map from \(F\) into an algebra with involution has symmetric image. For a field unit \(t\) of \(F\) that is positive at every real place of \(F\), `realSymmetricUnitSquareRoot` gives a symmetric unit in the scalar-extended algebra at any real embedding of \(E\). Its square is the scalar extension of the image of \(t\).

The completed tensor product of \(F\) at the real embedding is the product of its completions there. Each of these completions is identified with the real numbers. Taking a positive square root in each factor and transporting through the product isomorphism gives a square root of the tensor image of \(t\). Its square is a unit, so the root is a unit. Its image in the real algebra is symmetric by scalar extension of the original symmetry condition.

For a unitary involution on the algebra with totally real base \(E\) and totally complex quadratic center \(K/E\), `hasSignature_twist_of_positive` transports each supplied real signature chart through conjugation by the local symmetric square root. If \(b\) is the square root and \(\sigma'\) is the twisted involution at that real embedding, then \(b\sigma'(x)b^{-1}=\sigma(bxb^{-1})\), so the chart retains the same signature.
