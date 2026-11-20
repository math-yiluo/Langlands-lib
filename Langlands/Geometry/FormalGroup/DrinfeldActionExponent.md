# The signed exponent in the Drinfeld group action

Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2 A, printed p. 109 (PDF p. 3), gives \(n=v(\det g_1)+v(\det g_2)\) in the action on framed triples. For the division-algebra factor we use the reduced norm. Both orders are normalized with a scalar uniformizer of order one.

`exponentHom` takes the determinant of the actual invertible matrix and the reduced norm of the actual division unit, applies the existing field-unit order, and adds the results in \(\mathbb Z\). It is a group homomorphism. The division contribution is also the negative logarithm of the canonical discrete division valuation. Its zero locus consists exactly of units from the actual integer order.

The reduced-norm order on a central scalar is the reduced degree times the scalar order. Thus the exponent vanishes on \((aI,a^{-1})\) and on the integer-order units in the division factor. For a scalar \(t\) of normalized order one, correcting \(g_2^d\) by the central scalar \(t^{-v(\operatorname{Nrd}g_2)}\) gives the image of an actual integer-order unit. These are the order identities used in the Frobenius correction and its height calculation.
