# The real rank-raising determinant and integral identity

Let \(q=[g]\) be a class in \(N_{r+1}(\mathbb R)\backslash GL_{r+1}(\mathbb R)\).
For a row \(x\) and a trailing block \(h\in GL_1(\mathbb R)\), put
\(a(h)=\operatorname{diag}(\det h,1,\ldots,1)\). The right translate of the
padded class \([\operatorname{diag}(g,1)]\) by
\(\left(\begin{smallmatrix}a(h)^{-1}&0\\x&h\end{smallmatrix}\right)\) is
\([\left(\begin{smallmatrix}g a(h)^{-1}&0\\x&h\end{smallmatrix}\right)]\).
Its determinant absolute value equals \(|\det g|\).

For two prescribed compatible real quotient measures, the one-coordinate
quotient Haar formula identifies the larger measure as \(C\) times the
lower-block coordinates with measure \(|\det g|^{-1}dg\,dx\,d^\times h\).
Here \(C>0\), \(dx\) comes from the specified additive Haar measure, and
\(d^\times h\) is the specified nonzero, sigma-finite, right-invariant measure
finite on compact sets of the trailing group. Fixing \((x,h)\), the change of
variables \(g\mapsto g a(h)^{-1}\) preserves the smaller quotient measure.
After this substitution the determinant density is
\(|\det g|^{-1}|\det h|\). Multiplication by the larger spectral weight with
exponent \(s\) gives the smaller weight with exponent \(s-1\) and the
averaging factor \(|\det h|\).

The Lean proof applies the quotient Haar formula, moves the determinant
density into the integrand, and performs the substitution by a
measure-preserving map on the product. Absolute integrability of the
larger weighted kernel implies integrability of the transformed product
kernel. Fubini gives both integrability of the smaller averaged kernel and
its equality with the larger integral up to \(C\).

This is the change of variables in H. Jacquet, *Archimedean Rankin–Selberg
Integrals* (2009), proof of Lemma 14.1, author-posted pp. 106–107. The
statement permits any measurable coefficient on the larger quotient,
including a row test in the equal-rank integral. Its hypothesis is absolute
integrability at the chosen spectral parameter.
