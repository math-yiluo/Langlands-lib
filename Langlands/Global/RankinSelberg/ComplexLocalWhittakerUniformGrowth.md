# Simple-root decay from uniform growth of Whittaker derivatives

The growth hypothesis is on the image of each simple-root derivative
word of a fixed inducing vector. Along
\(g=\operatorname{diag}(e^{x_i})k\), the bound has exponent
\(M\sum_i |x_i|\), with one \(M\) for all words and a constant for each
word that is uniform in \(k\).

For a chosen decay order \(L\), take a natural number \(j\ge L\).
At \(x\), select the roots with \(x_i-x_{i+1}\ge 0\)
and repeat each selected direction \(j\) times. The derivative word
identity gives the multiplier with norm
\[
|\gamma|^{\text{length of the word}}\,
e^{j\sum_i \max(x_i-x_{i+1},0)} .
\]
Its norm is positive. Divide the growth estimate for that word by this
multiplier. The sum of the rescaled constants over the finitely many
subsets of simple roots gives one constant for all \(x\). Replacing
\(j\) by \(L\) in the resulting decay bound preserves the inequality.

The functions satisfying this estimate form a complex submodule.
For addition the proof takes the larger fixed exponent and adds
the two constants. For scalar multiplication it multiplies the constant
by the norm of the scalar. The estimate passes from each intertwiner's
range to their supremum, which is the Library's complex Whittaker model.
This implements the implication from uniform growth to simple-root
decay in Jacquet's Proposition 3.1, printed and PDF pp. 15–16 of
*Archimedean Rankin–Selberg integrals* (2009).
