# Finite Taylor coefficient detection for a matrix

Let \(A\) be a square matrix over the formal power series ring of a commutative
domain, with nonzero determinant of order \(d\). `coefficientCount A` is
\(d+1\). If every coordinate of \(A x\) vanishes through degree \(d\), then
every coordinate of \(x\) has zero constant coefficient.

The vanishing makes each entry of \(A x\) divisible by \(X^{d+1}\).
Multiplying by the adjugate preserves this divisibility and yields
\(\det(A)x\). If any entry of \(x\) has nonzero constant coefficient, its
order is zero, so its product with the determinant has order \(d\).
This contradicts divisibility by \(X^{d+1}\).

This is a one-parameter algebraic ingredient for the finite-order detection
step in R. P. Langlands, *On the notion of an automorphic representation*
(1979), Lemma 9, printed p. 207, PDF p. 202 of Corvallis Part I
(`langlands-1979-notion-automorphic-representation`). The matrix and its
nonzero determinant are inputs. An application to Eisenstein series must
first obtain them from a suitable family of sections and evaluations.
