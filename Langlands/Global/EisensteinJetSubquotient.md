# Simple subquotients detected by finitely many coefficient maps

Let \(D\) be a submodule of a section module \(J\), and let the restriction of
specialization \(q\) to \(D\) surject onto a simple module \(Q\). Suppose
vanishing under a finite family of coefficient maps \(c_i : J \to Z\) for
\(x \in D\) implies \(q(x)=0\). Then some submodule of \(Z\) surjects onto \(Q\).

Intersect \(D\) with the kernel of the first coefficient. The image under
specialization is zero or all of \(Q\) by simplicity. In the zero case,
`coefficientQuotient` descends the surjection to the image of that coefficient,
using the equivalence between its range and the quotient by its kernel. In the
surjective case, repeat on the intersection with one fewer coefficient. The
empty coefficient family would force specialization to vanish on all of \(D\),
which contradicts surjectivity onto a simple module.

This is the algebraic descent used after Lemma 7 in R. P. Langlands,
*On the notion of an automorphic representation* (1979), printed p. 206,
PDF p. 201 of Corvallis Part I (`langlands-1979-notion-automorphic-representation`).
Here \(Z\) is a single coefficient space, and the argument uses simplicity
directly on images in \(Q\). An application must supply the module actions,
the coefficient maps into automorphic forms, and the detection hypothesis.
