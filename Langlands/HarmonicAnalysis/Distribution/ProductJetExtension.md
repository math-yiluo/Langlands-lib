# Extending a single transverse derivative on a product

Let \(\chi\) be a scalar test on an open set \(V\subset W\) that equals one
near zero. An \(F\)-valued multilinear coefficient test \(a\) on
\(U\subset E\) extends to the test
\[
  (x,y)\longmapsto \chi(y)\,(i!)^{-1}a(x)(y,\ldots,y)
\]
on \(U\times V\). The extension is continuous and real linear. The
operator that evaluates the diagonal tuple is the diagonal of a
continuous multilinear map into the space of evaluation operators.
Multiplying it by the cutoff makes it a test, and the fixed-kernel
construction supplies continuity in \(a\).

The pure transverse derivative at \((x,0)\) is the derivative of the
restriction \(y\mapsto f(x,y)\) at zero, by the translation formula
and the linear chain rule. This derivative depends only on the germ at
zero, so the cutoff can be omitted when computing it. The diagonal
polynomial has a power series with one nonzero degree. Mathlib's
iterated derivative formula expresses the degree-\(i\) derivative as a
sum over permutations. For symmetric \(a(x)\), these \(i!\) terms
cancel the factorial normalization and recover \(a(x)\). All other
transverse derivatives vanish. A smooth bump with closed ball support
gives an admissible cutoff whenever \(W\) is finite-dimensional and
\(0\in V\).

This internal construction supplies the individual transverse
coefficients used in finite-jet arguments for distributions on a
zero section.
