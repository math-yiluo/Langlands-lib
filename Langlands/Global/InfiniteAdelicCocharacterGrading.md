# Cocharacter eigenspaces at infinity

Let \(G\) be an affine group over a number field \(F\) with a smooth
relative dimension, and let \(\chi\) be a cocharacter of \(G\).
The cocharacter element at infinity is the real tangent realization
of the image of \(1+\varepsilon\) under \(\chi\) on dual-number points.

For a subspace \(W\) of the algebraic Lie kernel over \(F\),
`realizedTangentSubmodule` takes the real span of the images of vectors
in \(W\). Additivity of `tangentVector` makes this operation commute
with sums. The realization of the whole algebraic Lie kernel is the
whole real tangent space by `span_range_tangentVector`. For a morphism
of smooth affine groups, `realizedTangentSubmodule_range` identifies the
realization of its algebraic differential's image with the image of its
real tangent map. This uses naturality of `tangentVector` and the spanning
result in the source.

The algebraic weight space for the \(n\)-th power character consists
of eigenvectors of the adjoint action of \(d\chi(1)\) with eigenvalue
\(n\), by `Lie.lie_cocharacterLieVector_of_mem_weightSpace`. Since
`tangentVector` preserves brackets and rational scalar multiplication,
its real span lies in the \(n\)-eigenspace. The algebraic cocharacter
weight spaces span the Lie kernel, so their real realizations span the
tangent space. Independence of eigenspaces for the distinct real
integers gives equality with each eigenspace.
