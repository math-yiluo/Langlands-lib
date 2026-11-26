# Fixed-level smoothing on the actual cuspidal Hilbert space

Let \(G\) be an affine connected reductive group over a number field,
with the positive split central torus and quotient measures of
`fullAEL2CuspidalSubmodule`. Write an adelic point as
\(x=(x_\infty,x_f)\) using `AdelicGroupPoints.split`.
The full adelic measure is supplied as the transport of the product of
left Haar measures on the two factors.

For a continuous compactly supported infinite test \(f\) and a finite
Hecke test \(g\), `adelicSmoothingWeight` is
\(x\mapsto f^{*(k+1)}(x_\infty)g(x_f)\).
The infinite convolution power is continuous and compactly supported.
Together with integrability of the finite test, product integration gives
integrability of the weight on the full adelic group. Write \(R(g,k)\)
for `adelicSmoothingAction`, its integrated operator on the actual
cuspidal Hilbert space.

For a compact open subgroup \(K\) of the finite factor let \(e_K\) be
its normalized indicator and set \(T=R(e_K,0)\). If \(g\) is right
\(K\)-invariant and a bounded operator \(U\) commutes with \(T\),
`AdelicFixedLevelSmoothingStatement` gives
\[
   (R(g,0)U)T^k = R(g,k)U \qquad (k\geq 0).
\]
The proof pulls back the right action and the weights along the
measure-preserving adelic product isomorphism. The Bochner integrals
agree on every vector. `fixedLevelSmoothingPowers` then gives the
displayed equality for the original operators.

`adelicSmoothingAction_mem_of_invariant` shows that each \(R(g,k)\)
preserves any complete subspace invariant under adelic right
translation. Every weighted orbit of a vector in that subspace lies
in the subspace, so its Bochner integral does too.

The operator identity supplies the fixed-level archimedean variation
for the comparison motivated by Arthur–Clozel, *Simple Algebras, Base
Change, and the Advanced Theory of the Trace Formula* (1989), Ch. 1,
§4, formulas (4.6)–(4.7), printed pp. 43–44 (PDF pp. 57–58).

Source ID `arthur-clozel-1989-base-change`,
SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
