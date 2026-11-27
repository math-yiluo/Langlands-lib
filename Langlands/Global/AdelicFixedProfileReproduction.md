# An archimedean reproducer for fixed compact profiles

`exists_reproducingKernel_of_centerEigenvalue` works on the actual archimedean
points of a connected reductive group. Fix a maximal compact subgroup `K` and a
finite-dimensional space `E` of functions on `K`. The theorem chooses one element
`z` of the enveloping centre. For each eigenvalue `c`, it gives one continuous
compactly supported kernel that reproduces evaluation at the identity on every
smooth eigenfunction of `z` with eigenvalue `c` whose right compact profiles
`k ↦ f(a * k)` lie in `E` for all `a`.

`adelicAdaptedCasimir` gives a spanning sum of squares `S`, with `z = S - C` for
the doubled compact sum of squares `C`. `exists_monic_aeval_compactSquares` gives a
monic polynomial `q` whose application to `C` kills functions with these profiles.
On the specified eigenspace, `S - c` acts as `C`, and centrality lets this equality
iterate. Consequently `X * q(X - c)` evaluated at `S` kills every such function.
The factor `X` makes the order positive. Expressing the operator as a sum of Lie
words gives the elliptic principal symbol, since the real sum of squares of the
symbols of the spanning vectors is positive off the zero covector.

The kernel of the operator is invariant under left translation. The elliptic
estimate `exists_lieWord_l2_evaluation` bounds evaluation at the identity there
by an `L²` norm on a compact set. `exists_compact_reproducingKernel_of_l2_evaluation`
represents that evaluation by a continuous compactly supported kernel. The
inversion invariance of archimedean Haar used by that result follows from the
modular character comparison with the full adelic group, whose Haar measure is
right invariant for connected reductive `G`.

This is the elliptic reproduction argument of Harish-Chandra, *Discrete series
for semisimple Lie groups II*, Acta Math. 116 (1966), §8, Theorem 1 and footnote 1,
pp. 18–19, specialized here to a single central eigenvalue and a specified profile
space. Registered as `harish-chandra-1966-discrete-series-ii`, SHA-256
`3ad72529bddbfe96e537bc3f49df6aa3223169c2abbe265d858c32c48545f3d9`.
The adapted Casimir is the same operator used in the proof of Lemma 33, §17,
pp. 108–109, of Harish-Chandra, *Two theorems on semi-simple Lie groups* (1966).
The general adelic reproducer uses the same local evaluation argument.
[Adelic reproducing kernel](AdelicReproducingKernelProof.md)
