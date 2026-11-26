# Bi-finite smooth convolution approximation

`Langlands.Global.AdelicBiFiniteConvolutionApproximationStatement` says that
one smooth compact test kernel approximates a finite family of continuous
\(K\)-finite functions by right convolution, to any tolerance on a
specified compact subset of the actual adelic group. Here \(K\) is a
compact subgroup of the infinite adelic group. Both the left and right
translate spans of the kernel under \(K\) are finite-dimensional.

The proof forms the finite-dimensional space spanned by the compact
orbits of the input family. The direct and inverse compact translations
give two coefficient families obtained by evaluation from endomorphisms
of this space. The existing compact-weight lemma supplies one weight
reproducing the direct translates and one weight reproducing the inverse
translates. Both weights have finite left translate span.

The ordinary smooth convolution approximation is used on the product
of the specified compact set with \(K\). The kernel is then averaged on
each side with the respective weight. Right averaging of the kernel
preserves its action on the given inputs. Left averaging of the kernel
averages the output error on the enlarged compact set. Its error is
bounded by the original error times the \(L^1\) norm of the left weight.
The compact averaging lemmas give the two finiteness conditions and the
required test-function properties. The module also proves the
approximation estimate when the two reproducing weights are supplied.

This implements the compactly filtered approximate identity of
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*,
I.4.5, printed p. 61
(`moeglin-waldspurger-1995-spectral-decomposition`, collection fingerprint
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`,
chapter `05.4_pp_49_77_Upper_bounds_as_functions_of_the_constant_term.pdf`,
SHA-256 `a72fe12ffc7707cc35e91375a8fc9dc62c35570afbbb061c0e7ff6db99a90d3d`).
The weights are found by reproducing point evaluations on finite
coefficient spaces.
