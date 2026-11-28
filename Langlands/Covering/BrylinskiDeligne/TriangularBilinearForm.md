# Strictly lower triangular bilinear forms for sign extensions

Let \(e_i\) be a basis of an abelian group over \(\mathbb Z\), indexed by a
linearly ordered set. For an integral bilinear form \(B\),
`strictLowerBilinearForm e B` is the bilinear form \(D\) constructed by
linear extension in both variables from the coefficients
\[
  D(e_i,e_j)=
  \begin{cases}
    B(e_i,e_j), & j<i,\\
    0, & i\le j.
  \end{cases}
\]
`strictLowerBilinearForm_apply_basis` proves this formula.

When \(B\) is symmetric and the basis values \(B(e_i,e_i)\) are even,
`even_sub_strictLowerBilinearForm` proves that
\(B(y,z)-D(y,z)-D(z,y)\) is even for all \(y,z\). The proof builds a
bilinear form \(H\) with diagonal coefficients \(B(e_i,e_i)/2\) and
off-diagonal coefficients zero. Evaluating on basis pairs gives
\(B=D+D^{\mathsf T}+2H\), so the difference is \(2H(y,z)\).

`strictLowerBilinearForm_ordered_sum` uses bilinearity to show that \(D\)
pairs an integer multiple of \(e_i\) with a sum of multiples of \(e_j\)
to zero when all the \(j\) satisfy \(i\le j\). This vanishing removes
the cocycle signs when multiplying lifts in increasing order. For a finite
basis, `sorted_sum_basis_repr` reconstructs a vector from its basis
coordinates by summing over the sorted list of all indices. The proof
converts that list sum to the ordinary basis sum. These results include
the empty basis and use arbitrary integer coordinates.

The construction is a coordinate realization of the sign-cocycle law and
the simple-coroot commutator relations. Brylinski–Deligne, *Central extensions
of reductive groups by \(K_2\)*, Proposition 3.11, formula (3.11.1) and its
proof, give the exponent of the commutator modulo two. The registered source
is `brylinski-deligne-2001-central-extensions`, SHA-256
`24ea359c677a6c767a5eeeffad7d39f7019d875d3f18c5280f5086414e182ba5`,
printed pp. 31–32 (PDF pp. 27–28).

Gan–Gao, *The Langlands–Weissman program for Brylinski–Deligne extensions*,
§2.4 gives the rigidifying simple-coroot generators and their relations,
and §2.6 gives the product law. The registered source is
`gan-gao-2018-langlands-weissman-program`, SHA-256
`fabbe056bdec2a5d57a22a0d3ad275640d0343c3f71092a7df427f7ebaebe892`,
printed pp. 197–198 and 200 (PDF pp. 215–216 and 218).
