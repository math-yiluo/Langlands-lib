# Polynomial bounds on norm-one partial convolution

`exists_normOnePartialConvolution_bound` works on the norm-one subgroup of
the adelic points of an affine group scheme locally of finite type over a
number field. It uses a positive-size closed matrix embedding \(\rho\), the
central split torus data of `normOneDecomposition`, and right invariance of
norm-one Haar. The class \(v\) belongs to \(L^2\) of the positive rational
quotient, with its measure transported from the norm-one rational quotient.

Fix a compact set \(D\) and a real bound \(M\geq 0\). There are \(C\geq 0\)
and \(d\in\mathbb N\) such that for every compactly supported continuous
kernel \(K\) with \(\operatorname{tsupport} K\subseteq D\) and
\(\lVert K\rVert_\infty\leq M\), the partial convolution satisfies

\[
  \bigl|\operatorname{normOnePartialConvolution}(K,v)(x)\bigr|
  \leq C\,\operatorname{adelicHeight}_{\rho}(x)^d\,\|v\|_2
  \qquad(x\in H(\mathbb A)^1).
\]

The proof fixes a positive bump on the positive subgroup. The full
convolution kernel `normOneSmoothingKernel` is uniformly bounded and
supported in one compact set \(S\), obtained by multiplying the support of
the bump by the inverse of \(D\) intersected with the norm-one subgroup.
The quotient convolution kernel theorem bounds the evaluation by the
\(L^2\) norm of its kernel vector times \(\|v\|_2\). The square of that vector
norm is bounded using the uniform kernel bound, the ambient Haar mass of
\(S\), and the subgroup Haar mass of the conjugate of \(SS^{-1}\).
The all-point conjugate mass estimate
`adelicPositiveRationalConjugateGrowth_allPoints` bounds the last factor by
a height power. The comparison of full and partial convolution divides by
the fixed, nonzero integral of the bump for normalized positive Haar.

The estimate gives uniform control of the reflected kernels that occur
when smoothing families of Levi classes in the norm-one fibre pairing
construction of Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series*, §6.2, equation (6.8).
