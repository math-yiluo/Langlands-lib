# Weyl symmetry of finite normalized convolution families

`exists_symmetricFamily_of_finiteConvolutionExpansions` acts on a smooth
compactly supported presentation of a symmetric inducing family. It assumes
finite regular intertwining expansions and finite normalized convolution
expansions in square-integrable inducing forms. The kernel is continuous and
compactly supported. The result uses the same `symmetricFamilySpace` and the
same supplied `Mop`.

The new inducing forms are the forms appearing in the convolved expansions,
indexed by a finite disjoint union over the original forms. The new coefficient
of each form multiplies the original smooth compactly supported coefficient
by the corresponding entire convolution coefficient on the imaginary slice.
The ambient realization theorem produces a spectral family with these forms
and coefficients.

For a Weyl map, the supplied measure preservation lets the proof compare the
source and target presentations at almost every source parameter. The original
Hilbert-space Weyl equality identifies the two associated pointwise inducing
functions. Apply normalized convolution at the target parameter to that
identity. Continued covariance identifies the resulting sum with the finite
expansion of the supplied imaginary operator applied to the new source
presentation. The target Iwasawa restrictions therefore agree almost
everywhere, which proves the new Weyl equality in the weighted Hilbert space.

This is a finite-presentation form of the symmetry-preserving action in
J. Arthur, *An introduction to the trace formula* (2005), §7, printed
pp. 34–35 (volume PDF pp. 46–47), registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
