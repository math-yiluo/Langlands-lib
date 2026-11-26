# Reduction to character regularity on the cyclic semidirect product

`CyclicGLSemidirect` is \(\mathrm{GL}_n(E)\rtimes\mathbb Z/l\mathbb Z\),
with the module topology on the matrix group and discrete component
coordinates. `cyclicGLAdjoint` uses the actual action on \(M_n(E)\) over
\(F\), sending \(X\) to \(\delta\sigma^i(X)\delta^{-1}\) at \((\delta,i)\).
`IsCyclicGLRegular` compares the algebraic multiplicity of \(1\) in this
operator with the multiplicity at every element in the same component.

`twistedCharacterSemidirectReduction` proves the full-universe conditional
implication to `TwistedCharacterLocalIntegrabilityStatement`. The premises
are `CyclicGLCharacterRegularityStatement`, the character theorem on these
semidirect products, and `SigmaRegularCyclicGLComparisonStatement`, the
forward comparison at the generator component.

The proof scales the given intertwiner to have \(l\)-th power one. The
resulting representation of the semidirect product is admissible because
its restriction along the open matrix subgroup is admissible, and
irreducible by the same restriction. The ambient character function pulls
back along the open generator slice to the twisted character function for
the normalized intertwiner, with the distribution identity holding for
every Haar measure. Scaling recovers the character of the given
intertwiner. The regular-locus comparison and continuity of the slice
give the required local constancy.

Clozel, *Characters of non-connected, reductive p-adic groups*, §2.2
and Theorem 1 in §3.3, printed pp. 151–153, defines regularity by the
first nonzero coefficient of the shifted adjoint characteristic
polynomial and gives the character theorem. Source ID
`clozel-1987-nonconnected-characters`, SHA-256
`11f4169a65a0716f162928dd4ed87995bb60cb5275cecf7896ee655cec86eb29`.
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula*, Chapter 1, §2.1 and Proposition 2.2, printed
pp. 10–12, uses the normalization, extension and component restriction
for cyclic field extensions. Source ID `arthur-clozel-1989-base-change`,
SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
