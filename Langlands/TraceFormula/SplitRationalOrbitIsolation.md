# Split matching tests that isolate rational classes

`splitRationalOrbitIsolation` proves `SplitRationalOrbitIsolationStatement`.
It takes finite lists of ordinary and twisted rational matrices over a
cyclic field extension \(L/K\) of degree \(m+1\) with a generator
\(\sigma\), and a regular associated pair to retain. The rational
localizations into a nonarchimedean local field and its cyclic algebra
of \(m+1\) split factors preserve norm association. The upper ambient
Haar measure is the product of the lower measure in split coordinates,
as required by `IsSplitProductHaar`.
The open neighbourhoods contain the chosen split tuple and its ordered
product, respectively. The lemma constructs concordant split tensor
and convolution tests supported within these neighbourhoods. The tensor
is one at the chosen upper point and the convolution is positive at its
ordered product. For each list, a local orbit on which the corresponding
test is nonzero comes from the selected rational conjugacy class.

The rational cutoff is first constructed downstairs. The ordered
product of the chosen upper point is locally conjugate to the
image of the chosen base point, by the local norm association.
The proof uses this conjugacy to impose the cutoff on the product
of the split coordinates. The cyclic norm lemma supplies a rational
base matrix associated with each twisted rational representative.
`splitOrbitCutoff` then supplies the tensor and convolution.
A twisted conjugate in the support of
the tensor has ordered product in the refined neighbourhood.
The norm association of the corresponding rational representative
identifies that product up to local conjugacy with the representative's
associated base matrix. The rational cutoff then gives rational
conjugacy of the corresponding base classes. The cyclic norm lemma
recovers the claimed rational twisted conjugacy. The ordinary
assertion uses the cutoff directly.

This is an internal implementation of the support refinement at a
split auxiliary place in Arthur–Clozel, Chapter 1, pp. 43 and 46,
and Henniart–Lemaire, I.6.8, pp. 49–50 (PDF pp. 57–58). The finite
rational lists and the compatible split localization are inputs.
