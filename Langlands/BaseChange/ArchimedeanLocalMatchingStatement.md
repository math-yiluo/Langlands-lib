# Matching at infinite places

The definitions and proposition targets are in `Langlands.BaseChange`.
`IsArchimedeanTest` is compact support and real manifold smoothness on the
actual matrix group with the Library's `matrixModel`. For
`IsBiFiniteArchimedeanTest`, the translates by the standard orthogonal or
unitary maximal compact span finite-dimensional spaces on each side.

`SplitArchimedeanMatchingStatement` covers both real and complex split
places. With `l + 1` factors the automorphism is the cyclic shift
`(σx)_i = x_{i+1}` with indices modulo `l + 1`. The product Haar condition
uses the pushforward of the measure on `GL_n(F^{l+1})` by the ordered
coordinate projections and the product of the `l + 1` copies of the same
base Haar measure. The proposition asks that the split Haar measure exists
and that for any such measure the tensor of smooth compactly supported tests
matches its smooth compactly supported convolution. If all factors are
bi-finite, the convolution is bi-finite. Its left translates come from the
first factor and its right translates come from the last. The definition
`archimedeanConvolutionProduct` folds from factor zero in increasing order,
using the convolution `∫ f(x) h(x⁻¹ g) dx`, with the same base Haar measure.
This order agrees with the first coordinate of the cyclic norm product in
Arthur–Clozel I.5, (5.1)–(5.2), printed pp. 48–49. The complex instance is
the split test comparison needed at every infinite place of a totally
complex base.

`NonsplitRealMatchingStatement` states Arthur–Clozel I.7.3 (printed
pp. 73–74) for `ℂ/ℝ` with complex conjugation. Every upper test in the
bi-finite space has a lower match in the bi-finite space. A lower test in
that space has an upper match when its orbital integrals vanish at regular
semisimple non-norms. The ambient Haar measures are supplied. The same
`AreConcordant` as at finite places compares regular orbital integrals with
associated centralizer measures and their compatible quotient measures.
The nonsplit statement is needed only for the unrestricted base-field route.

Source: Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced
Theory of the Trace Formula* (1989), I.5 and I.7.3, registered as
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The measure predicate and the right-associated fold are internal
representations of the product measure and the source's convolution.
