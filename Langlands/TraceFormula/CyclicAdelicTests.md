# Factorizable tests for the cyclic discrete comparison

The notation and definitions are in `Langlands.TraceFormula`. Write
`G = cyclicBaseGroup F n` for the actual group scheme `GL_n/F` and
`W = cyclicWeilGroup F E n` for its base change to `E` followed by Weil
restriction to `F`. An upper test is a function on the adelic points of
`W`, viewed as a function on the component of the fixed automorphism `σ`.
`cyclicWeilAdelicMap` is the map used by
`GeneralLinearWeilAdelicTwistStatement` to compare these points with actual
matrix `GL_n(𝔸_E)`. Both fields are in the same field universe for this
geometric construction.

`IsCyclicTraceTest` uses compact support and the existing adelic smoothness
predicate. Left and right translates by the inverse image of the specified
infinite compact span finite-dimensional complex spaces. In the base-change
applications the compact is `adelicInfiniteStandardCompact`, the product of
the standard orthogonal and unitary groups with finite coordinate one, in
the matrix coordinates for the corresponding field.

`IsFactorizableCyclicTraceTest` requires the displayed function to be the
actual product under adelic evaluation. Its finite set contains all the
infinite places. Inside the set the factors are compactly supported and
continuous, and the finite-place factors are locally constant. Outside
it all factors are indicators of the actual integral subgroups. The factor
maps, topological group comparisons and `IsAdelicFactorization` are from
`GeneralLinearBaseChangeLocal`.

`CyclicLocalHaarData` supplies the two local Haar measures in matrix
coordinates with Borel measurable spaces. `Matches` requires
`IsCyclicAlgebra σ (Module.finrank F E)`. Thus `σ` generates the cyclic
action with order the extension degree. The Library's
`isCyclicAlgebra_localGalois` gives the cyclic algebra condition after
completion, with the same degree. `Matches` applies
`BaseChange.AreConcordant` at every place, with the actual local algebra
`F_v ⊗[F] E`, entrywise action of `id ⊗ σ`, and the full extension degree
as the norm length. It transports the local tests
through `localGLEquiv` and `localPointsEquiv`. Thus the comparison is between
ordinary and twisted regular orbital integrals using the same associated
centralizer and compatible quotient measures as the existing local theory.
In particular the lower orbital integrals vanish on regular classes outside
the norm image.

`IsFactorizableCyclicMatch` requires a common exceptional set for both sides,
local concordance everywhere and volume one for both distinguished integral
subgroups at each omitted place. `cyclicMatchedTests` is the complex span of
these pairs. `CyclicLocalHaarData.IsCompatible` requires a finite exceptional
set outside which both families have unit integral-subgroup volume. It
specifies the ambient Haar normalization by the product formula on each side
at every level with these unit tail volumes.

These are internal definitions for Arthur and Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula* (1989), I.3.1,
I.5 and II.1, printed pp. 20, 48–50, 75–80, with III.(4.1)–(4.2), printed
p. 203. Registered source `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
