# Canonical unipotent splittings for GL and SL

Let \(q:W\to G\) be surjective with central kernel killed by a natural
number \(e\). For a nilpotent subgroup \(U\le G\) with bijective \(e\)-th
powers, `subgroupPowerSplitting` restricts \(q\) to \(q^{-1}(U)\) and
constructs the unique homomorphic lift of \(U\) by `nilpotentPowerSection`.
The restricted kernel inherits centrality and the exponent condition
from \(W\). Every homomorphic lift factors through this preimage, where
uniqueness of the power section applies.

`glUpperUnipotentSplitting` applies this construction to the upper-unipotent
subgroup of \(\mathrm{GL}_r(F)\) for a field \(F\) in which \(e\) is
nonzero. The upper-superdiagonal series proves nilpotence, and
`upperUnipotentPowerEquiv` supplies the power bijection.
`slUpperUnipotentEquiv` identifies the upper-unipotent subgroup of
\(\mathrm{SL}_r(F)\) with the same matrices in \(\mathrm{GL}_r(F)\), since
the determinant is the product of the diagonal entries.
`slUpperUnipotentSplitting` transports nilpotence and the power bijection
through this equivalence. `BruhatLiftData.ofSurjectiveCentralKernel` uses
the resulting section and supplied normalized monomial lifts to build
the Bruhat lift data.

Banks–Levy–Sepanski use the upper-unipotent splitting in §2, Lemma 1,
p. 140, and Lemma 3, pp. 141–142, of *Block-compatible metaplectic
cocycles*, DOI [10.1515/crll.1999.507.131](https://doi.org/10.1515/crll.1999.507.131).
Their existence proof uses ordered positive-root coordinates in the
Steinberg extension. The construction here uses nilpotence and the
power bijection for the case of a central kernel killed by an exponent
nonzero in the field.
