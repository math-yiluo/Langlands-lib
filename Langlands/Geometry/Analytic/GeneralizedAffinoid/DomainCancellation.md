# Cancellation for full affinoid-domain representations

`Langlands.Analytic.PresentedAffinoidAlgebra.Represents.hom_ext` is the
shared cancellation lemma moved unchanged from
`Langlands.Geometry.Analytic.StrongQuasiIsoCancellation`. Its name, type,
universe and proof are preserved.

For a complete ultrametric normed field, a full representing structural map
`i : A → B` cancels among bounded maps `ψ χ : B → R` to every actual
positive-polyradius presented-affinoid test algebra. The common composite
has spectral image in the represented locus because it factors through
`M(B)`. The full representation property then identifies its two lifts.
No injectivity of a spectrum map is assumed.

Both the relative-domain construction and strong-quasi-isomorphism
cancellation import this shared declaration. Its source rationale remains
the full bounded factorization property described in the original
[strong cancellation companion](../StrongQuasiIsoCancellation.md) and the
[relative representation companion](DomainRelativeRepresentation.md).
