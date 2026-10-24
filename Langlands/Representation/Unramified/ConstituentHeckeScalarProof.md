# Standard Hecke scalars of spherical principal-series constituents

`Langlands.Unramified.sphericalConstituentHeckeScalar` proves exactly
`Langlands.Unramified.SphericalConstituentHeckeScalarStatement.{uF, uV}`.
The field universe `uF` and representation carrier universe `uV` remain independent.

For every prime `p`, every `F : PadicField p`, every positive rank `r + 1`,
every tuple `z : Fin (r + 1) → ℂˣ`, and every
`A : AutomorphicObject.{uF, uV} F r.succPNat`, the theorem takes
`IsSphericalConstituent F z A` to
`HasSphericalHeckeSpectrum F A (Eigenvalues.ofTuple z)`. Thus the actual standard
Hecke operators have the prescribed scalars on the nonzero spherical fixed
space. No regularity assumption on the tuple or additional hypothesis is used.

The implemented proof introduces the statement's variables and constituent
hypothesis, then applies
`Langlands.Unramified.hasSphericalHeckeSpectrum_of_isSphericalConstituent F h`
from the published module
`Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof`.
This is a direct packaging of an existing Library theorem as the separately
named proposition; it introduces no new scalar calculation.

The imported theorem proves the scalar identity on smooth subquotients by
lifting fixed vectors through compact-open averaging, applying the
principal-series scalar calculation, and transferring the identity through
intertwiners. Its implemented proof is described in
[SphericalSpectrumUniquenessProof.md](SphericalSpectrumUniquenessProof.md).
The mathematical scope, normalization, and original Borel and Gross references
are recorded in the unchanged
[target statement](ConstituentHeckeScalarStatement.md).

Worker 219 supplied the published helper and the wrapper proof pattern.
Worker 1 assembled this exact statement theorem and its documentation.
