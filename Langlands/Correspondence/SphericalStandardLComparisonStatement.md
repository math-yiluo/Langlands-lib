# The standard L-polynomial on spherical classes

Author: Worker 1273.

`Langlands.Correspondence.SphericalStandardLComparisonStatement` is an internal
comparison obligation for the unramified-normalization proof. It is a
proposition definition. This module supplies no proof of the comparison or of
`FullCorrespondenceUnramifiedStatement`.

For a prime `p` and `F : PadicField p`, the statement quantifies over every
continuous nontrivial unitary additive character `ψ`, every additive Haar measure
`ν` self-dual for `ψ`, every positive rank `r + 1`, classes `π` of that rank and
`π0` of rank one, an unordered spectrum `s` of `r + 1` nonzero complex numbers
with multiplicities, and a complex polynomial `P`. Its hypotheses are:

- `π0` is the trivial rank-one representation, expressed by
  `IsRankOneCharacter F 1 π0`;
- `π` has the spherical spectrum `s`, expressed by the existing actual
  normalized-principal-series relation `HasSphericalSpectrumClass`;
- `P` satisfies the existing `IsAutomorphicPairLPolynomial F ψ ν π π0` relation.

The conclusion is `P = Eigenvalues.eulerPolynomial s`. For an enumeration
`z : Fin (r + 1) → ℂˣ` of `s`, this is
`P = ∏ i, (1 - C (z i : ℂ) * X)`. Here the spectral variable is `X = q^(-s)`.
The values `z i` are the inducing quasi-characters evaluated at the canonical
uniformizer, as specified by `HasSphericalSpectrumClass`; they are neither
inverted nor multiplied by an additional normalization factor.

The polynomial relation uses the Langlands definition on irreducible admissible
classes through tempered standard modules. The spectrum relation supplies a
nonzero `GL_(r+1)(O_F)`-fixed vector and a subquotient of the actual normalized
unramified principal series. There is no genericity or unitarity hypothesis.
The statement assumes the polynomial certificate and proves neither its
existence nor a comparison for nonspherical representations.

The field universe `uF` and representation-carrier universe `uA` are independent.
No parameter-carrier universe or correspondence map occurs in this statement.

This statement has internal provenance: it isolates the representation-side
comparison needed to combine the Library's parameter Euler polynomial with its
spherical classification. It does not purport to be a transcription of a
particular literature result. The formula remains a proof obligation; naming it
introduces no axiom and does not strengthen the hypotheses of the existing full
correspondence target.
