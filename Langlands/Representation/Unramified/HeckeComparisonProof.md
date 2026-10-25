# Normalized principal-series and spherical Hecke spectra agree

`Langlands.Unramified.sphericalHeckeComparison` proves the published proposition
`SphericalHeckeComparisonStatement.{uF,uV} F` from
`Langlands.Representation.Unramified.HeckeComparisonStatement`. Its full type is

```lean
{p : ℕ} → [Fact p.Prime] → (F : PadicField.{uF} p) →
  SphericalHeckeComparisonStatement.{uF,uV} F
```

For every positive rank `n = r + 1`, actual smooth irreducible admissible complex
representation `A : AutomorphicObject.{uF,uV} F r.succPNat`, and multiset
`s : Eigenvalues (r + 1)`, the theorem asserts
`HasSphericalSpectrum F A s ↔ HasSphericalHeckeSpectrum F A s`.
The representation carrier universe `uV` remains independent of `uF`.

The relations retain the normalized upper-Borel principal series, the canonical
uniformizer, and the actual spherical subgroup `K = GL_n(O_F)`. The Hecke relation
requires a nonzero fixed submodule and, on every fixed vector, the standard
operator for each `0 ≤ i ≤ n` to act by
`(sqrt(q) : ℂ)^(i*(n-i)) * ((-1)^i * s.eulerPolynomial.coeff i)`.
Here Haar measure gives `K` mass one, the square root is the canonical positive
real square root embedded in `ℂ`, and the Euler polynomial is the product
`∏_j (1 - z_j X)` with multiplicities. The theorem introduces no additional
hypotheses such as unitarity, genericity, temperedness or a finite-dimensional
ambient carrier.

## Implemented proof

For the forward implication, unfold `HasSphericalSpectrum` to obtain a tuple
`z` enumerating `s` and a proof that `A` is its spherical constituent. Apply
`hasSphericalHeckeSpectrum_of_isSphericalConstituent` from
`Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof`.
This published theorem supplies the actual normalized operator calculation on
spherical subquotients.

For the converse, `Eigenvalues.ofTuple_surjective` gives a tuple `z` with
`Eigenvalues.ofTuple z = s`. The published
`SphericalExistence.sphericalConstituentExistence` from
`Langlands.Representation.Unramified.SphericalConstituentExistenceProof` gives
an actual spherical constituent `B` of the principal series for `z`, with
carrier universe `uF`. Applying the same scalar theorem to `B` gives its
Hecke spectrum `s`. The published `sphericalHeckeSpectrumDetermination` from
`Langlands.Representation.Unramified.SphericalHeckeSpectrumDeterminationProof`,
specialized at universes `{uF,uV,uF}`, gives an actual representation equivalence
from `A` to `B`. Finally `isSphericalConstituent_iff_of_equiv` transports the
spherical subquotient realization back to `A`. Together with the same tuple
`z`, this proves `HasSphericalSpectrum F A s` on the original carrier.

All three mathematical inputs are proved Library theorems. The determination
proof uses generation of the actual spherical Hecke corner and an annihilator
comparison of cyclic representations. This composition requires no independent
spherical exhaustion or coefficient-separation theorem: it starts with the
specified multiset and constructs a constituent for that multiset.

## Provenance and contributions

This is a derived composition of the published constituent existence, scalar
calculation and Hecke determination results. It proves the comparison supported
by Borel, *Automorphic L-functions* (1979), sections 7.1–7.2 and 10.4 (printed
pages 38–39 and 44–45; source `borel-1979-automorphic-l-functions`, retained
`Part II.pdf`, SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`), and Gross,
*On the Satake isomorphism* (1998), sections 2, 3 and 6, in particular (2.5),
(3.14) and (6.2)–(6.7) (PDF pages 3, 6–8 and 11–12; source
`gross-1998-satake-isomorphism`, SHA-256
`9bd0077b2057edd32885e46fd38872f423a4d45fef6bec0aa181af32dee062b3`). The
implemented converse uses determination directly, whereas the statement's
source discussion describes a route through exhaustion and separation.

Worker 86 assembled the proof. Its converse was adapted from Worker 342's
shared `SphericalSpectrumExistenceAssembly` draft, using the spectrum already
supplied by this comparison. Worker 257 contributed the independent-universe
determination interface used in the assembly. The final implementation imports
the published results by Lean name; the draft provenance is attribution, not
proof evidence.
