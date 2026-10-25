# Exhaustion of spherical representations by normalized principal series

`Langlands.Unramified.sphericalSpectrumExistence` proves exactly
`Langlands.Unramified.SphericalSpectrumExistenceStatement.{uF, uV}` from
[SphericalClassificationStatement](SphericalClassificationStatement.md).
For every prime `p`, finite extension `F : PadicField.{uF} p`, positive rank
`n = r + 1`, and actual irreducible admissible smooth complex representation
`A` with nonzero `GL_n(O_F)`-fixed subspace, it constructs a multiset
`s : Eigenvalues n` satisfying `HasSphericalSpectrum F A s`.

The conclusion supplies a tuple `z : Fin n → ℂˣ` enumerating `s` and an actual
subquotient realization of the original representation `A` in
`principalSeriesOfTuple F z`. This is the existing induction from the upper
Borel with its positive half-modulus normalization. The field and group
topologies and spherical subgroup are the canonical published constructions.
The input carrier universe `uV` remains independent of `uF`; no finiteness,
unitarity, genericity, or temperedness hypothesis is imposed on `A`.

## Implemented proof

The proof composes four published theorems and the published invariance of the
constituent relation under representation equivalence.

1. `sphericalHeckeSpectrumExistence` constructs a multiset `s` for the actual
   standard Hecke operators on the original fixed subspace of `A`. Its proof
   uses the fixed-line theorem, invertibility of the last standard Hecke
   element, and complex polynomial factorization with multiplicities; see
   [SphericalHeckeSpectrumExistenceProof](SphericalHeckeSpectrumExistenceProof.md).
2. `Eigenvalues.ofTuple_surjective` supplies `z` with
   `Eigenvalues.ofTuple z = s`. Then
   `SphericalExistence.sphericalConstituentExistence` constructs an actual
   irreducible admissible spherical constituent `B` of this normalized
   principal series; see
   [SphericalConstituentExistenceProof](SphericalConstituentExistenceProof.md).
   This auxiliary object's carrier is in universe `uF`.
3. `sphericalConstituentHeckeScalar`, after rewriting by the enumeration
   equality, proves `HasSphericalHeckeSpectrum F B s`. This uses the
   principal-series scalar formula transferred through actual subquotients;
   see [ConstituentHeckeScalarProof](ConstituentHeckeScalarProof.md).
4. `sphericalHeckeSpectrumDetermination` applied to `A`, `B`, and their common
   spectrum supplies an intertwining linear equivalence `e` from `A` to `B`.
   Its independent carrier universes allow the instantiation
   `{uF, uV, uF}`. The theorem uses spherical Hecke generation and the corner
   annihilator argument; see
   [SphericalHeckeSpectrumDeterminationProof](SphericalHeckeSpectrumDeterminationProof.md).
5. `isSphericalConstituent_iff_of_equiv F z e` transports the constituent
   property of `B` back to `A`. In particular, the surjective intertwiner
   witnessing the subquotient is transported to the original carrier.
   The witnesses `s`, `z`, the enumeration equality, and this transported
   constituent property give exactly the required existential conclusion.

## Provenance

This is an internal composition of the cited Library results, with no additional
representation-theoretic premise. It implements the exhaustion claim recorded
in the unchanged target's source correspondence: Borel,
*Automorphic L-functions* (1979), section 10.4, printed pages 44–45
(PDF pages 53–54; registered source `borel-1979-automorphic-l-functions`).
The normalization and Hecke interpretation are those already specified in the
target and imported results, with Gross, *On the Satake isomorphism* (1998),
section 6 (registered source `gross-1998-satake-isomorphism`) as their source.
The Lean proof follows the composition above rather than assuming either
literature assertion as an axiom.

The two Hecke-spectrum theorems are used as proved results, with no explicit
unproved inputs. The argument does not use a converse principal-series/Hecke
comparison or assume a principal-series realization of `A`. The original target
and its imports are unchanged. This file proves exhaustion alone, without
asserting the other conjuncts of the spherical classification statement.
