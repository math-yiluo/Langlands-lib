# Spherical constituent uniqueness across unordered principal-series parameters (proof)

`Langlands.Unramified.sphericalConstituentUniqueness` proves
`SphericalConstituentUniquenessStatement.{uF, uV, uW}` (module
`Langlands.Representation.Unramified.SphericalClassificationStatement`). Let
`z, w : Fin (r + 1) → ℂˣ` have the same unordered spectrum,
`Eigenvalues.ofTuple z = Eigenvalues.ofTuple w`. Let `A` (carrier universe `uV`)
be a spherical constituent of the normalized principal series of `z`, and `B`
(carrier universe `uW`) one of the principal series of `w`. Then
`A.obj.representation` and `B.obj.representation` are equivalent.

## Proof

The theorem applies `sphericalConstituentUniqueness_of` (module
`Langlands.Representation.Unramified.SphericalHeckeDetermination`) to two
Library results, the first used twice:

- `hasSphericalHeckeSpectrum_of_isSphericalConstituent` (module
  `Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof`), once at
  carrier universe `uV` for `A` and once at `uW` for `B`. A spherical constituent of the principal series
  of `z` has spherical Hecke spectrum `Eigenvalues.ofTuple z`: the standard operator
  `T_i` acts on its nonzero `GL_{r+1}(O_F)`-fixed space by
  `standardHeckeScalar F (Eigenvalues.ofTuple z) i`.
- `sphericalHeckeSpectrumDetermination` (module
  `Langlands.Representation.Unramified.SphericalHeckeSpectrumDeterminationProof`):
  two actual irreducible admissible spherical objects with one common spectrum are
  equivalent.

So `A` has spectrum `ofTuple z`, `B` has spectrum `ofTuple w = ofTuple z`, and the
determination theorem gives the equivalence.

## Provenance

Borel, *Automorphic L-functions* (1979), 7.1–7.2 and 10.4, printed pages 38–39 and
44–45 (source `borel-1979-automorphic-l-functions`): the constituent of the
unramified principal series with a nonzero hyperspecial fixed vector has the
spherical Hecke character of the Satake class of the parameter, and that character
determines the class-1 representation. Gross, *On the Satake isomorphism* (1998),
(3.14) and section 6 (source `gross-1998-satake-isomorphism`), gives the Hecke
eigenvalues. The formal route avoids intertwining operators and the Satake
transform. It combines the eigenvalue computation on the principal series with
generation of the spherical Hecke algebra by the standard elements up to central
powers, and the annihilator form of Bernstein–Zelevinsky 2.10(b).
