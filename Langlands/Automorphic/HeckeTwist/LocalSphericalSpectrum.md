# Spherical spectra under multiplication by any Hecke determinant character

Author: Worker 5136.

Let `S` be a local realization of `GL_{r+1}(F_v)` at a finite place `v` and `χ` an
arbitrary Hecke character with `χ_v ∘ det` trivial on `GL_{r+1}(𝒪_v)` (hypothesis
`hlocal`). This internal module shows that the twist
`S.heckeDeterminantTwist χ` has the spherical Hecke spectrum of `S` with every
Satake parameter multiplied by `χ_v(ϖ_v)`, the Library's
`χ.finiteUniformizerValue v`. The scaling is the Library's `Eigenvalues.scale`.

- Private helpers: a linear equivalence carries a nonzero subspace to a nonzero
  subspace, and a scalar equation on the image of an equivalence holds on the
  whole target.
- `standardHeckeOperator_heckeDeterminantTwist_uniformizer`: the `i`-th
  standard Hecke operator picks up the factor `χ_v(ϖ_v)^i`, by the Library's
  `finiteLocalDeterminant_standardDiagonal` and
  `standardHeckeOperator_heckeDeterminantTwist` (module `LocalSphericalTwist`).
- `standardHeckeOperator_heckeDeterminantTwist_scaled`: an eigen-equation with
  the normalized eigenvalue `standardHeckeScalar … s i` becomes one with the
  scaled parameters `Eigenvalues.scale (χ.finiteUniformizerValue v) s`
  (the Library's `standardHeckeScalar_scale`).
- `isSphericalHeckeEigenvector_heckeDeterminantTwist`: a nonzero simultaneous
  eigenvector with parameters `s` maps to one with the scaled parameters.
- `hasSphericalHeckeSpectrum_heckeDeterminantTwist`: if every standard Hecke
  operator acts on the whole spherical space of `S` by the scalar of `s`, the
  same holds for the twist with the scaled parameters.
- `hasSphericalHeckeSpectrum_heckeDeterminantTwist_outside_tail`: the same
  without `hlocal`, for `v` outside `χ.finiteHeckeDeterminantTail (r + 1)`
  (module `FiniteTail`).
- `heckeDeterminantTwistSphericalSpectrum` and
  `heckeDeterminantTwistSphericalEigenvector`, with `_val` lemmas: the same
  transport as functions on bundled spectra and eigenvectors.

Provenance: internal. This is the Library module
`Langlands.Automorphic.LocalSphericalDeterminantSpectrum` with the finite-order
hypothesis removed. No correspondence with a particular passage of the
literature is claimed.
