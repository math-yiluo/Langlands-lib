# Supplied spherical spectra under actual determinant multiplication

For an actual local automorphic realization in positive rank `r + 1`,
a finite-order Hecke character and triviality of its actual local determinant
character on the actual integral subgroup, the existing spherical multiplier
equivalence transports supplied simultaneous Hecke eigenvectors and supplied
whole-space spherical spectra. Each entry of the existing unordered nonzero
complex spectrum is multiplied by `finiteUniformizerValue` of the character at
the selected finite place. Multiplicities are retained. The number field has
arbitrary universe, and the actual form-space carrier is unchanged.

`standardHeckeOperator_determinantTwist_uniformizer` identifies the multiplier
for standard index `i : Fin (r + 2)` with the `i.val` power of that local
uniformizer value. It combines the proved actual Hecke covariance with the
actual determinant calculation on the existing standard diagonal.
`standardHeckeOperator_determinantTwist_scaled` then applies the published
power law for normalized standard Hecke scalars. The normalization remains the
existing mass-one double-coset measure and positive square-root residue
normalization, including both endpoint indices.

`isSphericalHeckeEigenvector_determinantTwist` transports the existing
nonzero simultaneous eigenvector relation. Nonzeroness follows from
injectivity of the actual spherical multiplier equivalence.
`hasSphericalHeckeSpectrum_determinantTwist` transports the existing
whole-space scalar relation. A nonzero fixed vector transports through that
equivalence, and its surjectivity supplies the scalar equation for every
target fixed vector.
`hasSphericalHeckeSpectrum_determinantTwist_outside_tail` removes the separate
local-triviality premise outside the already proved finite character-tail
bound.

`determinantTwistSphericalSpectrum` constructs the bundled target spectrum:
its numerical value is the scaled supplied spectrum, and its proof field is
the transported actual whole-space scalar action.
`determinantTwistSphericalEigenvector` constructs a bundled target nonzero
eigenvector with the scaled eigen-equations. Its vector is the actual
spherical multiplier applied to the supplied vector. The two `_val` lemmas
record these formulas by definitional equality. Both constructors require
supplied source data; neither chooses spectra or eigenvectors from existence.

Provenance is internal composition of the published actual multiplier,
local-character determinant identity and numerical spectrum-scaling formulas.
The construction assumes a supplied old spectrum or eigenvector; it proves
their transport and does not assert spectral existence, Satake classification,
independence from changing the chosen uniformizer, or global association.
