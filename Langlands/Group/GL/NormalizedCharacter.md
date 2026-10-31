# Residue-normalized determinant characters

Author: Worker 23. This construction belongs to task
`d3d94910-f173-4702-9fc9-b48753f5bbcc`, revision 1.

For every prime `p`, finite extension `F : PadicField p`, supplied compatible
`T : F.TopologicalData`, and natural rank `n`, this file constructs
`T.determinantNorm n : GeneralLinear n F.Carrier →* NNRealˣ`.
Its underlying positive real value is exactly `T.normalizedAbs (det g)`,
or `q ^ (-ord (det g))`. The determinant is the usual determinant of the actual
invertible matrix. The coefficients of the representation space play no role
in constructing this character. All field universes and ranks are permitted.

The field map `normalizedAbsHom` packages the accepted normalized absolute value
as a nonnegative monoid-with-zero homomorphism. Its zero, one and multiplication
fields reuse the accepted arithmetic normalization proof.
`normalizedAbsUnits` restricts it to actual units through `Units.map`.
Composition with the accepted determinant gives the requested character.
The scalar-matrix formula is `determinantNorm (a I_n) = normalizedAbsUnits(a)^n`,
proved using Mathlib's determinant formula and the homomorphism power law.

Continuity follows from the proved identity
`normalizedAbs(x) = canonicalNorm(x)^[F:Q_p]` and the proved equality of the
supplied and spectral-norm topologies. The degree exponent is essential.
This construction does not identify the unadjusted spectral norm with the
residue-cardinality normalization.

The theorem `determinantNorm_eq_one_of_mem_compact` says the determinant norm
is one on every compact matrix subgroup. It applies the continuous positive
character theorem from `Topology.CompactNormCharacter` to
`determinantNormContinuous`. The unchanged theorem was moved here from
`RankOneMatrixFunctionalEquationComparisonFourierInvariance` for shared use.

The kernel is open because its field-unit preimage is exactly the
valuation-one sphere. The file proves the norm-one/discrete-valuation-one
equivalence, transports through the actual value-group isomorphism, and uses
Mathlib's open-sphere theorem for a compatible valuation. The continuous unit
projection and continuous determinant give the two preimages. No unproved
nonarchimedean-group certificate for GL is used.

The equality with the fixed spectral norm raised to the extension degree also
proves that two compatible `TopologicalData` realizations give the same
homomorphism. The canonical constructor specializes to the accepted
`F.canonicalTopologicalData`, so it covers every algebraic p-adic field without
an additional realization hypothesis.

This is the actual norm character needed by the separate real-power twist
construction. Parabolic block-modulus characters, their Haar-modulus
identification, and normalized induction assembly remain further work.

Source convention: Henniart (2002), section 2.5, printed page 595 (PDF page 9),
defines the determinant quasicharacter twist and denotes the normalized
absolute value by `nu`; section 2.8, printed page 596, uses its real powers.
The original pages were read.
Source ID `henniart-2002-characterization`, SHA256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
The packaging and proofs are internal derivations from the exact accepted
arithmetic normalization and GL constructions.

Project dependencies are imported from the current Library by Lean name:

- `Langlands.Group.GL.Padic` and its `Basic` import provide the actual matrix
  group, determinant, scalar embedding and compatible topology. In particular,
  `T.generalLinearDeterminant` is the continuous determinant map.
- `Langlands.LocalField.Normalization.Proof` provides
  `T.normalizedAbs_mul`, `T.normalizedAbs_eq_canonicalNorm_pow_degree`,
  `T.normalizedAbs_le_iff_of_ne_zero` and
  `T.topology_eq_canonicalNormTopology`. These prove the normalization,
  valuation and topology facts used here.

The imported pairs were checked against published Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`.
Their original authors retain authorship of the imported modules; this file
does not copy their implementations.
The pinned environment is Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
The relevant Mathlib audit covers `Units.map`, `det_scalar`,
`Valuation.restrict_eq_one_iff`, `Valuation.isOpen_sphere`,
the topology on units, and continuity of natural powers of the norm.
