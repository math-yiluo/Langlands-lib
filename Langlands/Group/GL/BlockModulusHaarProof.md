# The block modulus is the Haar module of Levi conjugation

Author: Worker 117.

The closing theorem `Langlands.glBlockModulusHaar` proves exactly the published
`Langlands.GLBlockModulusHaarStatement.{uF}`. For every prime `p`, field
`F : PadicField.{uF} p`, supplied topological realization `T`, rank `n`, ordered
block shape `B`, Borel measurable structure on the actual block unipotent
radical, Haar measure `μ` on that radical, and Levi element `m`, it proves

`μ.map (B.leviAction F.Carrier m) = ((T.leviModulus B m : ℝ≥0)⁻¹) • μ`.

The topology is exactly `T.topology` and the radical's inherited subgroup
topology. The absolute value in the modulus is the existing residue-normalized
one. The theorem adds no countability, regularity, normalization, chosen
measurable-structure, coordinate-Haar or determinant-scaling premise. It retains
all field universes and block shapes, including rank zero and one block.
The target statement and its imported Lean/Markdown pairs are unchanged.

## Implemented proof

The shared helper `HarmonicAnalysis.pi_nnreal_smul` in
[FiniteProductMeasureScaling](../../HarmonicAnalysis/FiniteProductMeasureScaling.md)
identifies the finite product of rescaled
sigma-finite measures with their product rescaled by the product of the
nonnegative scalars. It checks measurable rectangles using `Measure.pi_eq`,
`Measure.pi_pi`, and `Finset.prod_smul`.

The named theorem `PadicField.TopologicalData.leviModulus_eq_upperPair_prod`
rewrites the existing nested product definition of the explicit modulus into
a single product over strict upper block pairs. It removes the coercion from
nonnegative real units, rewrites a subtype product as a filtered product, and
expands the finite Cartesian product. This step is only a reindexing of the
existing character.

The main assembly is implemented in
`glBlockModulusHaarStatement_of_prerequisites`. This helper exposes the
rectangular-scaling and coordinate-Haar propositions as explicit premises;
the closing theorem discharges both with published proofs. The assembly
installs precisely the supplied field topology and its intrinsic second
countability. The target's arbitrary measurable structure on the radical
equals its Borel structure by the supplied `BorelSpace` certificate, so the
proof rewrites by that equality before choosing a reference measure. This
preserves the quantifier over every Borel measurable structure.

Each strict upper rectangular coordinate receives its canonical additive Haar
measure. Finite-dimensional local compactness and second countability give
sigma-finiteness. Rectangular determinant scaling identifies the image of each
factor under `X_ij ↦ m_i X_ij m_j⁻¹` as that factor multiplied by
`(|det m_i|^(B.size j) / |det m_j|^(B.size i))⁻¹`.
The image measure is also sigma-finite because it equals a finite nonnegative
scalar multiple of the original measure. `Measure.pi_map_pi` and
`HarmonicAnalysis.pi_nnreal_smul` combine these identities. Reindexing the modulus product and
moving inversion outside the finite product give exactly the inverse of
`T.leviModulus B m`.

The proof pushes this product measure to the actual radical through the inverse
of `B.radicalCoordinatesHomeomorph F.Carrier`. The coordinate-Haar theorem
makes the resulting reference measure `ρ` Haar. The published formula
`radicalCoordinates_leviAction_symm` identifies Levi conjugation in these
coordinates with the blockwise map just measured. Continuity supplies
measurability. Composing pushforwards and commuting pushforward with scalar
multiplication transfer the inverse-modulus equality to `ρ`.

The coordinate homeomorphism transfers second countability to the radical.
The existing named results `T.unipotentRadicalTopologicalGroup`,
`T.unipotentRadicalT2Space`, and `T.unipotentRadicalLocallyCompactSpace` supply
its locally compact Hausdorff topological group structure. Mathlib's
`isMulLeftInvariant_eq_smul` expresses the supplied arbitrary Haar measure `μ`
as a nonnegative scalar multiple of `ρ`. Pushforward linearity and commuting
scalar actions yield the required equality for `μ`.

The helper `glBlockModulusHaarStatement_of_rectangular` supplies the published
`glBlockUnipotentCoordinateHaarStatement` to discharge the coordinate premise.
Finally, `glBlockModulusHaar` supplies the published
`HarmonicAnalysis.padicRectangularHaarScalingStatement`. Its complete type is
the original unconditional proposition. Empty products are allowed throughout,
so the proof covers the trivial radical cases without a positive-rank or
nonempty-upper-pair hypothesis.

## Reused results and provenance

This is an internal proof of the already published block-modulus statement,
using the existing coordinate formulas, explicit modulus definition, intrinsic
topology lemmas, and Mathlib's finite-product and Haar-uniqueness results.
The forward-pushforward convention in the unchanged target is preserved:
the scaling factor is the inverse modulus.

The imported `PadicRectangularHaarScalingProof` supplies the named determinant
change-of-variables theorem and `padicRectangularScalarHaarScaling`, the latter
with scalar factor `((T.normalizedAbsUnits a : ℝ≥0)^(r*s))⁻¹` for entrywise
multiplication by a field unit on an `r` by `s` matrix. Its scalar-field input is
the published `padicScalarHaarScaling` from `PadicScalarHaarScalingProof`.
The imported `BlockUnipotentHaarProof` supplies coordinate-Haar transport using
finite triangular translations. These proofs are reused by their Lean names;
none is assumed as a premise of the final theorem. The module introduces no
new Haar normalization or external literature assertion.
