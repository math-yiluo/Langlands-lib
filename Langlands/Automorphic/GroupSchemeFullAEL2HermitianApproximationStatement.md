# One Hermitian approximation on the original quotient and full cusp L2 spaces

`GroupSchemeFullAEL2HermitianApproximationStatement` asks for one sequence
of real weights that approximates the identity on both the original
canonical positive-central quotient L2 space and its original full
all-parabolic almost-everywhere cuspidal submodule. It uses the same
weights, group measure and index on both spaces.

Write `μG` for canonical left Haar on the full actual adelic group and
`μQ` for the unchanged `positiveRationalQuotientHaarMeasure`. Each weight
is continuous, compactly supported, nonnegative and integrable against
`μG.inv`, with integral one and reciprocal modular symmetry
`f n a = (Measure.modularCharacter a⁻¹ : ℝ) * f n a⁻¹`. Its topological
supports eventually lie in every neighborhood of the identity. The group
measure is right Haar; no equality with left Haar is asserted.

`A n` is exactly `haarQuotientL2IntegratedAction` and `B n` exactly
`fullAEL2CuspidalIntegratedAction`, with the same complex weight
`a ↦ (f n a : ℂ)` against `μG.inv`. Both are symmetric contractions, and
each converges strongly to the identity on every vector in its own
original Hilbert space. The target also specifies the exact inclusion
identity `(B n ψ).val = A n ψ.val`, commutation of the subtype-valued
orthogonal projection with `A n` and `B n`, and commutation of the
ambient orthogonal projection with `A n`.

The full cusp carrier still imposes separate almost-everywhere absolute
convergence and vanishing of periods for every actual proper rational
parabolic. All its number-field, affine locally finite-type group,
connected reductivity, structural `ParabolicDynamicStatement`, central
split torus, finite splitting, injective finite-index character
restriction and norm-one right-Haar hypotheses remain explicit. There
is no replacement carrier or measure and no new continuity, closedness
or completeness premise.

Provenance is internal. This target combines the original quotient
approximation proposition with the existing inclusion and projection
laws for the full cusp integrated action. The intended derivation takes
the ambient weights once and transfers the conclusions through that
inclusion; it does not select a separate sequence for the cusp space.
The pair states a proposition and supplies no proof. Independent public
proofs of the ambient and full cusp targets remain separate obligations.

The qualified source scope of the ambient target is retained: continuous
compact weights on the full adelic group are a precursor to the smooth
weights on the split-centre quotient used by Getz–Hahn. This target
establishes no smoothness, smooth-vector density, quotient-group descent,
compactness, trace formula or spectral decomposition.
