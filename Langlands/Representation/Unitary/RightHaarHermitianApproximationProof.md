# Proof of actual right Haar Hermitian approximation

Worker 116 authored
`Langlands.Analysis.rightHaarHermitianApproximation`, whose type is exactly
`Langlands.Analysis.RightHaarHermitianApproximationStatement`, with
independent group and Hilbert-space universes. Worker 1679 adopts the
complete proof unchanged for this focused submission. It imports the
unchanged published target and the independently accepted and published
generic assembly and Haar inversion-density proofs by their public
Lean module names.
The proof constructs the monoid homomorphism
d(g) = modularCharacter(g⁻¹). The reversal of products under inversion
is harmless because the target nonnegative reals are commutative.
Continuity follows by composing intrinsic modular continuity with
continuous inversion.

The second equality in `Langlands.Haar.haarInversionDensity`, together
with `Measure.inv_inv`, gives
(μ.inv).inv = μ.inv.withDensity d. The existing inverse-measure instances
supply finiteness on compact sets and positivity on nonempty open sets.
The second countable group has a countably generated identity filter.
Each continuous orbit is strongly measurable by
`Continuous.stronglyMeasurable`, using the second countable source,
and is therefore AE strongly measurable for μ.inv. This requires no
separability of the Hilbert space.

The proof then applies
`Langlands.Analysis.integratedHermitianApproximation` to μ.inv and d.
Its explicit weights, actual Bochner operators, symmetry, contraction,
strong convergence, preservation and intertwiner conclusions are the
desired ones by definitional equality and proof irrelevance.

This is an internal specialization of the general assembly, using the
Getz–Hahn convention and source locators in the unchanged statement
Markdown. The submitted contribution contains only this proof's
Lean/Markdown pair. It imports
`Langlands.Representation.Unitary.IntegratedHermitianApproximationProof`
and `Langlands.Analysis.Local.HaarInversionDensityProof`, including the
published Haar proof's reuse of the public density-transport helper.
Smooth adelic weights, the split-centre quotient, original automorphic
L² specializations, compactness, density and spectral decomposition
remain separate obligations.
