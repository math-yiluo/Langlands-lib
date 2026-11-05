# Proof of symmetry of the actual integrated unitary action

Worker 116 develops the exact theorem
`Langlands.Analysis.integratedUnitarySymmetry`, of type
`Langlands.Analysis.IntegratedUnitarySymmetryStatement` with independent
group and Hilbert-space universes. This private proof is not a proof
submission under the parent program. Its target and constructor must be
published before an exact proof child can receive it.

The proof derives norm preservation from the given inner product law and
uses the constructor's weighted-orbit integrability theorem on each of
the two test vectors. The group homomorphism law gives
π(g)π(g⁻¹)y = y; applying the assumed inner product preservation gives
⟪π(g)x,y⟫ = ⟪x,π(g⁻¹)y⟫.

Using `integral_inner` in the second inner product slot, complex
conjugation and `integral_conj` moves the first integrated vector through
the inner product. The preceding inverse identity identifies its scalar
integrand as conjugate(f(g)) times ⟪x,π(g⁻¹)y⟫.

`integral_map_equiv` for `MeasurableEquiv.inv G` changes variables to
μ.inv. The actual measure equality in the target replaces this measure
by μ.withDensity d. The NNReal-density integral formula gives the scalar
factor d(g) conjugate(f(g⁻¹)), and the given almost-everywhere Hermitian
weight identity replaces that factor by f(g). Finally `integral_inner`
for the other genuinely integrable weighted orbit yields ⟪x,T y⟫.

This implements the internal Bochner argument described in the target's
English explanation. It retains the actual inversion-density correction;
there is no inversion-invariance premise or implicit assumption that the
group is unimodular. The target's cited Getz–Hahn passages motivate the
weight convention, while the proof uses the actual measure identities
and pinned Mathlib integration theorems. Identifying the density for an
automorphic Haar measure, constructing the weights, proving compactness
and realizing the automorphic representation remain separate obligations.
