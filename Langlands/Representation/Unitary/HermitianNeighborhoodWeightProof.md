# Proof of continuous Hermitian neighborhood weights

Worker 116 authored the complete proof adopted here from parent draft 27;
Worker 1679 prepared this focused exact-target submission and its validation.
The theorem `Langlands.Analysis.hermitianNeighborhoodWeight` has exact type
`Langlands.Analysis.HermitianNeighborhoodWeightStatement`, imported from the
published statement module. The adopted Lean proof is unchanged.

The group universe is arbitrary. The group is locally compact and Hausdorff
with its Borel measurable space; the measure is finite on compact sets and
positive on nonempty open sets. The supplied d : G →* ℝ≥0 is continuous.
No measure invariance, inversion-density identity or countable local base
is assumed. The resulting function is real, continuous and nonnegative,
with compact topological support in the given identity neighborhood,
actual integral one and f(g) = d(g)f(g⁻¹) everywhere.

For the given identity neighborhood U the proof takes
V = interior(U) ∩ inversion⁻¹(interior(U)). It is open, contains the identity,
and both V and its inverse are contained in U. The pinned Urysohn theorem
`exists_continuousMap_one_of_isCompact_subset_isOpen`, applied to the
compact singleton {1}, supplies a continuous real bump φ, with compact
topological support inside V, φ(1) = 1 and values between zero and one.

The function ψ(g) = φ(g) + d(g) φ(g⁻¹) is continuous, nonnegative and
compactly supported. Compactness of the inverted bump follows from
inversion being a homeomorphism; multiplication by the continuous d
preserves compact support. The support-of-sum and support-of-product
inclusions put its topological support inside U. The actual homomorphism
law d(g)d(g⁻¹) = 1 gives ψ(g) = d(g)ψ(g⁻¹), and ψ(1) = 2.

Continuity and compact support give integrability against the supplied
measure finite on compact sets. The theorem
`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero` uses the
measure's positivity on nonempty open sets, global nonnegativity and the
nonzero value at the identity to show that c = ∫ ψ is strictly positive.
Dividing ψ by c preserves continuity, compact support, the support
inclusion, nonnegativity, integrability and the Hermitian identity.
`integral_div` and c ≠ 0 give integral one.

This is the internal continuous-weight precursor explained in the target
Markdown, not a construction of the smooth sequence in Getz–Hahn section
9.3. Smoothness, countable shrinking neighborhoods, the actual Haar
modular density, representation realization and compact integrated
operators remain separate obligations.
