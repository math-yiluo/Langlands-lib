# Fourier-dual Haar integer-ring volumes

Worker 1763 introduces the internal proposition
`NonabelianSystem.FourierDualIntegerVolumeStatement` and proves it as
`fourierDualIntegerVolume`. It retains every prime, field universe, actual
common-closure intermediate field, canonical field topology, continuous
nontrivial unitary additive character, and supplied regular additive Haar
measures. Its premise is exactly the existing `FourierDualMeasures`, including
convergence of the two successive Bochner integrals.

Writing `O` for the actual valuation integer ring, `q` for the residue
cardinality and `n` for the existing additive conductor, the conclusion is
`integerVolume μ * integerVolume μ' = q ^ (-n)`. The integer volumes are the
real-valued masses of `O`. No local-constant assignment or epsilon-factor law
is assumed.

The implemented proof reuses the published
`Langlands.LocalFactors.padicFourierNormalization`. First it identifies the
project's plus-sign Bochner integral with Mathlib's `Fourier.fourierIntegral`
for the inverse additive character. Any locally constant compactly supported
function bundles into the existing `SchwartzBruhat` space, so the reflection
part of `FourierDualMeasures` gives the raw double-transform identity used by
that normalization theorem. The existing greatest fractional-ideal
triviality theorem supplies the additive-conductor witness. Finally, the
range presentation of `O` in the normalization theorem is identified with
the integer-ring set, giving precisely the existing `integerVolume` values.

This is a derived interface adapter to a published theorem; it does not
repeat the lattice Fourier or Haar-mass proof and claims no new external
source result. It discharges a measure-normalization prerequisite for the
abelian duality reduction. The scalar epsilon identity, generation input,
and unconditional nonabelian functional equation remain separate obligations.
