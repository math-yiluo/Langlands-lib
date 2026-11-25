# The topology of a quadratic extension of a nonarchimedean local field

The module `Langlands.HarmonicAnalysis.QuadraticExtensionTopology` proves the topological
properties of a quadratic extension `E = F(δ)` of a nonarchimedean local field `F`, given by a
quadratic involution `c` (`hE : IsQuadraticInvolution c δ`, `Langlands/Group/Unitary/Basic.lean`),
with the module topology over `F`.

## Content

- `IsQuadraticInvolution.isTopologicalRing`: `E` is a topological ring (finite over `F`).
- `IsQuadraticInvolution.continuous_conj`, `continuous_trace`: the conjugation and the trace are
  continuous (linear maps of finite-dimensional spaces).
- `IsQuadraticInvolution.t2Space`: `E` is Hausdorff.
- `IsQuadraticInvolution.continuous_norm`: the norm is continuous, since `N z = ½ tr(z c(z))`
  (for `2 ≠ 0`).
- `IsQuadraticInvolution.continuousInv₀`: the inverse is continuous away from `0`, since
  `z⁻¹ = N(z)⁻¹ c(z)`.

Together with `IsQuadraticInvolution.finite` and the results of
`Langlands.HarmonicAnalysis.Bicharacter.SelfDual` (compact open exhaustion, Hausdorff, locally
compact, second countable for finite-dimensional spaces) and `isModuleTopology_matrix`
(`Langlands.HarmonicAnalysis.LinearHaarScaling`), this is what the Fourier analysis on `E` and on
`M_{α×ν}(E)` of the unitary dual pairs needs.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`:
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuadExtTopology.lean` (whole). The
repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- The source's single statement (a conjunction of eight properties, the last one the source's
  `Good` for the matrix spaces) is split into the six theorems above; `Good` is replaced by the
  Library's `CompactOpenExhaustion` and Mathlib's classes, which the callers obtain from
  finite-dimensionality.
- `[CharZero F]` is weakened to `[NeZero (2 : F)]` where `2` is used (the norm and the inverse) and
  dropped elsewhere; the universes of `F` and `E` are arbitrary.

## Declarations

- `Langlands.IsQuadraticInvolution.isTopologicalRing`, `continuous_conj`, `continuous_trace`,
  `t2Space`, `continuous_norm`, `continuousInv₀`.

## Dependencies

`Langlands.Group.Unitary.Basic`, `Langlands.HarmonicAnalysis.Bicharacter.SelfDual`; Mathlib:
`RingTheory.Norm.Basic`, `RingTheory.Trace.Basic`, `Topology.Algebra.Module.ModuleTopology`.
