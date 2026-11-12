# Renard II.3.7–II.3.8: proof of the modular distribution formulas

Worker 1466, Task 5393. The theorem
`Langlands.HarmonicAnalysis.Distribution.RenardModular.statements` proves the
published proposition `Langlands.HarmonicAnalysis.Distribution.RenardModular.Statements`
at its full universe parameter `uG`. It supplies all seven conjuncts with the
original hypotheses, densities, characters, and actual distribution actions.
The target pair and its imports are unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are II.3.7, printed pp.47–48 / PDF pp.53–54, and
II.3.8 including (II.3.8.1), printed p.48 / PDF p.54. The proof route below
is an internal deduction using the published Library and pinned Mathlib,
rather than a transcription of the source's proof.

## Integral comparison and character conventions

Van Dantzig's theorem, imported from `LocallyProfiniteProof`, supplies a local
`NonarchimedeanGroup` instance from the target's locally compact, Hausdorff,
totally disconnected hypotheses. The imported modular-character regularity
proof then gives local constancy and compact-subgroup triviality for Mathlib's
character. Renard's character is its composition with group inversion, as
specified by the published `renardModular` adapter.

The private helper `integral_unique_complex` extends Mathlib's real compact-support
Haar integral uniqueness theorem to complex functions by comparing real and
imaginary parts. It needs only a left-invariant comparison measure finite on
compact sets. In particular, no regularity or countability is imposed on the
Haar measure supplied by the target.

`translation` applies this uniqueness to right translation of the supplied
measure. Mathlib's modular character is exactly the resulting Haar scalar
factor. Translating on the left preserves the Haar integral, which gives the
displayed two-sided test-integral formula. `regularity` obtains positivity,
local constancy, continuity and compact-subgroup triviality by composition with
inversion in Renard's reciprocal convention.

## Inversion with unrestricted totally disconnected groups

`modularDensity` is the actual locally constant function
`x ↦ ((Measure.modularCharacter x : ℝ) : ℂ)`. The reciprocal adapter identifies
it pointwise with the required function `x ↦ ((renardModular x : ℝ)⁻¹ : ℂ)`.

For a regular reference Haar measure `η = Measure.haar`, let `ν` be `η`
weighted by the nonnegative Mathlib modular character `w`. The private
`map_density_equiv` proves transport of a density through a measurable
equivalence by the map and restricted Lebesgue-integral identities. Right
translation scales `η` by `w(g)` while transporting the density to
`w(x g⁻¹)`. The character identity cancels these factors. Thus `ν` is right
invariant, and `ν.inv` is left invariant. Continuity of `w` gives local
finiteness of `ν`, hence finiteness on compact sets for `ν.inv`.

Choose a compact open subgroup `K`. The character is one on `K`, and `K` is
closed under inversion, so `ν.inv(K) = η(K)`. Compact-set Haar uniqueness and
cancellation of this finite positive mass show
`haarScalarFactor ν.inv η = 1`. Applying complex compact-support uniqueness to
the inverted test function therefore gives
`∫ f(x⁻¹) dη = ∫ w(x) f(x) dη`.

The helper `inversion_eq_density` transfers this identity to every Haar measure
`μ` by applying the same compact-support uniqueness twice: to the inverted
test and to the published `multiplyTest modularDensity f`. Both comparisons
have the same scalar factor. Finally, inversion exchanges the published left
and right distribution actions, so left invariance of `ofMeasure μ` implies
right invariance of its inverted distribution. This proves
`inversionDensity` without second countability, sigma finiteness, or regularity
of `μ`; it does not assert equality of the corresponding unrestricted measures.

## Unimodularity, automorphisms and indices

The Haar distribution is nonzero because it has positive value on the
characteristic function of a compact open subgroup. The translation identity
and cancellation against this nonzero distribution give the equivalence
between the trivial modular character and right invariance. `unimodularity`
then proves the abelian example by commuting the translation factors, and the
compact and elementwise compact-subgroup examples by character triviality on
compact subgroups.

The private `automorphism_factor` proves that the Haar scalar factor of the
pushforward under the actual continuous automorphism is the reciprocal of
Mathlib's `mulEquivHaarChar`. It uses composition of Haar scalar factors and
invariance of those factors under pushforward, so the result holds for the
arbitrary supplied Haar measure. `automorphism` applies integral uniqueness
with this factor. For actual inner conjugation, the two-sided translation
formula computes the same scalar; `innerAutomorphism` cancels the nonzero
Haar distribution to identify it with `renardModular h`.

For `indexFormula`, set `P = σ⁻¹(K)` and `L = K ∩ P`, exactly as in the target.
Compact-set Haar uniqueness for `μ.map σ` gives the preimage mass scaling.
The published `Langlands.Haar.relIndex_mul_measure` supplies both mass/index
identities for `K` and `P`. The intersection `L` is compact open, with finite
positive Haar mass. Cancelling that mass gives
`renardAutomorphismModule σ * [K:L] = [P:L]`; finite index makes the denominator
nonzero and yields the required quotient `[P:L] / [K:L]` in `ℝ≥0`.

The final theorem assembles `translation`, `regularity`, `inversionDensity`,
`unimodularity`, `automorphism`, `innerAutomorphism` and `indexFormula` in the
published order.
