# Continuous kernel vectors of compactly supported convolutions on a coset space

`Langlands.QuotientIntegration.QuotientConvolutionKernelStatement` is a
proposition definition. It supplies no proof.

## Setting

The setting is that of the published
`Langlands.QuotientIntegration.QuotientL2UnfoldingStatement`, with the
ambient measure also left invariant:

- `G` is a Hausdorff, locally compact, second countable topological group
  with its Borel σ-algebra, in an arbitrary universe `uG`; `H` is a closed
  subgroup with an s-finite, right invariant measure `μH` finite on compact
  sets.
- `μG` is a left invariant measure on `G`, finite on compact sets, and `ν`
  is a measure on the left coset space `LeftQuotient H` (cosets `H g`),
  finite on compact sets, with `IsCompatible H μG μH ν`. That hypothesis is
  the existing property of actual measures (compact-test Weil integration
  formula, regularity, nonzeroness and right invariance of `ν`); the
  statement does not construct a compatible quotient measure.

No compactness of the coset space, finite total volume, normality of `H`
or unimodularity is assumed.

## Conclusion

For every compactly supported continuous `f : C_c(G, ℂ)` there is a map
`v : G → Lp ℂ 2 ν` with three properties.

1. `v` is continuous into `L²(ν)` with its norm topology.
2. For every `x : G` and every class `φ : L²(ν)`, the function
   `a ↦ f(a) φ(H (x a))` is integrable for `μG` and
   `⟪v x, φ⟫ = ∫ f(a) φ(H (x a)) dμG(a)`.
   Mathlib's inner product is conjugate linear in its first entry, and `φ`
   inside the integral is Mathlib's chosen representative of its class; the
   equality with the inner product shows that the integral depends only on
   the class.
3. Write `S = supp f · (supp f)⁻¹` (topological supports). For every `x`
   and every uniform bound `M` of `‖f‖`,
   `‖v x‖² ≤ M · (∫ ‖f‖ dμG) · μH(H ∩ x S x⁻¹)`,
   where the last factor is `μH.real` of the preimage in `H` of the
   conjugate `x S x⁻¹`.

Property 2 determines each `v x` uniquely. For `x` fixed it is the kernel
vector of the point evaluation `φ ↦ ∫ f(a) φ(H (x a)) da`. No statement is
made about the operator `R(f)` itself. The published
`QuotientIntegratedContinuousRepresentativeStatement` is the operator
version.

## Sources and provenance

This is a derived statement. The source is Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

- The proof of Lemma 9.3.3, printed p.248 (one-based PDF p.260), applies
  the Riesz representation theorem to the continuous form
  `φ ↦ R(f)φ(x)` and obtains a kernel `K_{R(f),x}` with
  `R(f)φ(x) = ∫_{[G]} K_{R(f),x}(y) φ(y) dy` and
  `‖K_{R(f),x}‖₂ ≤ C` independent of `x`. Here the bound is taken from
  hypothesis (9.13) of Lemma 9.3.3, printed p.247 (PDF p.259).
- The first line of (9.14), printed p.250 (PDF p.262), gives
  `R(f)φ(x) = ∫ f(x⁻¹ y) φ(y) dy`. After the substitution `y = x a` this
  is the integral in property 2.

Getz–Hahn work on the quotient by a discrete subgroup and pair `K` with `φ`
bilinearly; here `H` is an arbitrary closed subgroup with a compatible
quotient measure, and `v x` corresponds to the complex conjugate of
`K_{R(f),x}` because the Hilbert pairing is conjugate linear in its first
entry. The vector exists without hypothesis (9.13). The explicit bound in
property 3 and the continuity of `v` are internal. They replace the
constant `C` with an explicit factor that may be unbounded in `x` when the
coset space is not compact. For a compact coset space the factor is
uniform.

## Intended proof

A compiled proof exists in the shared draft of task
`34b81620-20d7-4059-9b08-6bedd1c1c029`. For each `x`, the published
unfolding theorem for the weight `b ↦ conj f(x⁻¹ b)` gives `v x` as the
class of that weight's `H`-average. The bound comes from estimating the
orbital integral of `‖f‖` over `H ∩ x S x⁻¹` and integrating by the
compatibility formula. Continuity uses uniform continuity of `f` and the
same estimate for the difference weights. This route is a proof plan, not
accepted proof evidence.

## Remaining obligations

An independently reviewed exact-target proof remains necessary. This
statement asserts no Hilbert–Schmidt, trace-class, smoothness, growth,
cuspidal or spectral conclusion.
