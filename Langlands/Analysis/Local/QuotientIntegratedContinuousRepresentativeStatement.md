# Continuous representatives of compactly supported convolutions on a coset space

`Langlands.QuotientIntegration.QuotientIntegratedContinuousRepresentativeStatement`
is a proposition definition. It supplies no proof.

## Setting

The setting is that of
`Langlands.QuotientIntegration.CompactQuotientIntegratedHilbertSchmidtStatement`
**without** the compactness of the coset space:

- `G` is a Hausdorff, locally compact, second countable topological group
  with its Borel σ-algebra; `H` is a closed subgroup with an s-finite, right
  invariant measure `μH` finite on compact sets.
- `μG` is a left invariant measure on `G`, finite on compact sets, and `ν`
  is a measure on `LeftQuotient H`, finite on compact sets, with
  `IsCompatible H μG μH ν`.
- `π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)` preserves norms, has almost
  everywhere strongly measurable orbits, and for every `g` and `φ` the class
  `π g φ` is represented `ν`-almost everywhere by
  `q ↦ φ (rightTranslate H g q)`. So `π` is the original right regular
  action, supplied with its defining property.

## Conclusion

For every compactly supported continuous `f : C_c(G, ℂ)` (with its
integrability proof `hf`) and every class `φ : L²(ν)` there is a function
`ψ : LeftQuotient H → ℂ` with three properties.

1. `ψ` is continuous.
2. The class `R(f)φ = integratedIsometricAction μG π _ _ f hf φ` is
   `ν`-almost everywhere equal to `ψ`.
3. Write `S = supp f · (supp f)⁻¹`. For every `x : G` and every uniform
   bound `M` of `‖f‖`,
   `‖ψ (H x)‖² ≤ M · (∫ ‖f‖ dμG) · μH(H ∩ x S x⁻¹) · ‖φ‖²`.

The bound is the pointwise form of the `L²`-to-sup estimate (9.13). Its
factor `μH(H ∩ x S x⁻¹)` may be unbounded in `x` when the coset space is not
compact. No Hilbert–Schmidt, smoothness, growth or cuspidal conclusion is
asserted.

## Sources and provenance

This is a derived statement. The source is Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

- Lemma 9.3.3, printed pp.247–248 (one-based PDF pp.259–260), states the
  estimate `‖R(f)φ‖_∞ ≪_f ‖φ‖₂` (9.13) on a closed invariant subspace and
  uses it through the point evaluations `φ ↦ R(f)φ(x)`, which presuppose a
  pointwise defined function.
- The first line of (9.14), printed p.250 (PDF p.262), gives
  `R(f)φ(x) = ∫ f(x⁻¹ y) φ(y) dy`.

The statement supplies the continuous function behind these point
evaluations for an arbitrary closed subgroup with a compatible quotient
measure, and the pointwise bound with explicit dependence on the coset. The
explicit bound is internal. For a compact coset space the bound is
uniform, which recovers the compact-quotient estimate.

## Intended proof

A private proof compiles. The separately staged kernel statement
`QuotientConvolutionKernelStatement` supplies a continuous `v : G → L²(ν)`
with `⟪v x, φ⟫ = ∫ f(a) φ(H (x a)) da` and the norm bound. The function
`x ↦ ⟪v x, φ⟫` is left `H`-invariant, because `H (h x a) = H (x a)`, so it
descends to a continuous `ψ` on the coset space (`descend`,
`Continuous.quotient_lift`). The published pointwise statement
`IntegratedTranslationPointwiseStatement`, applied to the right translation
action (jointly continuous through the open quotient map, measure
preserving by `IsCompatible`; the coset space is locally compact and second
countable, so `ν` is σ-finite), identifies `R(f)φ` almost everywhere with
`q ↦ ∫ f(a) φ(q a) da`, which is `ψ`. Cauchy–Schwarz and the kernel bound
give (3).
