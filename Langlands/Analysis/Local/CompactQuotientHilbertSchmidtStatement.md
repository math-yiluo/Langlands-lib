# Hilbert–Schmidt convolution on a compact left coset space

`Langlands.QuotientIntegration.CompactQuotientIntegratedHilbertSchmidtStatement`
is a proposition definition. It supplies no proof.

## Setting

- `G` is a Hausdorff, locally compact, second countable topological group
  with its Borel σ-algebra.
- `H` is a closed subgroup of `G`, with Borel σ-algebra. Its measure `μH`
  is s-finite, right invariant and finite on compact sets.
- `μG` is a measure on `G` that is finite on compact sets and **left**
  invariant. No unimodularity is assumed.
- `ν` is a measure on the left coset space `LeftQuotient H` (cosets `H g`)
  that is finite on compact sets. It satisfies the existing compatibility
  predicate `IsCompatible H μG μH ν`: it is nonzero, regular and invariant
  under every right translation, and it satisfies the Weil integration
  formula for compactly supported continuous functions.
- `LeftQuotient H` is compact. In particular `ν` is a finite measure.
- `π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)` preserves norms and has almost
  everywhere strongly measurable orbits, as required by the existing
  `integratedIsometricAction`. For every `g` and every `L²` class `φ`, the
  class `π g φ` is represented `ν`-almost everywhere by
  `q ↦ φ (rightTranslate H g q)`. So `π` is the original right regular
  action, supplied with its defining property rather than as a chosen
  construction.

## Conclusion

For every compactly supported continuous `f : C_c(G, ℂ)`, the integrated
operator `integratedIsometricAction μG π _ _ f hf` is Hilbert–Schmidt in the
sense of the published predicate
`Langlands.Analysis.OperatorIdeals.IsHilbertSchmidt`. That operator is the
Bochner integral `φ ↦ ∫ g, f g • π g φ ∂μG`. The predicate asks for square
summability of the images of one Hilbert basis. The integrability proof
`hf` is a quantified argument; any proof gives the same operator.

The single universe of `G` also carries the subgroup and the quotient.
No trace-class conclusion, spectral decomposition, finite multiplicity or
automorphic specialization is asserted.

## Sources and provenance

This is a derived statement. The source is Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

- Lemma 9.3.3, printed pp.247–248 (one-based PDF pp.259–260), assumes that
  `[G]` has finite volume. If `R(f)` is bounded from a closed invariant
  subspace to bounded functions, its proof first derives the
  Hilbert–Schmidt property from point evaluations and finite volume.
- Theorem 9.1.2 and Corollary 9.1.3, printed p.241 (PDF p.253), state the
  trace-class property and the discrete decomposition on the cuspidal
  subspace.

When the quotient is compact, the needed sup-norm estimate holds on the
whole `L²` space, with no cuspidality, rapid decay or reduction theory.
The statement isolates that case. It generalizes in two ways:

- it allows an arbitrary closed subgroup `H` with compact left coset space
  and a compatible quotient measure, instead of `A_G G(F)` in `G(A_F)`;
- it uses compactly supported continuous weights instead of smooth ones.

For a connected reductive group whose quotient `[G]` is compact, the
Library's actual quotient `PositiveRationalQuotient` is the left coset
space of `positiveRationalSubgroup`. Its measure satisfies `IsCompatible`
with the ambient Haar measure by
`positiveRationalQuotientHaarMeasure_isCompatible`. The statement is
designed for that specialization, which still has to check the remaining
instance hypotheses and the compactness of the quotient.

## Intended proof

A private proof compiles. It uses only published results and the
pointwise statement `Langlands.Analysis.IntegratedTranslationPointwiseStatement`.
That statement is itself submitted separately, and the proof will use its
proof once that is published.

1. Compactness of the quotient and openness of the quotient map give a
   compact set `C ⊆ G` of coset representatives.
2. For `g ∈ C`, translate and conjugate the weight to
   `h_g(b) = conj f(g⁻¹ b)`. The published `quotientL2Unfolding` supplies
   an `L²` vector `v_g` representing the quotient average of `h_g`. It
   also gives `⟨v_g, φ⟩ = ∫ f(g⁻¹ b) φ(H b) dμG(b)` for every `φ`.
3. Left invariance of `μG` rewrites that integral as
   `∫ f(a) φ(H g a) dμG(a)`, the pointwise value of `R(f)φ` at `H g`.
4. The averages of the `h_g` are bounded by `sup |f| · μH(K₀)`, with `K₀`
   the compact set of `h ∈ H` lying in `C · supp f · C⁻¹`. So
   `‖v_g‖ ≤ ν(X)^{1/2} · sup |f| · μH(K₀)`, uniformly in `g ∈ C`.
5. The pointwise statement identifies `R(f)φ` almost everywhere with
   these evaluations. The published `hilbertSchmidtUniformEvaluation`
   criterion then gives the Hilbert–Schmidt property.
