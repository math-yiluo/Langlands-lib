# Trace-class convolution products on a compact left coset space

`Langlands.QuotientIntegration.CompactQuotientConvolutionTraceClassStatement`
is a proposition definition. It supplies no proof.

## Setting

The setting is that of the Hilbert–Schmidt statement
`Langlands.QuotientIntegration.CompactQuotientIntegratedHilbertSchmidtStatement`:

- `G` is a Hausdorff, locally compact, second countable topological group
  with its Borel σ-algebra.
- `H` is a closed subgroup of `G`, with Borel σ-algebra. Its measure `μH`
  is s-finite, right invariant and finite on compact sets.
- `μG` is a measure on `G` that is finite on compact sets and **left**
  invariant.
- `ν` is a measure on the left coset space `LeftQuotient H` (cosets `H g`)
  that is finite on compact sets and satisfies the existing compatibility
  predicate `IsCompatible H μG μH ν` (nonzero, regular, invariant under
  right translations, and the Weil integration formula for compactly
  supported continuous functions).
- `LeftQuotient H` is compact.
- `π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)` preserves norms, has almost
  everywhere strongly measurable orbits, and for every `g` and `φ` the class
  `π g φ` is represented `ν`-almost everywhere by
  `q ↦ φ (rightTranslate H g q)`. So `π` is the original right regular
  action, supplied with its defining property.

## Conclusion

For all compactly supported continuous `f₁ f₂ : C_c(G, ℂ)`, the
convolution `f₁ ⋆ f₂ : g ↦ ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG` is `μG`-integrable,
and the integrated operator
`integratedIsometricAction μG π _ _ (f₁ ⋆ f₂) _`, that is
`φ ↦ ∫ g, (f₁ ⋆ f₂) g • π g φ ∂μG`, is trace class in the sense of the
published predicate `Langlands.Analysis.OperatorIdeals.IsTraceClass`. The
integrability proof is part of the existential conclusion, so no
integrability hypothesis is needed. The convolution is the left-measure
convolution of the published statement
`Langlands.Analysis.IntegratedActionConvolutionStatement`.

No trace formula, trace-class property for a general smooth weight, or
automorphic specialization is asserted. The Dixmier–Malliavin factorization
of a smooth weight into a finite sum of convolutions is not part of this
statement.

## Sources and provenance

This is a derived statement. The source is Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

- Theorem 9.1.2, printed p.241 (one-based PDF p.253): `R_cusp(f)` is of
  trace class for every `f ∈ C_c^∞(A_G \ G(A_F))`.
- Lemma 9.3.3, printed pp.247–248 (PDF pp.259–260), and the end of §9.5
  (PDF p.274): after proving the Hilbert–Schmidt property, the proofs write
  a smooth weight as a finite sum of convolutions `f₁ ∗ f₂` by the
  Dixmier–Malliavin lemma (Theorem 4.2.9, Exercise 9.8). Then `R(f)` is a
  finite sum of products of two Hilbert–Schmidt operators, which are of
  trace class (Exercise 9.2).

The statement isolates the convolution-product step in the case of a
compact quotient, where the Hilbert–Schmidt property holds on the whole
`L²` space. It allows an arbitrary closed subgroup with compact left coset
space and uses compactly supported continuous weights. Section 3.4 of the
same source, formula (3.9), defines convolution with a right Haar measure;
the left-measure form used here is explained in the Markdown of
`IntegratedActionConvolutionStatement`.

## Intended proof

A private proof compiles. Compactly supported continuous weights are
integrable for a measure finite on compact sets. The convolution statement
gives integrability of `f₁ ⋆ f₂` and the identity
`π(f₁ ⋆ f₂) = π(f₁) ∘ π(f₂)`. The compact-quotient Hilbert–Schmidt
statement makes `π(f₁)` and `π(f₂)` Hilbert–Schmidt, and the published
`Langlands.Analysis.OperatorIdeals.hilbertSchmidtProductTraceClass` makes
their composition trace class. The proof will use the proofs of the
convolution and Hilbert–Schmidt statements once those are published.
