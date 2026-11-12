# Renard II.3.7–II.3.8: modular distribution formulas

This statement unit uses the published integration and density maps and the
reciprocal adapters `Distribution.renardModular` and
`Distribution.renardAutomorphismModule`. It supplies no proofs. The namespace is
`Langlands.HarmonicAnalysis.Distribution.RenardModular`; `Statements` is the
conjunction of the seven individually closed Prop-valued declarations.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Locators: II.3.7 definition, displayed integral and Proposition, printed p.47 /
PDF p.53; unimodularity definition, examples and (II.3.7.1), printed p.48 /
PDF p.54; II.3.8, including (II.3.8.1), on the same page.

`TranslationStatement` asserts the source's `r(g)μ = δ(g)μ` on the actual
algebraic distribution `ofMeasure μ`, and its two-sided test-integral formula
with argument `h' * x * h⁻¹`. Both scalars use the source convention, the inverse
of Mathlib's `Measure.modularCharacter g`. The right point action is
`x ↦ xg⁻¹`. No complex conjugation occurs.

`RegularityStatement` states positivity, local constancy, continuity and
triviality on every compact subgroup. The source states the character property
and compact-subgroup triviality. Local constancy and continuity are explicit
regularity bridges: the Library's `Langlands.Haar.isLocallyConstant_modularCharacter`,
`continuous_modularCharacter` and `modularCharacter_eq_one_of_mem_compact`
already prove the Mathlib-convention versions for nonarchimedean locally compact
groups. Composition with inversion and the identity
`renardModular g = Measure.modularCharacter g⁻¹` give the precise correspondence.
Mathlib's `Measure.modularCharacterFun_pos` supplies positivity. The character
law itself is already built into the published `renardModular : G →* ℝ≥0`.

`InversionDensityStatement` states Proposition (ii) on the actual density map:
the uniquely specified locally constant function `d(g) = δ(g)⁻¹` produces a
right-invariant distribution equal to `GroupAction.inversionDistributions μ`.
The existential witness is constrained pointwise at every group element;
there is no arbitrary replacement density. The statement retains all t.d.
groups, whereas `Langlands.Haar.HaarInversionDensityStatement` concerns measures
and requires second countability. No such extra restriction is imposed here.

`UnimodularityStatement` records the literal source property `∀ g, δ(g)=1`,
its equivalence with right invariance of the left Haar distribution, and all
three examples: abelian groups, compact groups, and groups in which each element
belongs to a compact subgroup. The pinned Mathlib has no group-level
`IsUnimodular` definition; its similarly named module notion is unrelated.
Thus the source definition is represented by this exact character property.

`AutomorphismStatement` states actual automorphism pushforward scaling and the
complex test-integral identity (II.3.7.1). The automorphism is a supplied
`ContinuousMulEquiv`, with the original topology. `InnerAutomorphismStatement`
identifies its module with `δ(h)` when its point map is exactly
`x ↦ h*x*h⁻¹`. The pointwise premise specifies the actual inner map rather than
assuming the scalar identity. These statements use any Mathlib Haar measure;
regularity and countability are not premises.

`IndexFormulaStatement` uses the actual preimage subgroup
`P = σ⁻¹(K)` and intersection `L = K ∩ P`. It states the preimage mass scaling,
the two mass/index identities, and
`δ(σ) = [P:L]/[K:L]` in the nonnegative reals. Mathlib's `L.relIndex K` means
`[K:L]`, so the numerator is `L.relIndex P`. This is the exact orientation of
(II.3.8.1). The existing `Langlands.Haar.CompactOpenIndexHaarStatement` and its
proof use the reciprocal automorphism character and an image-oriented
multiplicative identity. They are reusable inputs but are not substituted for
the explicit preimage formula here. The compact open subgroup is the supplied
one; no finiteness or nonzero-denominator hypothesis is assumed in place of
what compactness and openness must establish.
