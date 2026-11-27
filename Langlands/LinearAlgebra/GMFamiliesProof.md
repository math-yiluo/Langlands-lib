# Arthur's lemmas on `(G, M)`-families: the conjunction

Module `Langlands.LinearAlgebra.GMFamiliesProof`, namespace `Langlands.GMFamily`. It proves
`GMFamilyStatement` of [`GMFamiliesStatement`](GMFamiliesStatement.md) without hypotheses.

```lean
theorem gmFamily : GMFamilyStatement.{u}
```

The statement, as published (not changed), is the conjunction
`SmoothExtensionStatement.{u} ∧ SplittingFormulaStatement.{u} ∧ DescentFormulaStatement.{u} ∧
AlternateSplittingFormulaStatement.{u}` of four statements about `(G, M)`-families in the
Euclidean model of [`GMFamilies`](GMFamilies.md). Each quantifies over a finite-dimensional real
inner product space `E : Type u`, a root set `R` and Levi spaces of `R`:

- `SmoothExtensionStatement` (Arthur 2005, Lemma 17.1): for a `(G, M)`-family `c`, a smooth
  function on `StrongDual ℝ a` agrees with `cM R a c` wherever every `theta a S Λ` is nonzero.
- `SplittingFormulaStatement` (Lemma 17.4): for two families `c, d`,
  `(cd)_M(λ) = ∑_{Q ∈ 𝓕(M)} c_M^Q(λ) d'_Q(λ_Q)` off finitely many hyperplanes.
- `DescentFormulaStatement` (Lemma 17.5, restricted to Levi subgroups `M₁ ⊆ M` over the same
  field): for a `(G, M₁)`-family `c₁` and `ξ ∈ 𝔞_{M₁}^M` in general position, the induced family
  satisfies `c_M(λ) = ∑_{L₁ ∈ 𝓛(M₁)} d_{M₁}^G(M, L₁) c_{M₁}^{Q₁}(λ)` off finitely many
  hyperplanes. The case of `M₁` over a proper extension of the field of `M` is not part of the
  statement (see the Markdown of `GMFamiliesStatement`).
- `AlternateSplittingFormulaStatement` (Lemma 17.6): for two families `c, d` and `ξ ∈ 𝔞_M^G` in
  general position,
  `(cd)_M(λ) = ∑_{L₁, L₂ ∈ 𝓛(M)} d_M^G(L₁, L₂) c_M^{Q₁}(λ) d_M^{Q₂}(λ)` off finitely many
  hyperplanes.

## Proof

The theorem is the anonymous constructor of the conjunction applied to four theorems, each
taken at the same universe `u`:

```lean
⟨smoothExtension.{u}, splittingFormula.{u}, descentFormula.{u}, alternateSplittingFormula.{u}⟩
```

- `smoothExtension : SmoothExtensionStatement`
  ([`GMFamilySmoothExtension`](GMFamilySmoothExtension.md)): the chamber terms are put over a
  common denominator, the numerator vanishes on every wall by cancellation of the two chambers
  adjacent across it, and smooth division by the product of wall factors gives the extension.
- `splittingFormula : SplittingFormulaStatement.{u}`
  ([`GMFamiliesSplittingProof`](GMFamiliesSplittingProof.md)): the chamber inversion (17.9),
  proved with a determinant evaluation of the alternating theta sums, applied to each chamber
  term of the product family and followed by a rearrangement over faces.
- `descentFormula : DescentFormulaStatement.{u}`
  ([`GMFamiliesDescentProof`](GMFamiliesDescentProof.md)): both sides are expanded over fine
  chambers, and the weighted vertex sums of the affine chamber slices are evaluated, with finite
  wall cancellation for fine chambers containing no coarse chamber in their closure.
- `alternateSplittingFormula : AlternateSplittingFormulaStatement.{u}`
  ([`GMFamilyAlternateSplittingProof`](GMFamilyAlternateSplittingProof.md)): the coefficient of
  each product `c P₁ Λ * d P₂ Λ` is expressed as a sum over feasible intersections of two
  translated chambers, and its invariance under change of generic intercepts reduces it to a
  reference position.

The four component statements are unchanged; this module adds no hypothesis, definition or
lemma. The theorem depends on the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## Source

J. Arthur, *An introduction to the trace formula*, §17, Lemma 17.1 (printed p.94), Lemma 17.4
(pp.97–98), Lemma 17.5 (pp.99–100) and Lemma 17.6 (p.101), in the volume registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`; and J. Arthur, *The invariant trace
formula. I. Local theory*, §7, Proposition 7.1 and Corollary 7.4 (printed pp.357–358), registered
as `arthur-1988-invariant-trace-formula-I`. The source of each component and the route of its
Lean proof are in the Markdown of its module.
