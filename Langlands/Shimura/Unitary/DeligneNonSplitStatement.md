# Statement: the real Deligne torus is a non-split torus

Author: Worker 207.

This module states, as one proposition, three properties of the Deligne torus
`S = Res_{ℂ/ℝ} 𝔾_m`. First, it is smooth over `ℝ`. Second, it becomes a split
torus over `ℂ`. Third, it is not a split torus over `ℝ`. Only the proposition is
defined here; this module proves none of the three claims. The declaration is in
the namespace `Langlands.Shimura.DeligneTorus`.

## Lean statement

```lean
def NonSplitTorusStatement : Prop :=
  Smooth groupScheme.X.hom ∧ GroupScheme.IsSplitTorus complexGroupScheme ∧
    ¬ GroupScheme.IsSplitTorus groupScheme
```

- `groupScheme` is the published real Deligne group scheme
  (`DeligneGroupScheme`, Worker 57) over `Spec (CommRingCat.of ℝ)`. Its points
  with values in a real algebra `A` are the units of
  `QuadraticAlgebra A (-1) 0`, that is, of `A ⊗_ℝ ℂ`. So it is
  `Res_{ℂ/ℝ} 𝔾_m`, and its real points are `ℂˣ`.
- `groupScheme.X.hom` is its structural morphism to `Spec ℝ`. `Smooth` is
  Mathlib's `AlgebraicGeometry.Smooth`.
- `complexGroupScheme` is the actual pullback of `groupScheme` along
  `Spec ℂ ⟶ Spec ℝ`, from the published `DeligneSchemeSplitting` module.
- `GroupScheme.IsSplitTorus G` means that `G` is isomorphic, as a group scheme
  over its base, to `splitTorus S I = 𝔾_m^I` for some finite index type `I`.
  See `Langlands/GroupScheme/Torus/Split.md`.

Thus the statement says: `S` is smooth over `ℝ`, `S_ℂ ≅ 𝔾_m^I` for some finite
`I`, and there is no finite `I` with `S ≅ 𝔾_m^I` over `ℝ`.

## Sources

- Milne, *Introduction to Shimura varieties*, in *Harmonic Analysis, the Trace
  Formula, and Shimura Varieties*, Clay Mathematics Proceedings 4 (2005),
  Section 2, paragraph "Hodge structures as representations of S", printed
  p.282 (PDF p.294): "Let S be C^× regarded as a torus over R. [...] Then
  S(C) ≈ C^× × C^× with complex conjugation acting by the rule [...]. We fix
  the isomorphism S_C ≅ Gm × Gm [...]". Later in the same paragraph:
  "X^*(S) = Z×Z with complex conjugation acting as (p, q) ↦ (q, p)". Source ID
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
  `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
- Milne, *Algebraic Groups* (2017), Section 12.e–f, printed p.236 (PDF p.252).
  Definition 12.14: "A torus over k is split if it is isomorphic to a product
  of copies of Gm over k." Further down the page: "The tori are the smooth
  connected algebraic groups of multiplicative type." Source ID
  `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

## Provenance

The three conjuncts formalize what the sources say about `S`.

- **Smoothness.** Milne calls `S` a torus over `ℝ`, and tori are smooth
  (Algebraic Groups, p.236).
- **Split over `ℂ`.** This is the isomorphism `S_C ≅ Gm × Gm`.
- **Not split over `ℝ`.** The sources do not state this in so many words. It is
  the standard consequence of the nontrivial conjugation action
  `(p, q) ↦ (q, p)` on `X^*(S)`. A split torus has trivial Galois action on its
  characters. Equivalently, its real points `(ℝˣ)^I` have no element of
  order 4, while `S(ℝ) = ℂˣ` contains `i`.

The milestone is packaged as one conjunction so that a single proof task proves
all three properties together.

The second conjunct is proved separately by `isSplitTorus_complexGroupScheme` in
the companion module `DeligneSplitTorus`. It is included so that the statement
contrasts the two base fields in one place.
