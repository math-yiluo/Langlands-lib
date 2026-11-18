# Open charts covering the moduli functor from frame charts

This internal module reduces the published statement
`LargeLevelChartCoverStatement` to three named statements. It adds no
mathematical assertion beyond that implication. The three statements stay
explicit hypotheses.

## Results

- `preimage_eq_top_iff_range_subset`: for a morphism `f : X ⟶ Y` of
  universe-zero schemes and an open `U` of `Y`, `f ⁻¹ᵁ U = ⊤` exactly when the
  set-theoretic range of `f` lies in `U`.
- `frameChart_mem_range_iff`: assume `FrameLocusBaseChangeStatement` in
  universe zero. Let `a : uliftYoneda.{1}.obj X ⟶ moduliFunctor P g d n hd hn`
  be a transformation with the frame-chart property for `ρ`: a class `c.classOf`
  over a level base lies in the image of `a` exactly when `c.frameLocus ρ = ⊤`.
  Then for a datum `b` over a level base `S` and a morphism `f : T ⟶ S`, the
  restriction of `b.classOf` along `f` lies in the image of `a` exactly when the
  range of `f` lies in `b.frameLocus ρ`. The restriction of `b.classOf` is
  `(b.pullback f.hom).classOf`, by definition of `moduliFunctor`. The
  frame-chart property and base change rewrite the condition to
  `f ⁻¹ᵁ b.frameLocus ρ = ⊤`, and the first lemma finishes.
- `largeLevelChartCover_of_frameCharts` is a proved definition: a `def` whose
  type is the proposition `LargeLevelChartCoverStatement`. It takes three
  hypotheses:
  - `Hframe : FrameChartRepresentabilityStatement` (each frame chart is
    represented by a level base);
  - `Hbc : FrameLocusBaseChangeStatement.{0}` (the frame locus commutes with
    base change);
  - `Hcov : FrameLocusCoverStatement.{0}` (for large `n` every point lies in
    some frame locus).

## Proof of the reduction

Fix `P`, `g`, `d` with `0 < g` and `0 < d`. `Hcov` gives a bound `N`. Let
`n ≥ N` with `3 ≤ n`. The index type is the finite type of families
`ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2*g) → ZMod n`. For each
`ρ`, `Hframe` gives a level base `X ρ` and a transformation `a ρ` with
injective components and the frame-chart property.

- *Each `a ρ` is an open chart.* Injectivity is given. Every section `ξ` over a
  level base `S` is the class of some datum `b`, since the moduli functor takes
  values in a quotient. Take `U = b.frameLocus ρ`; `frameChart_mem_range_iff`
  gives the required equivalence for every `f : T ⟶ S`.
- *The charts cover.* For `ξ = b.classOf` and a point `x` of `S`, `Hcov`
  applied to `S`, which is locally noetherian with `n` a unit, gives `ρ` with
  `x ∈ b.frameLocus ρ`. The same open `U = b.frameLocus ρ` works.

## Provenance

This is an internal derivation. It only combines the conclusions of the three
statements, which are documented in their own modules, with the definitions of
`LevelBase.IsOpenChart` and `LevelBase.IsOpenChartCover`.
