# Common zero sets of holomorphic families on complex manifolds are analytic

Module `Langlands.Analysis.Meromorphic.CommonZeroSets`, namespace
`Langlands.Analysis.Meromorphic`.

`E` is a finite-dimensional complex normed space and `M` a topological space charted on `E`.
From the second result on, `M` is assumed to be a complex manifold:
`IsManifold 𝓘(ℂ, E) 1 M`. Holomorphy on a set `W ⊆ M` means
`MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) · W`, as in `IsAnalyticSubset`
(module `Langlands.Analysis.Meromorphic.AnalyticSystems`).

## Definition

- `IsLocallyCommonZeroSet Z` (universe parameter `w`) for `Z ⊆ M`: every point `s₀ ∈ M` has an
  open neighbourhood `W` and a family `f : Λ → M → ℂ`, indexed by some `Λ : Type w`, of
  functions holomorphic on `W`, such that `Z ∩ W = {s ∈ W | ∀ l, f l s = 0}`.

  It differs from `IsAnalyticSubset Z` only in that the family may be infinite (and its index
  type may depend on the point).

## Results

- `exists_finset_zero_iff_of_mdifferentiableOn`: for a family `f : Λ → M → ℂ` (any `Λ`) of
  functions holomorphic on an open `W ⊆ M` and `s₀ ∈ W`, there are an open `V` with
  `s₀ ∈ V ⊆ W` and a finite `t : Finset Λ` such that for all `s ∈ V`:
  `(∀ l, f l s = 0) ↔ (∀ μ ∈ t, f μ s = 0)`.
- `IsLocallyCommonZeroSet.isAnalyticSubset`: a set that is locally the common zero set of
  holomorphic families is an analytic subset, `IsAnalyticSubset 𝓘(ℂ, E) Z`.

## Proofs

- Let `φ = extChartAt 𝓘(ℂ, E) s₀` and `S = W ∩ φ.source`, which is open. Its chart image
  `T = φ '' S = φ.target ∩ φ.symm ⁻¹' S` is open in `E`: the target is open because the model
  `𝓘(ℂ, E)` has no boundary, and `φ.symm` is continuous on it. By
  `mdifferentiableOn_iff_of_subset_source'` (the chart on `ℂ` is the identity,
  `extChartAt_model_space_eq_id`), every `f l ∘ φ.symm` is complex differentiable on `T`. The
  finiteness theorem `exists_finset_zero_iff` (module
  `Langlands.Analysis.SeveralComplex.PointwiseSpan`) at `φ s₀` gives an open `V' ⊆ T` and a
  finite `t`. Take `V = S ∩ φ ⁻¹' V'`, which is open because `φ` is continuous on its source.
  For `s ∈ V` we have `φ.symm (φ s) = s`, so the equivalence on `V'` transfers to `V`.
- Analyticity: at `s₀`, take `W`, `Λ` and `f` from the hypothesis and `V`, `t` from the
  previous result, and use the finitely many functions `g j = f (t.equivFin.symm j)`,
  `j : Fin t.card`, which are holomorphic on `V ⊆ W`. For `s ∈ V`: `s ∈ Z` iff all `f l s`
  vanish (because `Z ∩ W` is the common zero set), iff the `f μ s` with `μ ∈ t` vanish, iff all
  `g j s` vanish.

## Provenance

Internal. This is the classical fact that the common zero set of an arbitrary family of
holomorphic functions on a complex manifold is analytic, i.e. locally cut out by finitely many
of them. It is the last step in the proof of
`Langlands.Analysis.Meromorphic.MeromorphicContinuationAnalyticComplementStatement`
(Bernstein–Lapid, Theorem 3.3 (1)). There Appendix A of the source describes the complement of
the unique-solution locus locally as the common zero set of the (possibly infinitely many)
`n × n` minors of a holomorphic coefficient matrix. The source asserts the analyticity of the
complement without a separate argument; here the passage to finitely many functions is
`Langlands.Analysis.SeveralComplex.exists_finset_zero_iff`.
