# Step 1 of Murre's induction: the family of charts

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseProof`, a supporting module of
`murreArtinianBase` (module `MurreArtinianBase`). Namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase`. Notation as in `ArtinianBaseTools`.

This module assembles a `u`-small family of charts for `F` over a local artinian `R`. Every
point of `F` with values in a field factors through one of the charts. Together with the
chart conditions, this is what `ChartGluing.murreChartGluing` needs.

## Ring-level charts

* `RingChart ξ`, for `ξ ∈ F(Spec B)`: the conjunction of the two ring-level properties of
  `exists_chart_ring`.
  - Unique infinitesimal lifting along nilpotent ideals of local artinian `R`-algebras.
  - Separation of `R`-algebra maps from `B` to fields.
* `RingChart.transport`: the property is invariant under an `R`-algebra isomorphism `B ≃ B'`.
* `RingChart.good`: for `B` of finite type and formally unramified over `R`, a ring-level chart
  satisfies `IsMonoElement F ξ` and `InfinitesimallyEtaleAt F ξ y` for all `y`. This combines
  `isMonoElement_of_field` and `infinitesimallyEtaleAt_of_ring`.

## Charts through finite field points

From here on `R` is local artinian with residue field `k = ResidueField R`.

* `residue_nil`: the kernel of `R → k` is nilpotent.
* `exists_ringChart_finite`: let `κ` be a finite extension of `k` and `η ∈ F(Spec κ)`. Then
  there are an `R`-algebra `B` and `ξ ∈ F(Spec B)` with:
  - `B` of finite type, formally unramified and artinian over `R`;
  - `RingChart ξ`;
  - a map `ρ : B → κ` with `ρ^* ξ = η`.

  The proof chains three earlier results.
  1. `exists_minimal` gives a minimal separable field of definition `E ⊆ κ` with
     `θ ∈ F(Spec E)`.
  2. `exists_etale_lift` gives a formally étale local artinian `E_L` over `R` with residue
     field `E`.
  3. `exists_chart_ring` gives `J` and `ξ`. Take `B = E_L/J`, which is artinian, of finite
     type, and formally unramified as a quotient of a formally étale algebra.

## The index type

The charts must be indexed by a type in universe `u`. Assume
`∀ T, Small.{u} (F.obj (op T))`; this is `SmallValues`.

* `PRing n I`: the presented `R`-algebra `R[X₁, …, Xₙ]/I`.
* `ChartData`: the type of triples `(n, I, x)` with `x` in `Shrink.{u} (F(Spec (PRing n I)))`.
  `ChartData.elem` recovers the element of `F`.
* `ChartData.Good`: `PRing n I` is formally unramified and artinian, and the element is a
  monomorphism, infinitesimally étale at every point.
* `ChartIdx F : Type u`: the subtype of good chart data.
* `exists_index`: every ring-level chart `ξ ∈ F(Spec B)` is isomorphic to an indexed one.
  Here `B` is of finite type, formally unramified and artinian. A presentation
  `B ≅ PRing n I` gives an index `i` whose element is the transport of `ξ`.

## Every field point factors through a chart

`exists_fac_field`: assume (F1a), (F1b), (F2), (F3), (F4′) and strong (F5). For every field `K`
and `η ∈ F(Spec K)`, there are `i : ChartIdx F` and `ρ : PRing i → K` with `ρ^* ξᵢ = η`.

1. By `exists_fg` ((F2)), `η` comes from `x ∈ F(Spec D)` for a finitely generated `R`-subalgebra
   `D ⊆ K`.
2. Take a maximal ideal `𝔫` of `D`. The field `κ = D/𝔫` is of finite type over `k`, hence
   finite over `k` by the Nullstellensatz (`finite_of_finite_type_of_isJacobsonRing`).
3. `exists_ringChart_finite` and `exists_index` give a chart `i` through which the
   restriction of `x` to `κ` factors. So the closed point `𝔫` lies in the Library's
   factorization locus `ChartGluing.W ξᵢ x`, by `ChartGluing.fac_fieldPt_iff`.
4. `W` is open (`ChartGluing.isOpen_W'`, from (F1a), (F1b), (F2), (F3) and the chart
   conditions). It contains a basic open `D(a)` around `𝔫`, with `a ≠ 0`.
5. The generic point of `Spec D` (the image of `Spec K`, since `D ⊆ K`) lies in `D(a)`, hence
   in `W`. `ChartGluing.fac_fieldPt_iff` gives a factorization of `x|_K = η` through
   `ξᵢ`, which `exists_homR` writes as a ring map `PRing i → K`.
