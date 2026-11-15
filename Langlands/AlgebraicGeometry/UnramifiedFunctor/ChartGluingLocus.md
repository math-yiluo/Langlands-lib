# The open locus of factorization through a chart

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingLocus`, fourth of the five
modules proving `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartGluingStatement`.
Namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing`; internal auxiliary
results. It completes the relative form of SGA 3, XI, Proposition 3.1 (iii) ⇒ (i) (printed
pp. 95–96 of the Gille–Polo recomposition, `sga3-exposes-xi-xii-xiv-gille-polo-2008`) used in
the proof of Proposition 3.5: for a chart `ξ ∈ F(U)` and any `η ∈ F(T)`, the fibre product
`T ×_F U` is the open subscheme `W ξ η` of `T`. Notation is that of `ChartGluingFac`,
`ChartGluingAdic` and `ChartGluingGerm`.

`ChartGluingGerm.locFac_of_mem_W` needs `T` to have a noetherian stalk and to be germ-injective
at the point. In SGA 3, 3.1 (iii) ⇒ (ii) only uses local rings `𝒪_{S,s}` of the locally
noetherian base. In the relative form needed here the test scheme `T` is an arbitrary
`S`-scheme, so this module first reduces to a noetherian `T` with condition (F2), as follows.

## Section `Adjoin`: an algebra as a filtered colimit

For an `R`-algebra `B`:

* `adjoinMap`, `adjoinDiagram R B`: the diagram `s ↦ R[s] ⊆ B` over finite subsets `s` of `B`,
  as rings under `R` (directed by inclusion).
* `adjoinCocone R B`, `isColimitAdjoinCocone`: `B` is the filtered colimit of its finitely
  generated subalgebras (checked on elements with `isColimitOfElements`).
* instance: `R[s]` is noetherian when `R` is (finite type over a noetherian ring).

## The local factorization

Assume `ξ` is a monomorphism, infinitesimally étale at every point, with `U → S` locally of
finite type, and `F` satisfies (F1a), (F1b), (F2), (F3).

* `locFac_of_mem_W_affine`: for a noetherian ring `R`, `h₀ : Spec R ⟶ S`, an `R`-algebra `B`
  and `η ∈ F(Spec B)`, `η` factors through `ξ` near every point of `W ξ η`. By (F2)
  (`good_all` and `exists_of_isColimit`), `η = x|_{Spec B}` for some
  `x ∈ F(Spec R[s])` with `R[s] ⊆ B` finitely generated. `Spec R[s]` is noetherian, hence
  locally noetherian and germ-injective, so `locFac_of_mem_W` applies to `x` at the image point
  (which lies in `W ξ x` by `mem_W_map_iff`), and `LocFac.pullback` gives the claim for `η`.
* `locFac_of_mem_W'`: if `S` is locally noetherian, then for every `T : Over S`, every
  `η ∈ F(T)` and every `t ∈ W ξ η`, `η` factors through `ξ` near `t`. Choose an affine open
  `S₀ = Spec Γ(S, S₀)` of `S` containing the image of `t` (with `Γ(S, S₀)` noetherian) and an
  affine open `V ∋ t` of `T` mapping into `S₀`; then `V = Spec Γ(T, V)` is an object of the
  form `algebraOver (S₀ ⟶ S) Γ(T, V)`, and `locFac_of_mem_W_affine` together with
  `LocFac.of_map` concludes.
* `fac_iff_range_subset_W` (SGA 3, XI 3.1 relative to `T`): over a locally noetherian `S`,
  `Fac ξ η a ↔ Set.range a.left ⊆ W ξ η` for every `a : T' ⟶ T`; this is
  `ChartGluingFac.fac_iff_range_subset` with the hypothesis `hloc` supplied by
  `locFac_of_mem_W'`.
* `isOpen_W'`: over a locally noetherian `S`, `W ξ η` is open (`ChartGluingFac.isOpen_W`).
