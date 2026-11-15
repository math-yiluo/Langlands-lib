# Step 1 of Murre's induction: from ring-level to scheme-level chart conditions

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseSpec`, a supporting module of
`murreArtinianBase` (module `MurreArtinianBase`). Namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase`. Notation as in `ArtinianBaseTools`.

The Library's chart-gluing theorem `ChartGluing.murreChartGluing` takes two hypotheses on a chart
`ξ ∈ F(U)`: `IsMonoElement F ξ` and `InfinitesimallyEtaleAt F ξ y`. Both are defined in the
Library module `MurreLocalToGlobalSteps` in terms of morphisms in `Over (Spec R)`. This module derives
them for `U = Spec B` from the ring-level properties proved in `ArtinianBaseChart`.

* `exists_homR`: every morphism `ovR R T' ⟶ ovR R T` over `Spec R` is `homR φ` for an `R`-algebra
  map `φ : T → T'`. `Spec` is fully faithful, and the map commutes with the structure morphisms.
* `homR_injective`: `homR` is injective.
* The reused `Charts.locallyOfFiniteType_ovR` and `Charts.formallyUnramified_ovR`
  from `MurreCharts` show that `Spec B ⟶ Spec R` is locally of finite type, respectively
  formally unramified, when `B` has the corresponding property over `R`.
  Their proofs use `HasRingHomProperty.Spec_iff`.
* `infinitesimallyEtaleAt_of_ring`: suppose `ξ ∈ F(Spec B)` has unique lifts at the ring level.
  That is, for every local artinian `R`-algebra `A`, nilpotent ideal `I`, `u₀ : B → A/I` and
  `v ∈ F(Spec A)` with `u₀^* ξ = v|_{A/I}`, there is a unique `u : B → A` lifting `u₀` with
  `u^* ξ = v`. Then `InfinitesimallyEtaleAt F ξ y` holds at every point `y`.
  - The Library definition quantifies over local artinian rings `A` with a morphism
    `Spec A ⟶ Spec R`. Such a morphism is `Spec` of a ring map, which makes `A` an
    `R`-algebra.
  - The test objects `algebraOver` and the morphisms over `Spec R` are then identified with
    `ovR R (A/J)` and `homR` of `R`-algebra maps, using `towerIso` and `exists_homR`.
* `isMonoElement_of_field`: let `B` be of finite type and formally unramified over `R`, and let
  `ξ ∈ F(Spec B)` separate `R`-algebra maps from `B` to fields. Then `ξ` is a monomorphism
  (`IsMonoElement F ξ`).
  - Let `h₁, h₂ : T ⟶ Spec B` over `Spec R` have the same image in `F(T)`.
  - At each point `z` of `T`, the composites with `Spec κ(z) ⟶ T` correspond to two maps
    `B → κ(z)` with the same restriction of `ξ`, so they are equal.
  - `Spec B ⟶ Spec R` has open diagonal (locally of finite type and formally unramified). The
    Library lemmas `Charts.lift_mem_range_diagonal` and
    `Charts.eq_of_forall_mem_range_diagonal` then give `h₁ = h₂`.
