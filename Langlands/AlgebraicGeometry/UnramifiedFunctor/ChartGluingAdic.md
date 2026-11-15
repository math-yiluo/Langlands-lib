# Factorization on the spectrum of a local ring

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingAdic`, second of the five
modules proving `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartGluingStatement`.
Namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing`; internal auxiliary
results. It formalizes the step (iii) ⇒ (ii) of the proof of SGA 3, XI, Proposition 3.1
(printed p. 96 of the Gille–Polo recomposition, `sga3-exposes-xi-xii-xiv-gille-polo-2008`):
for a point `t` of `T` with noetherian local ring `A = 𝒪_{T,t}`, a factorization of `η` through
`ξ` at the residue field extends to `Spec A`. Notation (`Fac`, `W`, `resPt`, conditions) is that
of `ChartGluingFac`; `AdicLimits` (F3), `InfinitesimallyEtaleAt`, `algebraOver`,
`algebraOverBase`, `algHomOver` are those of the published modules `MurreCriterionStatement`
and `MurreLocalToGlobalSteps`.

## Section `Adic`: morphisms out of the spectrum of a complete local ring

Let `A` be a local ring with maximal ideal `m`.

* `maximalIdeal_pow_succ_ne_top`, and instances: `A / m^(n+1)` is nontrivial and local.
* `comap_mk_maximalIdeal_pow`, `eq_of_quotient_pow`: `Spec (A / m^(n+1))` has exactly one
  point, which lies over the closed point of `Spec A`.
* `specMap_closedPoint`: `Spec` of a local homomorphism maps the closed point to the closed
  point.
* `range_subset_of_isLocalRing`: a morphism `Spec B ⟶ X` (`B` local) whose closed point lands
  in an open set `O` lands in `O` entirely (every point specializes to the closed point).

Assume now `A` is `m`-adically complete.

* `exists_specMap_adic_lift`: a compatible family `uₙ : Spec (A / m^(n+1)) ⟶ X` is the
  restriction of one `g : Spec A ⟶ X`. All `uₙ` send the unique point to the same point `x`.
  Choose an affine open `Spec R ⊆ X` around `x`; every `uₙ` lands in it
  (`range_subset_of_isLocalRing`), hence is `Spec` of a ring map `ψₙ : R → A / m^(n+1)`. The
  `ψₙ` are compatible, and Mathlib's `IsAdicComplete.StrictMono.liftRingHom` gives
  `ψ : R → A`; take `g := Spec ψ` followed by the inclusion.
* `specMap_adic_ext`: two morphisms `Spec A ⟶ X` agreeing on every `Spec (A / m^(n+1))` are
  equal. Both send the closed point to the same point, so both factor through one affine open
  `Spec R`; the two ring maps `R → A` agree modulo every `m^(n+1)`, hence agree since `A` is
  `m`-adically Hausdorff (`IsHausdorff.StrictMono.funext'`).

## Factorization over artinian and complete local rings

Here `ξ` is a monomorphism, infinitesimally étale at every point, and `F` satisfies (F1b).

* `algHomOver_comp_algebraOverBase`: compatibility of the helper morphisms of
  `MurreCriterionStatement`.
* `fac_id_of_isArtinianRing`: for a local artinian ring `B`, `f : Spec B ⟶ S` and
  `η ∈ F(Spec B)` with the closed point in `W ξ η`, `η` itself factors through `ξ`. The
  factorization at the residue field `B/m_B` (from `fac_fieldPt_iff`) is a morphism
  `u₀ : Spec (B/m_B) ⟶ U`; `m_B` is nilpotent, so infinitesimal étaleness of `ξ` at the image
  point gives `u : Spec B ⟶ U` with `F.map u.op ξ = η`. This is the first sentence of
  SGA 3, XI 3.1 (iii) ⇒ (ii), done for one artinian ring at a time.
* `fac_quotient_pow`: for a noetherian local ring `A`, the same hypothesis at the closed point
  gives `Fac ξ η` on every `Spec (A / m^(n+1))` (these rings are local artinian; the closed
  point of `W` is transported by `mem_W_map_iff`).
* `fac_id_of_isAdicComplete`: if moreover `A` is complete and `F` satisfies (F3), then `η`
  factors through `ξ`. The factorizations `uₙ : Spec (A / m^(n+1)) ⟶ U` are compatible (because
  `ξ` is a monomorphism), so `exists_specMap_adic_lift` gives `g : Spec A ⟶ U`, an
  `S`-morphism by `specMap_adic_ext`. Then `F.map g.op ξ` and `η` have the same restriction to
  every `Spec (A / mⁿ)` (for `n = 0` via the restriction from `n = 1`), so they are equal by
  the injectivity half of (F3). This is the middle of SGA 3, XI 3.1 (iii) ⇒ (ii).

## Factorization on the spectrum of a local ring

* `stalkPt T t : Over.mk (T.left.fromSpecStalk t ≫ T.hom) ⟶ T`, the canonical morphism
  `Spec 𝒪_{T,t} → T`.
* `fac_stalkPt`: if `𝒪_{T,t}` is noetherian and `t ∈ W ξ η`, then `Fac ξ η (stalkPt T t)`.
  Let `A = 𝒪_{T,t}` and `Â` its `m`-adic completion; `Â` is local, noetherian (Library instance
  from `Langlands.AlgebraicGeometry.Deformation.AdicCompletionNoetherian`) and complete, and
  `A → Â` is faithfully flat (`Module.FaithfullyFlat.of_flat_of_isLocalHom`), so
  `Spec Â ⟶ Spec A` is flat, surjective and quasi-compact. The closed point of `Spec Â` maps to
  `t`, so `fac_id_of_isAdicComplete` gives the factorization on `Spec Â`, and `fac_of_flat`
  descends it to `Spec A`. This is the last sentence of SGA 3, XI 3.1 (iii) ⇒ (ii).
