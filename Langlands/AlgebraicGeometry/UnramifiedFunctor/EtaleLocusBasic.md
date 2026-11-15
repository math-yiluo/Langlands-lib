# The étale locus of a closed subscheme of an étale chart: basic dictionary

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusBasic`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus`. This is a
supporting module of the proof of `ClosedOfGenericStatement` (see
`EtaleLocusClosedOfGeneric.md` and `EtaleLocusAssembly.md`). It imports the
published `MurreChartsLocal` and Mathlib's `Mathlib.RingTheory.Etale.Basic`.

Throughout, `R : CommRingCat`, `F : (Over (Spec R))ᵒᵖ ⥤ Type v`, `R'` is an
`R`-algebra, and `𝔍` is an ideal of `R'`.

## Ring-level lifting (section `RingLift`)

- `exists_lift`: for a formally smooth `R`-algebra `R'`, a ring map `φ : R → A`,
  a nilpotent ideal `J` of `A` and a ring map `γ₀ : R' → A/J` compatible with
  `φ`, there is `β : R' → A` with `β ∘ algebraMap = φ` and `mk_J ∘ β = γ₀`.
  This is `Algebra.FormallySmooth.lift`, rewritten for ring maps.
- `lift_unique`: for a formally unramified `R`-algebra `R'`, two ring maps
  `R' → A` that agree on `R` and modulo a nilpotent ideal are equal
  (`Algebra.FormallyUnramified.lift_unique`).

## Spectra (section `SpecHelpers`)

- `specMap_ofHom_comp`: `Spec (φ) ≫ Spec (ψ) = Spec (φ ∘ ψ)` for ring maps.
- `specMap_ofHom_inj`: `Spec` is injective on ring maps.
- `exists_specMap_ofHom`: every morphism `Spec A ⟶ Spec B` is `Spec` of a ring
  map.

## The chart and its points

- `baseMap R R'` is `Spec R' ⟶ Spec R`. `chart R R' 𝔍` is `Spec (R'/𝔍)` as an
  object of `Over (Spec R)`, the object in `ClosedEtaleLocusOpenStatement`.
  `chart_hom` computes its structure morphism.
- `homU γ f hf` is the morphism `Over.mk f ⟶ chart R R' 𝔍` given by a ring map
  `γ : R'/𝔍 → C`, when `f` is the structure morphism `Spec C ⟶ Spec R`
  induced by `γ`. `homU_left` computes its underlying morphism.
- `comp_eq_of_over`: the ring map of an `Over (Spec R)` morphism into the chart
  is compatible with the structure maps.

## The predicate `KillAt`

`KillAt ξ w A β` is a ring-level form of the lifting condition at a point `w`
of `Spec (R'/𝔍)`, for a ring map `β : R' → A`. It says: for every lifting
problem for `ξ` at `w` over `A` whose reduction is `β`, the map `β` kills
`𝔍`. A lifting problem consists of the structure morphism
`f = Spec (β ∘ algebraMap)`, a nilpotent ideal `J`, a morphism
`u₀ : Spec (A/J) ⟶ chart` over `Spec R` sending every point to `w` whose ring
map lifts to `mk_J ∘ β` on `R'`, and `v ∈ F(Spec A)` restricting to
`F(u₀)(ξ)`.

## `infinitesimallyEtaleAt_iff`

For an étale `R`-algebra `R'` and `F` satisfying strong (F5)
(`NilpotentInjective F`), `InfinitesimallyEtaleAt F ξ w` holds if and only if
`KillAt ξ w A β` holds for every local artinian ring `A` and every ring map
`β : R' → A`.

Proof.

- (⇒) Given a lifting problem, étaleness gives a morphism `u : Spec A ⟶ chart`
  extending `u₀`. Its ring map `γ : R'/𝔍 → A` composed with `R' → R'/𝔍`
  agrees with `β` on `R` and modulo `J`. By `lift_unique` (`R'` is formally
  unramified over `R`) it equals `β`, so `β` kills `𝔍`.
- (⇐) Given `u₀` and `v`, write `u₀ = Spec γ₀`. Formal smoothness
  (`exists_lift`) lifts `γ₀ ∘ mk` to `β : R' → A`. `KillAt` shows that `β`
  kills `𝔍`, so it factors through `γ : R'/𝔍 → A`, and `u := homU γ`.
  `u` extends `u₀`, and `F(u)(ξ) = v` by strong (F5), since both restrict to
  `F(u₀)(ξ)`. Uniqueness: another extension has ring map agreeing with `γ`
  on `R` and modulo `J` after composing with `R' → R'/𝔍`. So it equals `γ`
  by `lift_unique`.

The unique lifts in `InfinitesimallyEtaleAt` are thereby reduced to the
vanishing of `β` on `𝔍`. The later modules use this to rewrite étaleness at
`w` as the vanishing of `𝔍` in a stalk of a representing scheme.
