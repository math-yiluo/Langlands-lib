# Spreading out a factorization from a local ring

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingGerm`, third of the five
modules proving `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartGluingStatement`.
Namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing`; internal auxiliary
results. It formalizes the passage from `Spec 𝒪_{T,t}` to an open neighbourhood of `t` in the
proof of SGA 3, XI, Proposition 3.1 (ii) ⇒ (i) (printed p. 95 of the Gille–Polo recomposition,
`sga3-exposes-xi-xii-xiv-gille-polo-2008`: "`𝒪_{S,s}` is the inductive limit of the rings of
the affine neighbourhoods of `s`, and `F` commutes with inductive limits of rings"). Notation is
that of `ChartGluingFac` and `ChartGluingAdic`. `Good`, `specOver` and `good_all` are from the
published module `MurreBaseChangeColimits`: `specOver h` is the functor
`B ↦ (Spec B ⟶ Spec R ⟶ S)` on rings under `R`, `Good F h` says that `specOver h ⋙ F` preserves
filtered colimits, and `good_all` proves `Good F h` for every `h : Spec R ⟶ S` from (F1a) and
(F2).

## Section `UnderColimit`

* `isColimitOfElements`: a cocone in `Under R` over a filtered diagram is a colimit if it is a
  colimit on underlying sets (every element comes from some stage; two elements identified in
  the cocone are identified at a later stage). The forgetful functors `Under R ⥤ CommRingCat`
  and `CommRingCat ⥤ Type` reflect these colimits.
* `exists_eq_of_isColimit`, `exists_of_isColimit`: for `Good F h` and a filtered colimit cocone
  `c` in `Under R`, two elements of `F(Spec Dⱼ)` with the same image in `F(Spec c.pt)` become
  equal at a later stage, and every element of `F(Spec c.pt)` comes from some stage
  (`Types.FilteredColimit` API).
* `underBase`, `specOver_map_comp_underBase`, `map_underBase`: the structure morphism
  `Spec B ⟶ Spec R` over `S` and its naturality.

## Section `Localization`: `R_P` as a filtered colimit

For a prime `P` of a ring `R`:

* `DivIdx P`: elements of `R \ P`, preordered by divisibility; it is directed (`a, b ≤ ab`).
* `locMap`, `locDiagram P`: the diagram `a ↦ R_a` of rings under `R`.
* `locToAtPrime`, `locCocone P L`: for a localization `L` of `R` at `P`, the cocone `R_a → L`.
* `isColimitLocCocone`: `L = R_P` is the colimit of the `R_a`, `a ∉ P`, checked on elements
  with `isColimitOfElements`: every element `r/s` of `L` comes from `R_s`; if `x, y ∈ R_a` have
  the same image in `L`, write `x - y = α/aⁿ`; then `mα = 0` for some `m ∉ P`, and `x = y` in
  `R_{am}`.
* `exists_away_eq_of_atPrime`: with (F1a) and (F2), two elements of `F(Spec R)` with the same
  restriction to `Spec R_P` have the same restriction to `Spec R_g` for some `g ∉ P`.

## Germs of elements on schemes

* `exists_opens_eq_of_isOpenImmersion`: for an open immersion `j : Spec R ⟶ T.left`, two
  elements of `F(T)` with the same restriction to `Spec R_P` agree on an open neighbourhood of
  `j(P)`: apply the previous lemma, and take the open image of `Spec R_g ⟶ Spec R ⟶ T`, which
  contains `j(P)` (`PrimeSpectrum.localization_away_comap_range`).
* `specMap_germ_fromSpec`, `stalkAlgebraToStalkPt`, `stalkAlgebraToStalkPt_comp`: for an affine
  open `W ∋ t`, the morphism `Spec 𝒪_{T,t} ⟶ T` is `Spec` of the germ map `Γ(T, W) → 𝒪_{T,t}`
  followed by `W ⊆ T`; `stalkAlgebraToStalkPt` is the identity of `Spec 𝒪_{T,t}` between the two
  resulting objects of `Over S`.
* `exists_opens_eq_of_stalkPt`: two elements of `F(T)` with the same restriction along
  `stalkPt T t` agree on an open neighbourhood of `t` (an affine open `W ∋ t`; `𝒪_{T,t}` is the
  localization of `Γ(T, W)` at the prime of `t`, `IsAffineOpen.isLocalization_stalk`).
* `LocFac.of_map`: for an `S`-morphism `c : X ⟶ T` that is an open immersion, a local
  factorization of `η|_X` near `x` gives one of `η` near `c(x)`.

## Spreading out

`locFac_of_mem_W`: let `ξ` be a monomorphism, infinitesimally étale at every point, with
`U → S` locally of finite type, and let `F` satisfy (F1a), (F1b), (F2), (F3). Let `t ∈ W ξ η`
be a point of `T` with noetherian stalk at which `T` is germ-injective
(`Scheme.IsGermInjectiveAt`, true for instance on locally noetherian schemes). Then
`LocFac ξ η t`. Proof:

1. `fac_stalkPt` (module `ChartGluingAdic`) gives `k : Spec 𝒪_{T,t} ⟶ U` over `S` with
   `F.map k.op ξ = η|_{Spec 𝒪_{T,t}}`.
2. Mathlib's `spread_out_of_isGermInjective'` (using that `U → S` is locally of finite type)
   gives an open `V ∋ t` and an `S`-morphism `f : V ⟶ U` whose restriction to
   `Spec 𝒪_{T,t}` is `k`.
3. The elements `F.map f.op ξ` and `η|_V` of `F(V)` then have the same restriction to
   `Spec 𝒪_{V,t}` (identified with `Spec 𝒪_{T,t}` through `Spec` of the stalk map of `V ⊆ T`),
   so by `exists_opens_eq_of_stalkPt` they agree on an open `V' ∋ t` of `V`; hence `η` factors
   through `ξ` on `V'`, and `LocFac.of_map` transports this to `T`.
