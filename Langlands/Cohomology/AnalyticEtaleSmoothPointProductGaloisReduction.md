# Smooth point products have coinduced Galois fixed sections

Module `Langlands.Cohomology.AnalyticEtaleSmoothPointProductGaloisReduction`, namespace
`Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic`.

This module proves that the actual smooth point products satisfy the hypothesis
`HasCoinducedGaloisFixedSections` of the Galois-coinduced input
`AnalyticEtaleGaloisCoinducedLocalAcyclicStatement`
(module `Langlands.Cohomology.AnalyticEtaleGaloisCoinducedLocalAcyclic`). It then
derives the conditional reduction

`analyticEtaleSmoothPointProductLocalAcyclicCorrected_of_galoisCoinduced :
  AnalyticEtaleGaloisCoinducedLocalAcyclicStatement L X R G ρ →
    AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement L X h R G ρ`.

The Galois-coinduced statement is an explicit hypothesis of this theorem and is not
proved here. Everything in the module is algebra. It uses the fixed-coordinate
description of twisted induction in
`Langlands.Sheaf.Equivariant.TwistedInductionFixedCoordinates`.

The module's main new definition is the type `CosetFiber` of coset-fibre coordinates,
with its deck-group action `cosetFiberAction` (see *The coset fibres* below). The
remaining declarations are the lemmas and theorems listed in the sections below.

## Provenance

This is internal, derived content. It formalizes the observation in step (1′) of the
proof of Proposition 1.5.1 in Berkovich's manuscript *Etale equivariant sheaves on
p-adic analytic spaces* (1995–1996, printed p. 11). There, the sections of the
induced point product over a Galois covering `X′` are
`∏_i ∏_{(i, x′, ψ)} F_{x_i}`, a direct product of coinduced `Gal`-modules. The proof
below is the Library-level version of that sentence.

## Free actions and coinduction (generic algebra)

* `orbitMap_bijective`. If a group `Γ` acts freely on `T` (`γ • t = t → γ = 1`), and
  `e : Q ≃ T/Γ` identifies `Q` with the orbits, then `(γ, o) ↦ γ • (e o).out` is a
  bijection `Γ × Q → T`. For injectivity, equal translates lie in the same orbit, so
  `o = o'`, and freeness gives `γ = γ'`. For surjectivity, the chosen representative of
  the orbit of `t` is a translate of `t`.
* `coinduced_bijective`. Consequently `u ↦ (γ ↦ (o ↦ u (γ • (e o).out)))` is a bijection
  from `T → N` to `Γ → Q → N`. Functions on a free `Γ`-set form a coinduced module.
* `coinduced_pi_bijective`. The same for a family `T i` of free `Γ`-sets with
  coefficients `N i`, giving `(∀ i, T i → N i) → (Γ → ∀ i, Q i → N i)`.
* `sigmaReindex_bijective`. Reindexing `∀ a i, β a i → N i` as
  `∀ i, (Σ a, β a i) → N i` is bijective.

## Deck transformations in Kan coordinates

* `projection_map_transportTo`. For any twisted arrow `f : U ⟶ V` and labels with
  `g' = g * (twist f)⁻¹`, the `g`-coordinate of the restriction of `s` along `f` is the
  restriction along `transportTo f g g'` of the `g'`-coordinate of `s`. This is
  `map_projection` with a prescribed label.
* `deckTransport V e he g`. The ordinary arrow of the translate of `V` by `g` to itself
  underlying `deckEndomorphism V e he`. It has twist `1` (`twist_deckEndomorphism`) and
  underlying arrow `e.hom` (`deckTransport_left`).
* `sectionCoordinates_projection_deck`. In the point coordinates of the point product
  over `etaleGodementPoints L h`, restricting along a deck transformation moves the
  coordinate at the fibre point `p` of the `g`-translate to the coordinate at the image
  of `p` under `deckTransport`. The proof combines `projection_map_transportTo` with
  `PointProduct.sectionCoordinates_restrict`.

## The coset fibres

For a twisted étale object `V`, an open subgroup `Kₒ` and an index
`i : ULift (L-points of X)`, `CosetFiber L h V Kₒ i` is the type of pairs `⟨c, p⟩` of a
left coset `c ∈ G ⧸ Kₒ` and a point `p` of the `i`-th fibre of the translate of `V` by
the chosen representative `c.out`. These fibre points are `L`-points of `V.obj.left`
over the point `i`. A deck group `deck : Γ →* Aut V.obj.left` over `X` acts on it by
`cosetFiberAction`: `γ • ⟨c, p⟩ = ⟨c, fiber.map (deckTransport V (deck γ) _ c.out) p⟩`.

## Main theorem

`hasCoinducedGaloisFixedSections_smoothPointProduct L X h R G ρ M` proves
`HasCoinducedGaloisFixedSections L S` for
`S = (smoothPointProductFunctor ρ (etaleTopology X) (distinguishedLiftSystem ρ)
(etaleGodementPoints L h) R).obj M` and every coefficient family `M`. It assumes a
pointwise right Kan extension instance, `Small G` and the admissible-refinement
instance. Given a datum `(V, Γ, deck, l, Kₒ)`, the proof goes as follows.

1. The sections of `S` over `V` are the locally discrete sections of the raw induction
   `(ι etale ρ).op.ran.obj F₀` of the point product `F₀`. The map
   `f₁ : liftFixedSubmodule S V l Kₒ hK → fixedSubmodule ρ F₀ (liftAction l) Kₒ`,
   which forgets local discreteness, is bijective. It is injective because both are
   subtypes of the raw sections. It is surjective because `Kₒ`-fixed raw sections are
   locally discrete, by `fixedSubmodule_le_smoothSubmodule`. That lemma applies since
   `V` is distinguished and `liftAction l` is admissible for the distinguished lift
   system.
2. `pointProductFixedCoordinates` (with `IsLift (liftAction l)`) identifies the fixed
   sections with families `∀ c i, fibre_{c,i} → M i`.
3. The deck group acts freely on each `CosetFiber`. If `γ` fixes `⟨c, p⟩`, then
   `deck γ` fixes the `L`-point `p.down.1` of `V.obj.left`, so `γ = 1` by the
   freeness hypothesis of the datum.
4. Let `Q i` be the orbit set of `CosetFiber L h V Kₒ i`. It is `Small` because `G` is,
   so the module `A = ∀ i, Shrink (Q i) → M i` lies in `ModuleCat R`. The map `π` sends
   a section to its point coordinates at the chosen orbit representatives. By
   `sectionCoordinates_projection_deck`, `s ↦ (γ ↦ π (γ s))` equals the composite of
   `f₁`, the fixed coordinates and the coinduction map. That composite is bijective by
   `sigmaReindex_bijective` and `coinduced_pi_bijective`.

The commutation of the lift with the deck group is not needed here. It is a
hypothesis of the datum, used only by the analytic input.

## The reduction

`analyticEtaleSmoothPointProductLocalAcyclicCorrected_of_galoisCoinduced` assumes
`[IsTopologicalGroup G]`, `[Small.{max u (v + 1) uL} G]` and the
`HasAdmissibleRefinements` instance, together with
`AnalyticEtaleGaloisCoinducedLocalAcyclicStatement L X R G ρ`, and proves
`AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement L X h R G ρ`
(module `Langlands.Cohomology.AnalyticEtaleSmoothPointProductLocalAcyclicCorrected`).
Both statements bind the same three instance hypotheses on the definition itself.
The older `AnalyticEtaleSmoothPointProductLocalAcyclicStatement` lacks the
topological-group hypothesis by oversight and is not used here. Given Hausdorffness,
surjectivity of `pointProjection` (unused), continuity of the action, a coefficient
diagram `N` (injectivity unused) and `q`, it applies the hypothesis to the smooth point
product of `(piEquivalenceFunctorDiscrete _ _).inverse.obj N`. Its restriction to the
ordinary étale site is, by definition,
`(etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R).obj N`. The coinduced
hypothesis holds by the main theorem.
