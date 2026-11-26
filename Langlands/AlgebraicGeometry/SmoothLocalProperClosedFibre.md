# Properness of a smooth local family from its proper closed fibre

The module `Langlands.AlgebraicGeometry.SmoothLocalProperClosedFibre` proves
`Langlands.AlgebraicGeometry.isProper_of_smooth_of_proper_closedFibre`. Let
`R` be a noetherian, integrally closed local domain and `p : X ⟶ Spec R` a
smooth, separated, quasi-compact morphism with geometrically connected fibres.
If the actual pullback of `p` along `Spec` of the residue map
`R → IsLocalRing.ResidueField R` is proper, then `p` is proper. A discrete
valuation ring satisfies these hypotheses on `R`.

## Proof

1. Integrality. A smooth morphism with geometrically connected fibres has
   geometrically integral fibres
   (`geometricallyIntegral_of_smooth_geometricallyConnected`). Mathlib's
   `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` then makes `X`
   integral, and `X` is quasi-compact.

2. Chow envelope. The chart data `ChartData` from the proof of Chow's lemma
   `AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral`
   (module
   `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral`)
   give a nonempty open `Uo` of `X`. They also give the scheme-theoretic closure
   `X'` of a graph of `Uo` in `X` times a product of projective spaces over `R`,
   with a proper surjection `π : X' ⟶ X`. Let `P` be the scheme-theoretic image
   of `X'` in the product of projective spaces, with its proper structure
   morphism `q : P ⟶ Spec R`. The induced `a : X' ⟶ P` is an open immersion
   with `a ≫ q = π ≫ p`. The composite `d : Uo ⟶ X' ⟶ P` is quasi-compact and
   scheme-theoretically dominant, and `P` is integral
   (`isIntegral_schematicImage`). Geometrically connected fibres are nonempty,
   so `p` and `π ≫ p` are surjective, hence so are `a ≫ q` and `q`.

3. Generic fibre of the envelope. Let `K` be the fraction field of `R`. Take a
   field `L` and a morphism `Spec L ⟶ Spec K`. The base change of `d` to `L`
   is still scheme-theoretically dominant, since the base change is flat. Its
   source is a nonempty open of the integral scheme `X_L`, so it is integral.
   Therefore `P_L` is reduced and irreducible, hence integral, and the generic
   fibre of `q` is geometrically integral.

4. Global functions. The private lemma
   `bijective_appTop_of_geometricallyIntegral_generic` shows that `q.appTop` is
   bijective. The generic point of `P` lies over the generic point of `Spec R`,
   so the generic fibre inclusion is dominant and therefore
   scheme-theoretically dominant. Global functions on `P` thus inject into
   those of the generic fibre. The latter are `K`, by
   `bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected`
   applied to the proper, geometrically integral generic fibre. Global
   functions of the proper `P` are integral over `R`
   (`isIntegral_appTop_of_universallyClosed`), and integral closedness of `R`
   gives the bijection.

5. Connected closed fibre. By
   `isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop`, the
   closed fibre of `q` is preconnected.

6. Filling the envelope. Let `s` be the closed point of `Spec R` and `κ(s)`
   its residue field `IsLocalRing.ResidueField R`. The closed fibre of a
   morphism `Y ⟶ Spec R` is its actual pullback along
   `Spec κ(s) ⟶ Spec R`, with structure map to `Spec κ(s)`.

   First, the closed fibre `X'_s` of `π ≫ p` is proper over `κ(s)`. Regard
   `π` as a morphism over `Spec R` from `π ≫ p` to `p`. Its base change along
   `Spec κ(s) ⟶ Spec R` is a morphism `π_s : X'_s ⟶ X_s`, which is proper
   because `π` is proper (`MorphismProperty.overPullbackMap`). The structure
   map `X'_s ⟶ Spec κ(s)` is `π_s` followed by the given proper structure map
   `X_s ⟶ Spec κ(s)`, so it is proper by composition. Since
   `a ≫ q = π ≫ p`, the closed fibre of `a ≫ q` is proper over `κ(s)`.

   The private lemma `proper_open_of_connected_closedFibre` finishes the
   step. Let `e : X'_s ⟶ P` be the first projection `X'_s ⟶ X'` followed by
   `a`. Then `e ≫ q` is the structure map of `X'_s` followed by the closed
   immersion `Spec κ(s) ⟶ Spec R`, hence proper, and since `q` is separated,
   `e` is proper. Its image is closed and lies in the open `a(X')`. Every
   point of `X'` over the closed point maps into the image of `e`. So
   the closed fibre of `q` lies in the union of two closed sets, the image of
   `e` and the complement of `a(X')`, and no point of the fibre lies in both.
   Surjectivity of `a ≫ q` puts a point of `a(X')` in the fibre. Since the
   fibre is preconnected, it lies in the image of `e`, hence in `a(X')`. An
   open of `P` containing the closed fibre of the universally closed `q` is all
   of `P` (`open_eq_top_of_contains_closedFibre`). So the open immersion `a`
   is surjective, hence an isomorphism, and `a ≫ q` is proper.

7. Descent. Then `π ≫ p` is universally closed, and universal closedness
   descends along the surjection `π`
   (`UniversallyClosed.of_comp_surjective`). In Mathlib, `IsProper` means
   separated, universally closed and locally of finite type. The morphism `p`
   is separated by hypothesis and locally of finite type because it is
   smooth, so `p` is proper.

## Provenance

This is the case of a smooth morphism to the spectrum of a noetherian normal
local domain in Grothendieck and Dieudonné, *Éléments de géométrie algébrique
IV*, third part (1966), Corollary 15.7.10, printed p. 247. That corollary
assumes a separated, finite-type, universally submersive morphism to a
locally noetherian scheme with geometrically connected fibres. Here `p` is of
finite type because it is smooth, hence locally of finite type, and
quasi-compact. Smoothness gives universal openness and the nonempty fibres
give surjectivity, so `p` is universally submersive. EGA
deduces the corollary from Proposition 15.7.9. The Lean proof instead uses
the Chow envelope, normality of the base and the connectedness of the closed
fibre of a proper scheme with constant global functions.
