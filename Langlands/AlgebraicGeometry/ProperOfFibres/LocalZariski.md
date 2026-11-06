# Properness over a noetherian local normal domain from an open embedding into a proper scheme

Module `Langlands.AlgebraicGeometry.ProperOfFibres.LocalZariski`, namespace
`Langlands.AlgebraicGeometry.ProperOfFibres`.

This module is a local step of the general properness criterion used for relative parabolic
quotients. It is the classical *Zariski connectedness* argument: over a noetherian local normal
domain, a flat scheme that is open in a proper scheme, whose generic fibre has only constant
global functions and whose closed fibre is proper and nonempty, is already closed in the proper
scheme, hence proper.

## Main statement

`isProper_of_isOpenImmersion`. Let `B` be a noetherian local ring which is an integrally closed
domain (`[IsLocalRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]`), let `K` be a
fraction field of `B` (`[IsFractionRing B K]`), and write `k = IsLocalRing.ResidueField B` and
`ψ : Spec k ⟶ Spec B` for the closed point (`Spec.map` of `IsLocalRing.residue B`). Let

* `f : X ⟶ Spec B` be flat and quasi-compact;
* `ι : X ⟶ W` be an open immersion and `g : W ⟶ Spec B` be proper, with `ι ≫ g = f`;
* the global sections map of the generic fibre,
  `(pullback.snd f (Spec.map (algebraMap B K))).appTop`, be bijective (that is, the generic
  fibre `X_K` has global sections exactly `K`);
* the closed fibre `pullback.snd f ψ : X_k ⟶ Spec k` be proper, and `X_k` be nonempty.

Then `f` is proper.

All schemes and rings live in one arbitrary universe `u`. No further hypotheses (such as
finite type of `X`, separatedness of `X`, or connectedness of the fibres) are assumed; they
follow from the conclusion.

## Helper lemmas

* `SpecMap_appTop_injective`: for an injective ring map `ψ : R →+* S`, the global sections map
  of `Spec.map ψ` is injective (via `Scheme.ΓSpecIso_naturality`).
* `range_SpecMap_residue`: the image of `Spec k ⟶ Spec B` is the closed point.
* `bot_mem_range_SpecMap_algebraMap`: the generic point `(⊥ : PrimeSpectrum B)` lies in the image
  of `Spec K ⟶ Spec B`.
* `closedPoint_mem_of_isClosed`: a nonempty closed subset of `Spec B` contains the closed point
  (every point specializes to it).

## Proof as implemented

1. **Closure of the generic fibre.** Let `h : X_K ⟶ W` be the projection `X_K ⟶ X` followed by
   `ι`. It is quasi-compact (its composite with `g` equals `X_K ⟶ Spec K ⟶ Spec B`, which is
   quasi-compact). Let `Z = h.image` be its scheme-theoretic image, with closed immersion
   `i = h.imageι : Z ⟶ W`, and put `q = i ≫ g : Z ⟶ Spec B`, which is proper.
2. **Global sections of `Z` are `B`.** The map `h.toImage : X_K ⟶ Z` is injective on stalks
   (Mathlib `Scheme.Hom.stalkFunctor_toImage_injective`), hence injective on global sections
   (`TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective`). Composing with the inverse of
   the bijection `Γ(Spec K) ≅ Γ(X_K)` and `Γ(Spec K) ≅ K` gives an injective ring map
   `τ : Γ(Z) →+* K` with `τ ∘ q.appTop = algebraMap B K` (up to `Γ(Spec B) ≅ B`). Hence `q.appTop`
   is injective. It is surjective because `q.appTop` is integral (Mathlib
   `isIntegral_appTop_of_universallyClosed`), so every `τ z` is integral over `B`, hence lies in
   `B` because `B` is integrally closed; injectivity of `τ` then identifies `z` with an element of
   `B`. So `q.appTop` is bijective.
3. **Zariski connectedness.** By the FLT port
   `AlgebraicGeometry.isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop`
   (a proper morphism over a noetherian local ring with bijective global sections map has
   preconnected closed fibre), the closed fibre `F = q⁻¹{s}` of `Z` is preconnected, where `s`
   is the closed point of `Spec B`.
4. **`X` lies in `Z`.** The range of `i` is the closure of the range of `h` (scheme-theoretic
   image support). For `x ∈ X`, the generic point of `Spec B` specializes to `f x`; flatness of
   `f` (generalizing map, `Flat.generalizingMap`) gives `x' ⤳ x` with `x'` over the generic
   point, so `x'` comes from `X_K` (`Scheme.Pullback.range_fst`), and `ι x` lies in the closure of
   the range of `h`. Hence `range ι ⊆ range i`.
5. **The closed fibre of `X` is closed in `W`.** The map `e : X_k ⟶ X ⟶ W` is proper, since
   `e ≫ g = (X_k ⟶ Spec k) ≫ ψ` is proper (`ψ` is a closed immersion) and `g` is separated
   (`IsProper.of_comp`). So `E = range e` is closed in `W`; it is contained in `range ι` and
   contains `ι x` for every `x` with `f x = s`.
6. **Clopen splitting.** The sets `i⁻¹ E` and `(i⁻¹ range ι)ᶜ` are closed in `Z`, cover `F`
   (a point of `F` in `range ι` lies over `s`, hence in `E`), and are disjoint on `F`. By
   preconnectedness (`isPreconnected_iff_subset_of_disjoint_closed`), `F` lies in one of them. It
   cannot lie in the second: a point `w` of the nonempty `X_k` gives a point of `X` over `s`, which
   by step 4 is `i z` for some `z ∈ F` with `i z ∈ range ι`. Hence every point of `F` maps into
   `range ι`.
7. **All of `Z` lies in `X`.** If some `i z ∉ range ι`, the set `q((i⁻¹ range ι)ᶜ)` is closed
   (`q` is a closed map) and nonempty, so it contains the closed point `s`; a point `z'` with
   `i z' ∉ range ι` and `q z' = s` contradicts step 6.
8. **Conclusion.** Steps 4 and 7 give `range ι = range i`, which is closed. An open immersion with
   closed range is a closed immersion (`IsClosedImmersion.of_isPreimmersion`), so `f = ι ≫ g` is a
   composite of a closed immersion and a proper morphism, hence proper.

## Provenance

Internal. The statement is the special case, needed for the relative parabolic quotient
properness argument, of the standard argument behind Zariski's connectedness theorem. It plays
the role that the idempotent-lifting argument with the theorem on formal functions plays in
Conrad, *Reductive group schemes* (2014), proof of Theorem 2.3.6(2) (pp. 74–75), for a scheme
open in a proper scheme over a local base. The proof above is a direct assembly of Mathlib
results and the published FLT port
`AlgebraicGeometry.isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop`; no
source assertion is assumed.
