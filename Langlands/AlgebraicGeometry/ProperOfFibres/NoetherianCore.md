# Properness over a localization of a normal finitely generated ℤ-domain

Module `Langlands.AlgebraicGeometry.ProperOfFibres.NoetherianCore`, namespace
`Langlands.AlgebraicGeometry.ProperOfFibres`. This is the noetherian core of the
properness criterion used for relative parabolic quotients. For comparison, Conrad,
*Reductive group schemes* (2014), proof of Theorem 2.3.6(2) (pp. 73–75), also works over a
noetherian base, but passes to a complete local base and lifts an idempotent by the theorem
on formal functions; the route below instead uses the relative normalization (Zariski's main
theorem) and the Zariski connectedness argument of module `LocalZariski`. The statements are
internal helpers; the proofs below are the implemented Lean proofs.

## Helper lemmas

- `bot_mem_range_SpecMap_of_injective`: for an injective ring map `φ : R →+* K` from a
  domain to a field, the zero ideal of `R` is the image of the unique point of `Spec K`.
  Proof: the point of `Spec K` is the zero ideal, whose preimage is `ker φ = ⊥`.
- `irreducibleSpace_of_flat`: let `f : X ⟶ Spec R` be flat with `R` a domain, and let
  `e : Z ⟶ X` be a morphism from an irreducible scheme whose image contains every point of
  `X` over the generic point. Then `X` is irreducible. Proof: by going down for flat
  morphisms (`Flat.generalizingMap`) every point of `X` specializes from a point over the
  generic point, so the irreducible set `range e` is dense, and its closure `X` is
  irreducible.
- `finiteType_int_of_locallyOfFiniteType`: if `R` is a finitely generated `ℤ`-algebra and
  `g : Y ⟶ Spec R` is locally of finite type, then `Γ(Y, U)` is a finitely generated
  `ℤ`-algebra for every affine open `U`. Proof: `Γ(Spec R, ⊤) ⟶ Γ(Y, U)` is of finite type
  (`HasRingHomProperty.appLE`), `Γ(Spec R, ⊤) ≅ R`, and the two maps from `ℤ` agree since
  ring maps out of `ℤ` are unique.

## Main theorem `isProper_pullback_snd_of_mono`

Hypotheses: `N` is a domain, integrally closed, and of finite type over `ℤ`; `p` is a prime
of `N`; `B` is a local ring with `IsLocalization.AtPrime B p`; `K` is a fraction field of
`B`. Let `f : X ⟶ Spec N` be smooth and quasi-compact, `g : Y ⟶ Spec N` proper, and
`j : X ⟶ Y` a monomorphism with `j ≫ g = f`. Write `X_B ⟶ Spec B` for the base change
`pullback.snd f (Spec.map (algebraMap N B))`. Assume its generic fibre (base change along
`Spec K ⟶ Spec B`) is proper and geometrically connected, and its closed fibre (base change
along `Spec` of the residue map of `B`) is proper and nonempty. Conclusion: `X_B ⟶ Spec B`
is proper.

Proof as implemented:

1. `N` is noetherian (`Algebra.FiniteType.isNoetherianRing`); `B` is a noetherian
   integrally closed local domain (localization of a noetherian normal domain at a prime).
2. `j` is locally of finite type and quasi-compact, since `j ≫ g = f` is, and `g` is
   separated.
3. `X` is integral. It is reduced because `f` is smooth, hence geometrically reduced
   (Library `SmoothReducedProof.geometricallyReduced_of_smooth`), and flat over the
   reduced noetherian scheme `Spec N`
   (`GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`). The generic fibre
   `X_K` is smooth and geometrically connected over `K`, hence geometrically integral
   (Library `geometricallyIntegral_of_smooth_geometricallyConnected`) and integral. The
   map `X_K ⟶ X_B ⟶ X` agrees, through `pullbackLeftPullbackSndIso`, with the projection
   `X ×_N K ⟶ X`, whose image is the fibre over the generic point of `N`, because
   `N ⟶ K` is injective. So `irreducibleSpace_of_flat` makes `X` irreducible.
4. By `isFinite_fromNormalization` (module `MonoNormalization`, with the hypothesis supplied by
   `finiteType_int_of_locallyOfFiniteType` for `g`), the relative normalization
   `W := j.normalization ⟶ Y` is finite, so `w : W ⟶ Spec N` is proper. Zariski's main
   theorem in Mathlib makes `ι := j.toNormalization` an open immersion, and
   `ι ≫ w = f`.
5. Base change to `B`: the comparison `ι_B : X_B ⟶ W_B` is obtained by
   `IsPullback.of_right'`; the square with `ι` is a pullback, so `ι_B` is an open
   immersion, and `ι_B ≫ (W_B ⟶ Spec B) = X_B ⟶ Spec B`.
6. The generic fibre `X_K` is smooth, proper and geometrically connected over the field
   `K`, so its global sections map is an isomorphism (Library
   `fieldSmoothProperConnectedGlobalFunctions`).
7. `isProper_of_isOpenImmersion` (module `LocalZariski`) applied to `X_B ⟶ Spec B`, the open immersion `ι_B`
   into the proper `W_B`, the bijectivity from step 6 and the closed-fibre hypotheses gives
   properness of `X_B ⟶ Spec B`.
