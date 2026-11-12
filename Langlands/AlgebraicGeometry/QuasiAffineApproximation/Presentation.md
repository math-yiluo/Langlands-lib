# A presentation of a finite surjective quasi-affine cover (Part I)

Module `Langlands.AlgebraicGeometry.QuasiAffineApproximation.Presentation`.

This is Part I of the proof of `QuasiAffineSourceAFNoetherianSchemeApproximationStatement`.
It proves `presentationInterface : PresentationInterface.{u}`. The proposition
`PresentationInterface` is defined in `QuasiAffineApproximation.Skeleton`. The module is
internal to that proof and has no separate literature source. It is the first move of
Gross, Proposition 3.5, Step 3: replace the algebraic space `Y` and its finite cover
`f : U ⟶ Y` by étale equivalence relations of schemes, which can then be approximated.

## Declarations

- `isSurjective_map`. If `j : U ⟶ V` is a morphism over `S` with `j.left` surjective, then
  the map of represented presheaves `(schemeYoneda S).map j` is surjective in the sense of
  `AlgebraicSpace.IsSurjective`.
- `isSurjective_comp`. Surjective maps of presheaves over `S` are closed under composition.
- `exists_affine_atlas_of_isQuasiCompact`. A quasi-compact algebraic space `Y` over `S` has an
  étale surjective map `a₀ : U₀ ⟶ Y` from an affine scheme `U₀` over `S`.
- `presentationInterface`. Let `R` be a commutative ring and `U` a scheme over `Spec R`. Let
  `f : U ⟶ Y` be a finite surjective map to a quasi-compact quasi-separated algebraic space
  over `Spec R`, with `U` quasi-affine. Then there are étale equivalence relations `E` and
  `E'`, a cartesian morphism `(φ, g) : E' ⟶ E` and a morphism `q : E'.U ⟶ U` with:
  - `E.U` affine, and `φ` finite and surjective;
  - `(E'.t, E'.s)` the kernel pair of `q` (`IsPullback E'.t E'.s q q`);
  - `q` flat, locally of finite presentation and surjective;
  - any two points `w, w'` of `U` with the same image in `Y` (`SameImage (hom f) w w'`) lift
    to points `ω, ω'` of `E'.U` with `q ω = w`, `q ω' = w'` and `φ ω = φ ω'`.

  The proof uses neither the quasi-separatedness of `Y` nor the quasi-affineness of `U`.
  They are hypotheses of `PresentationInterface` only so that it matches the target.

## Proof

1. *Affine atlas.* Quasi-compactness of `Y` gives an étale surjective map `a : W ⟶ Y` from a
   quasi-compact scheme `W`. Étale morphisms are Zariski-local at the source, so Mathlib's
   `Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource` gives an étale surjective
   `j : V ⟶ W` with `V` affine. Then `a₀ := j ≫ a` is étale (`IsEtale.comp`) and surjective
   (`isSurjective_comp`, `isSurjective_map`).
2. *The relation `E`.* The kernel pair of the étale map `a₀` is represented with étale
   projections `t, s : Rel ⟶ U₀` (`exists_kernelPair`). Let
   `E := ofKernelPair t s a₀`.
3. *The cover.* Because `a₀` is representable, the fibre product `U₀ ×_Y U` is a scheme over
   `S`. Its two projections are `φ : U₀ ×_Y U ⟶ U₀` and `q : U₀ ×_Y U ⟶ U`. Base change gives:
   `q` is étale and surjective (from `a₀`), and `φ` is finite and surjective (from `f`). Let
   `E'` be the relation of the kernel pair `pullback q q` of `q`, using `ofKernelPair` with the
   étale projections. Its relation square, mapped to schemes, is `IsPullback E'.t E'.s q q`.
   Étale implies flat and locally of finite presentation.
4. *The map `g`.* The two composites `pullback.fst q q ≫ φ` and `pullback.snd q q ≫ φ` agree
   after composing with `a₀`. So they lift to `g : pullback q q ⟶ Rel` with `g ≫ t` and
   `g ≫ s` the two composites (`exists_lift_of_isPullback`).
5. *Cartesian.* The first condition of `IsCartesianHom` is `g ≫ t = E'.t ≫ φ`, which holds by
   construction. For the second, paste the kernel-pair square of `q` with the fibre-product
   square of `U₀ ×_Y U`. The pasted rectangle and the kernel-pair square of `a₀` give, by
   pullback cancellation, the square `g, E'.s, s, φ`. That square is a pullback of represented
   presheaves, hence of schemes over `S` (`isPullback_of_map`), hence of schemes.
6. *Lifting points with the same image.* Suppose `w = g₁ t₀` and `w' = g₂ t₀` for
   `g₁, g₂ : T ⟶ U` that agree after composing with `f`. Pull back the atlas `a₀` along
   `g₁ ≫ f`. This gives a scheme `T'` with a surjective map to `T`, a point `t₁` over `t₀`, and
   a map `ψ : T' ⟶ U₀`. The pairs `(ψ, T' ⟶ T ⟶ U)` through `g₁` and `g₂` both lift to
   `U₀ ×_Y U`, giving `ω₁, ω₂ : T' ⟶ U₀ ×_Y U` with `ω₁ ≫ φ = ψ = ω₂ ≫ φ`. The points
   `ω₁ t₁` and `ω₂ t₁` have the required images under `q` and `φ`.
