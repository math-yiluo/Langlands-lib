# Descent of a quasi-affine scheme along a flat surjection of affine schemes

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.QuasiAffine`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent`.

This is a helper module for the proof of Step 2b of Murre's induction
(`MurreCompletionDescentProof.md`). It proves effectivity of descent data on
quasi-affine schemes along a flat surjective morphism of affine schemes. This is the
fpqc analogue of the descent step in the published module
`Descent.LocallyQuasiFiniteDescent.Core`, and it reuses that module's ring-theoretic
input. It contains no definitions or statements that are meant to match the
literature. Everything here is internal to the proof.

## Declarations

- `exists_of_isPullback`: in a pullback square `P → X, P → Y` over `X → Z ← Y`, two
  points `x`, `y` with the same image in `Z` come from one point of `P`. The proof
  combines Mathlib's `Scheme.Pullback.exists_preimage_pullback` with the comparison
  isomorphism `IsPullback.isoPullback`.
- For `π : Z' ⟶ Z` and `g : W ⟶ Z'`, write `K := W ×_Z Z'`, the pullback of `g ≫ π`
  and `π`, and `K₂ := K ×_Z Z'`, the pullback of `pullback.snd ≫ π` and `π`. Two maps
  `K₂ ⟶ K` are defined, each as a `pullback.lift`:
  - `firstLift π g`: `(w, z₁, z₂) ↦ (w, z₂)`, i.e. `fst ≫ fst` paired with `snd`.
    Its well-definedness is `firstLift_w`.
  - `secondLift π g σ hσ` (for `σ : K ⟶ W` with `σ ≫ g = snd`): `(w, z₁, z₂) ↦ (σ(w, z₁), z₂)`,
    i.e. `fst ≫ σ` paired with `snd`. Its well-definedness is `secondLift_w`.

  `firstLift_fst`, `firstLift_snd`, `secondLift_fst`, `secondLift_snd` (all
  `@[reassoc]`) record their composites with the two projections of `K`.
- `exists_isPullback_of_isQuasiAffine`: let `Z` and `Z'` be affine, `π` flat and
  surjective, `W` quasi-affine. Let `σ : W ×_Z Z' ⟶ W` satisfy `σ ≫ g = snd`, have the
  graph `pullback.lift (𝟙 W) g` as a section (`hsec`), and satisfy the cocycle
  identity `firstLift ≫ σ = secondLift ≫ σ` (`hcoc`). Then there are a scheme `V`,
  `w : V ⟶ Z` and `p : W ⟶ V` such that `IsPullback p g w π` holds and
  `fst ≫ p = σ ≫ p`. That is, `W` is the base change of `V` along `π`, and `p`
  coequalizes the two maps `W ×_Z Z' ⟶ W`.

## Proof of `exists_isPullback_of_isQuasiAffine`

1. The first projection `K ⟶ W` is a base change of `π`, which is affine because `Z`
   and `Z'` are affine. So it is an affine morphism, and `K` is quasi-affine
   (`Scheme.IsQuasiAffine.of_isAffineHom`).
2. Global sections. For the square `K = W ×_Z Z'` and the square
   `K₂ = K ×_Z Z'`, the published
   `LocallyQuasiFiniteDescent.isPushout_appTop_of_isPullback` gives pushout squares
   of rings: flat base change of global sections for qcqs sources over an affine
   base. The section `hsec` makes `σ.appTop` injective, and `σ ≫ g = snd` gives
   `g.appTop ≫ σ.appTop = snd.appTop`.
3. The published `LocallyQuasiFiniteDescent.exists_isPushout_eqLocus`, applied with
   `r = π.appTop` (flat by `Scheme.Hom.flat_appTop`), `a = g.appTop`,
   `i₁ = fst.appTop` and `i₂ = σ.appTop`, gives a ring `B` (the equalizer of `i₁` and
   `i₂`) with maps `rB : Γ(Z) ⟶ B` and `ιB : B ⟶ Γ(W)` such that `Γ(W) = B ⊗_{Γ(Z)} Γ(Z')`
   (a pushout square) and `ιB ≫ i₁ = ιB ≫ i₂`. Its compatibility hypotheses are
   the composites of `firstLift`/`secondLift` with the projections, and the cocycle
   identity `hcoc` on global sections.
4. Taking spectra (`isPullback_SpecMap_of_isPushout`) gives a pullback square with
   `Spec Γ(W) ⟶ Spec B` a base change of `Spec Γ(Z') ⟶ Spec Γ(Z)`. The latter is
   identified with `π` through the isomorphisms `isoSpec`, so it is flat and
   surjective. Hence `Spec ιB` is flat and surjective, and therefore a quotient map
   (`Flat.isQuotientMap_of_surjective`).
5. `Γ(K) = Γ(W) ⊗_B Γ(W)` with the two maps `fst.appTop` and `σ.appTop`. This is
   `IsPushout.of_left` from the pushouts in steps 2 and 3. So `Spec Γ(K)` is the fibre
   product `Spec Γ(W) ×_{Spec B} Spec Γ(W)`.
6. Let `ω := W.toSpecΓ ≫ Spec ιB : W ⟶ Spec B`. The preimage of `range ω` under
   `Spec ιB` is exactly `range W.toSpecΓ`. If `Spec ιB y = ω x`, then step 5 and
   `exists_of_isPullback` give a point `δ` of `Spec Γ(K)` over `(toSpecΓ x, y)`.
   Mathlib's `Scheme.isPullback_toSpecΓ_toSpecΓ` for the affine morphism `fst`
   lifts `δ` to a point `d` of `K`, and `σ d` maps to `y`. Since `W.toSpecΓ` is an
   open embedding (`W` quasi-affine) and `Spec ιB` is a quotient map, `range ω` is
   open.
7. Let `V` be the open subscheme `range ω` of `Spec B` and `p : W ⟶ V` the lift of
   `ω`. By step 6, `IsOpenImmersion.isPullback` shows that `W` is the preimage of `V`
   under `Spec ιB`. Pasting with step 4 and composing with `Z.isoSpec`,
   `Z'.isoSpec` gives `IsPullback p g w π` for `w := V.ι ≫ Spec rB ≫ Z.isoSpec.inv`.
8. `fst ≫ p = σ ≫ p` can be checked after the monomorphism `V.ι`. It follows from
   `toSpecΓ` naturality and `ιB ≫ fst.appTop = ιB ≫ σ.appTop`.
