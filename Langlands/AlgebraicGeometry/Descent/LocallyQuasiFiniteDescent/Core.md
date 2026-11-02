# Descent of a quasi-affine fppf base change over an affine scheme

Module `Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Core`, namespace
`Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent`. This is a helper for the proof of
`Langlands.AlgebraicGeometry.FppfSeparatedLocallyQuasiFiniteDescentStatement` (Stacks Tag 02W8 in
sheaf form). The Stacks proof of 02W8 (Lemma 37.57.1) reduces to a quasi-affine piece over an
affine fppf chart. It then descends that piece by Descent, Lemma 35.38.1: descent data for
quasi-affine morphisms are effective. The main theorem here plays that role in sheaf form. It
is internal, and its proof is not the Stacks proof: there is no descent-data formalism and
no descent of quasi-coherent algebras. Instead the global functions are descended directly, and
the Library's "same kernel" criterion finishes the argument.

## Statements

- `isPullback_of_comp_mono`: a pullback square over `f ≫ ι` and `g ≫ ι`, with `ι` monic, is a
  pullback square over `f` and `g`.
- `isPullback_left_of_factor`: for `f : X ⟶ T` and `g : V ⟶ T` in `Over S` whose underlying
  maps factor through a monomorphism `ι : D ⟶ T.left` as `f'` and `g'`, the underlying
  square of schemes of `pullback f g` is a pullback square over `f'` and `g'`.
- `appLE_top_top`: `f.appLE ⊤ ⊤ e = f.appTop`.
- `isPushout_appTop_of_isPullback`: flat base change of global sections. Take a pullback square
  of schemes `P = X ×_Z Y` with `Z` and `Y` affine, `Y ⟶ Z` flat, and `X` quasi-compact and
  quasi-separated. Then the global-section rings form a pushout square. This specializes
  Mathlib's `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` to the top opens.
- `appTop_comp_eq`: a commutative square in `Over S` gives a commutative square of
  global-section maps.
- `exists_iso_of_quasiAffine` (core descent step). The setting:
  - `F` is an fppf sheaf on `Over S` and `p : F ⟶ h T`, where `h` is `schemeYoneda S`;
  - `c : h W ⟶ F` and `w : W ⟶ V` form a pullback square of `p` along `h g`, with
    `g : V ⟶ T`;
  - `c` is fppf locally surjective;
  - `g.left = g' ≫ ι` for a monomorphism `ι : D ⟶ T.left` from an affine scheme `D`, and
    `g' : V.left ⟶ D` is flat and locally of finite presentation;
  - `V.left` is affine and `W.left` is quasi-affine.

  Then there are `Y : Over S`, `q : W ⟶ Y` and an isomorphism `e : h Y ≅ F` with
  `h q ≫ e.hom = c`. So `F` is representable, and `c` comes from a morphism of schemes.

## Proof of `exists_iso_of_quasiAffine`

Write `K = W ×_T V` and `P = K ×_T V`. Since `ι` is monic, these are also fibre products over
`D` (`isPullback_left_of_factor`). `K ⟶ W` is a base change of the affine morphism `g'`, so
`K` is quasi-affine (`Scheme.IsQuasiAffine.of_isAffineHom`). Flat base change of global sections
(`isPushout_appTop_of_isPullback`) gives two pushout squares of rings:
- `Γ(K) = Γ(W) ⊗_{Γ(D)} Γ(V)`;
- `Γ(P) = Γ(K) ⊗_{Γ(D)} Γ(V)`.

The module `Transport` gives `secondMap : K ⟶ W`, with the diagonal `W ⟶ K` as a section
(`diag_secondMap`). So `secondMap` is injective on global sections. It also gives `firstLift`
and `secondLift : P ⟶ K` with the cocycle identity `firstLift_secondMap`. These are the
hypotheses of `exists_isPushout_eqLocus` (module `EqLocusPushout`), for the flat map
`Γ(D) → Γ(V)` (`Scheme.Hom.flat_appTop`). It gives a ring `B` with `Γ(D) → B → Γ(W)`. The ring
`B` equalizes the two maps `Γ(W) → Γ(K)`, and `Γ(W) = B ⊗_{Γ(D)} Γ(V)`.

Taking spectra (`isPullback_SpecMap_of_isPushout`), `Spec Γ(W) ⟶ Spec B` is a base change of
`Spec Γ(V) ⟶ Spec Γ(D)`, which is flat and locally of finite presentation. Hence so is
`ω : W ⟶ Spec Γ(W) ⟶ Spec B`; here `W ⟶ Spec Γ(W)` is the open immersion `toSpecΓ` of the
quasi-affine scheme `W`. Let `U ⊆ Spec B` be the image of `ω`. It is open because flat morphisms
locally of finite presentation are open maps. `ω` factors as a flat, locally finitely
presented, surjective morphism `q' : W ⟶ U`. The flatness and finite presentation of `q'`
follow by cancelling the monomorphism `U ⟶ Spec B`
(`IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms`). Set `Y = U`, over `T` by
`U ⟶ Spec B ⟶ Spec Γ(D) ≅ D ⟶ T`, and let `q : W ⟶ Y` be `q'`. Then:
- `q ≫ y = w ≫ g`;
- `q` identifies the two maps `K ⟶ W`, because `B` equalizes them on global sections;
- `q` and `w` are jointly monic, because `W ⟶ Spec Γ(W)` is monic and `Spec Γ(W)` is the
  fibre product `Spec B ×_{Spec Γ(D)} Spec Γ(V)`.

`app_eq_app_iff_comp_eq` then shows that `c` and `q` have the same kernel. `h q` is fppf
locally surjective because `q` is an fppf covering (`isLocallySurjective_schemeYoneda_map`). The
Library's `exists_iso_of_locallySurjective_of_same_kernel` produces `e`.
