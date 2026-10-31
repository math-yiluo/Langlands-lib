# Canonical scalar cohomology base change from actual Čech resolutions

This internal construction assembles the actual Čech comparison with the
published canonical scalar cohomology map. All schemes and rings lie in
an arbitrary common universe `u`. Let `φ : R ⟶ S`, and let
`g : Y ⟶ X`, `f : X ⟶ Spec R`, and `f' : Y ⟶ Spec S` form the
specified Cartesian square. Assume that `g` is affine, `f` is separated,
`φ` is flat, and `M` is quasi-coherent. Fix an ordered affine cover `𝒰`
of `X`.

`isIso_scalarBaseChangeMap_of_cech` proves invertibility of the
specified canonical `scalarBaseChangeMap φ f f' g w M hM n` in
every degree `n : ℕ`, under three explicit acyclicity inputs:

- Every term of `cechComplex 𝒰 M` has zero positive cohomology for `f`.
- Every term of the Čech complex of `g^* M` on the full inverse-image
  cover has zero positive cohomology for `f'`.
- The positive higher direct images under `g` of `g^* M` vanish.

The proof uses the actual augmentations `cechAug` and the actual
pullback-unit map `cechPullback`. Both augmentations are
quasi-isomorphisms by `quasiIso_cechAug`. The pushed target augmentation
is a quasi-isomorphism by `quasiIso_pushforward_cechAug`, which requires
no acyclicity premise. The exact compatibility square is
`cechAug_cechPullback`. For the Cartesian square and separated source,
`quasiIso_scalarCechSectionsMap_of_isPullback_of_isSeparated` proves that
the actual scalar sections cochain map is a quasi-isomorphism: its
intersection-factor maps are precisely the canonical affine sections
maps. These results supply the resolution and map hypotheses of
`isIso_scalarBaseChangeMap_of_acyclicResolutions`. That published
comparison identifies the cohomology of the actual scalar cochain map
with the stated canonical scalar base-change map.

`scalarCechCohomologyBaseChangeIso` packages this result as an actual
isomorphism from scalar-extended source cohomology to target cohomology.
Its forward map is exactly the specified `scalarBaseChangeMap`, and the
inverse is supplied by the proved invertibility above. Its hypotheses
are the same Cartesian square, flatness, and three acyclicity inputs.

This is an internal consequence of these constructions, with no
separate literature assertion. The two term-acyclicity inputs and the
higher-direct-image input remain hypotheses; this file does
not claim to prove them, unrestricted flat base change, or the relative
cube theorem.
