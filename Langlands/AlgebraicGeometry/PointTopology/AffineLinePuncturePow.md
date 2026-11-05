# The `n`th-power morphism of the punctured affine line

Author: Worker 105.

This module defines the actual morphism `t ↦ t ^ n` of the punctured affine line
`G_m = Spec R[t, t⁻¹]` over `Spec R`. It also proves that, on points with values
in a topological ring `S`, this morphism is the `n`th-power map of units. It
supports Conrad's example on printed p.11 of *Weil and Grothendieck approaches to
adelic points* (registered source `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`):
"the `n`th-power map `G_m → G_m` for `n > 1` not divisible by `char(F)` is a finite
étale map that induces the `n`th-power map `A_F^× → A_F^×`". The module makes no
claim about adelic images and does not prove that the map is finite étale.

## Definitions

Let `R : Type u` be a commutative ring and `n : ℕ`.

- `affineLinePowAlgHom R n : R[t] →ₐ[R] R[t]` is `MvPolynomial.aeval` sending the
  coordinate `t = MvPolynomial.X ()` to `t ^ n`.
- `punctureAwayPowAlgHom R n` is the induced `R`-algebra endomorphism of
  `R[t, t⁻¹] = Localization.Away t`. It is the localization lift
  (`IsLocalization.liftAlgHom`) of `R[t] → R[t, t⁻¹]`, `t ↦ t ^ n`. The lift exists
  because the image `t ^ n` of `t` is a unit. `punctureAwayPowAlgHom_comp` says that
  it extends `affineLinePowAlgHom R n` along `R[t] → R[t, t⁻¹]`.
- `affineLinePuncturePow R n : affineLinePuncture R ⟶ affineLinePuncture R` is the
  morphism over `Spec R`. It is the morphism of spectra of `punctureAwayPowAlgHom R n`,
  transported along the published isomorphism
  `affineLinePunctureIsoAway R : affineLinePuncture R ≅ ringTest R (Localization.Away t)`.
  Here `affineLinePuncture R` is the published open subscheme `D(t)` of the affine
  line.

## Properties

- `affineLinePuncturePow_ι`: followed by the open inclusion
  `affineLinePunctureι R` into the affine line, the power morphism equals the
  inclusion followed by the morphism of spectra of `affineLinePowAlgHom R n`. So it
  restricts the map `t ↦ t ^ n` of the affine line.
- `affineLinePunctureUnitHomeomorph_pow`: for a commutative topological ring `S`
  that is an `R`-algebra and a point `p` of the punctured line with values in `S`,
  `affineLinePunctureUnitHomeomorph R S (p ≫ affineLinePuncturePow R n)` is the
  `n`th power of `affineLinePunctureUnitHomeomorph R S p`. Here
  `affineLinePunctureUnitHomeomorph` is the published homeomorphism from these points
  to `Sˣ` with Mathlib's units topology. The proof compares coordinates: the
  coordinate of the composite is the image of `t ^ n` under the point, which is the
  `n`th power of the coordinate of `p`.

## Provenance

The morphism is Conrad's `n`th-power map of `G_m`. The construction through the
localization lift and the published isomorphism, the names and the comparison lemma
are derived here.
