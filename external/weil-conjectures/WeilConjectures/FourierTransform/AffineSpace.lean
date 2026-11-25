/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.AffineSpace.KernelTransform
public import WeilConjectures.FourierTransform.AffineSpace.NegProd
public import WeilConjectures.FourierTransform.AffineSpace.Transform
public import WeilConjectures.FourierTransform.AffineSpace.Unit

/-!

# The Fourier–Deligne transform on affine space

This module only re-exports its parts, which live in
`WeilConjectures.FourierTransform.AffineSpace`; it was split to keep the compilation of each part
cheap.

The Fourier–Deligne transform of `WeilConjectures.FourierTransform.Defs` is stated for an
arbitrary pair of `S`-schemes with a pairing. Its main case is affine `n`-space `𝔸(n; S)`
paired with itself by the standard pairing `⟨x, ξ⟩ = ∑ᵢ xᵢ ξᵢ` and shifted by the relative
dimension `r = #n`; this module records that datum and the computation of the transform of
the two simplest complexes, the constant sheaf and the skyscraper at the origin.

The affine-space data themselves — the standard pairing, the zero section and the
reflection `x ↦ -x` — are in
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`; they have nothing to do with étale
sheaves.

## Main definitions

- `AlgebraicGeometry.Etale.affineFourierTransform`: the Fourier–Deligne transform of
  `𝔸(n; S)` with the standard pairing.
- `AlgebraicGeometry.Etale.skyscraperZero`: the skyscraper `δ₀` at the origin.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit` and
  `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_skyscraperZero`: the transform
  exchanges the constant sheaf and the skyscraper at the origin.
- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_inv`: the transform for the
  inverse character is the transform of the reflected input.

## Coefficients

Coefficient hypotheses follow the classes in `WeilConjectures.FourierTransform.Defs`.

## Implementation notes

The statements only assert that an isomorphism *exists*. Later uses will need specific,
coherent isomorphisms, which `Classical.choice` cannot provide.

The transform of the constant sheaf is computed from the stalk formula
(`AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_geometricStalk`) and
`H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`, which needs `Λ` finite with exponent invertible on `S`. The
transform of the skyscraper is compact-support base change of `Rp₂,!` along the zero section.
The comparison of the transforms for `ψ` and `ψ⁻¹` is base change of `Rp₂,!` along the
isomorphism `ι × 1`, over the identity of the second factor
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_of_isIso`).

TODO: upgrade these back to `Iso` constructions once they can be built.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

-/
