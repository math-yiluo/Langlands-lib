/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.FourierTransform.Properties.BaseChange
public import WeilConjectures.FourierTransform.Properties.BaseLinear
public import WeilConjectures.FourierTransform.Properties.Stalk
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

/-!

# Formal properties of the Fourier–Deligne transform

The Fourier–Deligne transform of `WeilConjectures.FourierTransform.Defs` is a kernel
transform, and the properties collected here are the ones a kernel transform always has:
its stalks are integrals of the input against the kernel, it commutes with base change on
`S`, it is linear over the base — it turns tensoring with a complex pulled back from `S`
into tensoring with the same complex pulled back to the dual — and it commutes with the
Tate twist.

All four are stated as isomorphisms of *functors*: an object-wise family of isomorphisms
would not suffice downstream, where they are used to build the inverse functor and to
transport `t`-structures.

## Main definitions

- `AlgebraicGeometry.Etale.artinSchreierTwist`: tensoring with the Artin–Schreier sheaf of
  a global function, `K ↦ K ⊗ᴸ ℒ_{Ψ, f}`.
- `AlgebraicGeometry.Etale.fibreToProduct`: the morphism `⟨p₁, p₂ ≫ ξ⟩ : V ×_S T ⟶ V ×_S V'`
  from the fibre of `p₂` over a point `ξ : T ⟶ V'` of the dual.
- `AlgebraicGeometry.Etale.pairingAt`: the function `x ↦ b(x, ξ)` on the base change
  `V ×_S T` of `V` along a point `ξ : T ⟶ V'` of the dual.
- `AlgebraicGeometry.Etale.fourierTransformStalkIso`: the stalk formula as an isomorphism of
  functors.
- `AlgebraicGeometry.Etale.pairingBaseChange`: the base change of the pairing.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_geometricStalk`: the stalk of
  `FT_ψ(K)` at a geometric point `ξ` of `V'` is the compactly supported cohomology of
  `K|_{V_ξ} ⊗ᴸ ℒ_{ψ(b(x, ξ))}` on the fibre `V_ξ = V ×_S Ω`, shifted by `r`.
- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_baseChange`: the transform commutes
  with base change along `S' ⟶ S`.
- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tensor`: the transform is
  linear over the base.
- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tateTwist`: the transform commutes
  with the Tate twist.

## Coefficients

Coefficient hypotheses follow the classes in `WeilConjectures.FourierTransform.Defs`.

## Implementation notes

The stalk formula is constructed as an isomorphism
(`AlgebraicGeometry.Etale.fourierTransformStalkIso`). The base change, base linearity and Tate
twist compatibilities only assert that an isomorphism *exists*. Later uses, such as
transporting `t`-structures, will need specific isomorphisms that are coherent with one
another, which `Classical.choice` cannot provide.

The stalk formula and base change are compact-support base change for `Rp₂,!`
(sketch blueprint: `sk-prop-sf-cbc`), along `ξ` for the stalk formula and along the induced
cartesian square `W ×_{S'} W' ⟶ V ×_S V'` for base change. For the stalk formula it is
followed by the pullback of the kernel to `V_ξ`, which is formal (`Lξ^*` is monoidal); no
smooth base change is needed. In both cases the result is compared with `Rp₂,!` computed
with the *chosen* compactification of the base changed projection
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`), which needs that projection to be
quasi-compact: it is a base change of `π`, resp. of `pullback.snd π π'`, which are assumed
quasi-compact.

Base linearity is the base linearity of kernel transforms on full subcategories
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor_of_hasProjectionFormula`), that
is, the projection formula for `Rp₂,!`. As in the blueprint it is stated for `K` bounded
constructible and `N` in `Dᵇctf`, where the projection formula of `sk-thm-sf-pf-finite`
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_boundedConstructible`) applies to
`p₁^* K ⊗ᴸ 𝒦_ψ[r]` and `π'^* N`.

TODO: upgrade these back to `Iso` constructions once the exchange isomorphisms they are
built from exist as data.

This module only imports its parts: the stalk formula is in
`WeilConjectures.FourierTransform.Properties.Stalk`, base change in
`WeilConjectures.FourierTransform.Properties.BaseChange` and base linearity and the Tate twist
in `WeilConjectures.FourierTransform.Properties.BaseLinear`.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

-/

