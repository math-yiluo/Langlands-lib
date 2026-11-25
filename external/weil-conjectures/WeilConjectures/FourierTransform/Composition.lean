/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FourierTransform.Defs

/-!
# Composition of Fourier–Deligne transforms

Fourier–Deligne transforms are kernel transforms, so their composites are again kernel
transforms: the composite of the transforms with kernels `𝒦_ψ` on `V ×_S V'` and `𝒦_{ψ'}` on
`V' ×_S V''` and shifts `r`, `r'` is the kernel transform with kernel the convolution
`𝒦_{ψ'} ∗ 𝒦_ψ` and shift `r + r'`
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`). This reduces Fourier inversion to
the computation of the convolution of the Fourier kernels.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_comp`: `FT_{ψ'} ∘ FT_ψ` is the kernel
  transform of `𝒦_{ψ'} ∗ 𝒦_ψ` with shift `r + r'`.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

/-- The composite of two Fourier–Deligne transforms is a kernel transform: for pairings `b` on
`V ×_S V'` and `b'` on `V' ×_S V''`, characters `Ψ`, `Ψ'` and shifts `r`, `r'`,

`FT_{ψ'} ∘ FT_ψ ≅ Φ_{𝒦_{ψ'} ∗ 𝒦_ψ}[r + r']`,

the kernel transform of the convolution
`𝒦_{ψ'} ∗ 𝒦_ψ = r₁₃,!(r₁₂^* 𝒦_ψ ⊗ᴸ r₂₃^* 𝒦_{ψ'})` on `V ×_S V''`. In particular
`FT_{ψ⁻¹} FT_ψ` is the kernel transform with kernel `𝒦_{ψ⁻¹} ∗ 𝒦_ψ` and shift `2r`.

Class: torsion; decided by compact-support base change and the projection formula for `Rf_!`
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`), which need `[Finite Λ]`.
(sketch blueprint: `proposition-fourier-inversion`; blueprint: `proposition-fourier-inversion`) -/
theorem nonempty_iso_fourierTransform_comp [Finite Λ]
    [LocallyOfFiniteType π] [QuasiCompact π] [LocallyOfFiniteType π'] [QuasiCompact π']
    [CharP Γ(pullback π π', ⊤) p] [CharP Γ(pullback π' π'', ⊤) p]
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    [HasCompactification (pullback.snd π π')] [HasCompactification (pullback.snd π' π'')]
    [HasCompactification (pullback.snd π π'')]
    [HasCompactification (pullback.tripleProj₁₃ π π' π'' ≫ pullback.snd π π'')]
    (Ψ Ψ' : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (b' : Γ(pullback π' π'', ⊤))
    (r r' : ℤ) :
    Nonempty (fourierTransform Λ π π' Ψ b r ⋙ fourierTransform Λ π' π'' Ψ' b' r' ≅
      kernelTransform (ModuleCat.{u + 1} Λ) π π''
        (kernelConvolution (ModuleCat.{u + 1} Λ) π π' π''
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b))
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π' π'' Ψ' b')))
        (r + r')) :=
  nonempty_iso_kernelTransform_comp Λ π π' π'' _ _ r r'

end AlgebraicGeometry.Etale
