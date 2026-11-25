/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.AffineSpace
public import WeilConjectures.FourierTransform.AffineSpace.Convolution

/-!

# Invertibility of the Fourier–Deligne transform

Kernel transforms compose: the composite of the kernel transforms of `𝒦` and `𝒦'` is the
kernel transform of the convolution `𝒦' ∗ 𝒦`, with the shifts added
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`). Applied to the Fourier kernels
this reduces the inversion theorem to a single computation, that the convolution of
`𝒦_{ψ⁻¹}` with `𝒦_ψ` is the delta kernel `Δ_* Λ(-r)[-2r]`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution`: the convolution of the two
  Fourier kernels is the delta kernel.
- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_inv` and
  `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_self`: the inversion
  theorem, proved from the statements above.

## Coefficients

Coefficient hypotheses follow the classes in `WeilConjectures.FourierTransform.Defs`.

## Implementation notes

The statements only assert that an isomorphism *exists*. Showing that `FT_ψ` is an
equivalence with inverse `FT_{ψ⁻¹}(r)` will need specific, coherent isomorphisms, which
`Classical.choice` cannot provide.

The proof of `AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution` uses the Thom
isomorphism, Poincaré duality at geometric points, `H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]` and
`H_c^*(𝔸¹, ℒ_ψ) = 0`.

TODO: upgrade these back to `Iso` constructions once they can be built.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.AffineSpace

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]

section Inversion

variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
variable [HasCompactification
  (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The convolution of the kernel of `FT_{ψ⁻¹}` with the kernel of `FT_ψ` on `𝔸(n; S)` is
the delta kernel `Δ_* Λ(-r)[-2r]` supported on the diagonal, `r = #n` being the relative
dimension. The companion statement `𝒦_ψ ∗ 𝒦_ψ ≅ (id × ι')_* Δ_* Λ(-r)[-2r]` is not stated:
its consequence `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_self` is
deduced from this one and `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_inv`.

The character must be **nontrivial** in the strong sense that
`Ψ 1 - 1` is a unit of `Λ`, which is what makes `H_c^*(𝔸¹, ℒ_ψ)` vanish: for `Ψ = 1` both
kernels are constant and the convolution is `Λ(-r)[-2r]`, supported everywhere, and `Ψ ≠ 1`
is not enough when `Λ` is not a domain
(see `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit`).

Class: torsion; decided by the cohomology of `𝔸^r`, `H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`, which needs
`[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `proposition-fourier-inversion`) -/
theorem nonempty_iso_fourierKernel_convolution [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] (Ψ : AddChar (ZMod p) Λ)
    (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty (kernelConvolution (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ⁻¹ (stdPairing n S))) ≅
        (shiftFunctor _ (-2 * (Fintype.card n : ℤ))).obj
          ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
            (tateObject Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))))) := by
  rw [kernelConvolution_eq]
  obtain ⟨e₁⟩ := nonempty_iso_fourierKernel_convolution_integrand Λ n S Ψ
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedLowerShriek_tripleProj₁₃_tripleShear Λ n S
    ((DerivedCategory.singleFunctor _ 0).obj
      (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
  obtain ⟨e₃⟩ := nonempty_iso_rightDerivedLowerShriek_fourierKernel Λ n S Ψ hΨ
  obtain ⟨e₄⟩ := nonempty_iso_leftDerivedUpperStar_sub_tateObject Λ n S
  exact ⟨(R(pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
      (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).mapIso e₁ ≪≫ e₂ ≪≫
    (L((sub n S)^*[ModuleCat.{u + 1} Λ])).mapIso e₃ ≪≫ e₄⟩

/-- **Fourier inversion.** On `𝔸(n; S)` the Fourier–Deligne transform for the inverse
character inverts the Fourier–Deligne transform up to the Tate twist `(-r)`,
`r = #n` being the relative dimension:

`FT_{ψ⁻¹} FT_ψ(K) ≅ K(-r)`,

functorially in `K`:

```
                 FT_ψ
     D(𝔸(n; S)) ─────▶ D(𝔸(n; S))
              ╲             │
          (-r)  ╲           │ FT_ψ⁻¹
                  ▶         ▼
                    D(𝔸(n; S))
```

The proof composes the two kernel transforms
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`), computes the convolution of the
kernels (`AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution`), moves the shift
out of the kernel and recognises the kernel transform of `Δ_* Λ(-r)` as the Tate twist
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal`). The hypotheses are those
of the convolution computation: for `Ψ = 1` the transform is `Rp₂,! p₁^*(-)[r]`, which is not
invertible.
The composition law of kernel transforms also needs the projection
`𝔸(n; S) ×ₛ 𝔸(n; S) ×ₛ 𝔸(n; S) ⟶ 𝔸(n; S)` onto the last factor to admit a compactification.

Class: torsion; decided by the convolution computation
`AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution` (cohomology of `𝔸^r`), which
needs `[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sec-Fourier-inversion`) -/
-- TODO: discharge the `HasCompactification` hypothesis: the composite is a morphism
-- `𝔸^{3n}_S ⟶ 𝔸^n_S`, which is compactified through projective space by
-- `AlgebraicGeometry.Compactification.ofIsImmersionAffineSpace`, with no need for Nagata.
theorem nonempty_iso_affineFourierTransform_comp_inv [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
    [HasCompactification (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) ≫
      pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty (affineFourierTransform Λ n S Ψ ⋙ affineFourierTransform Λ n S Ψ⁻¹ ≅
        tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))) := by
  -- The kernel transform depends functorially on the kernel. Tensoring is first mapped over
  -- an arbitrary scheme `X`: doing so directly over the fibre product times out in the kernel.
  have ht {X : Scheme.{u}} {N N' : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))} (f : N ≅ N') :
      derivedTensorRight (ModuleCat.{u + 1} Λ) X N ≅
        derivedTensorRight (ModuleCat.{u + 1} Λ) X N' :=
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso f
  have hk {𝒦 𝒦' : DerivedCategory (Sheaf (pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))} (e : 𝒦 ≅ 𝒦') (a : ℤ) :
      kernelTransform (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) 𝒦 a ≅
        kernelTransform (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) 𝒦' a :=
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (ht e) _)
  obtain ⟨e₁⟩ := nonempty_iso_kernelTransform_comp Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
    (𝔸(n; S) ↘ S) ((DerivedCategory.singleFunctor _ 0).obj
      (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
    ((DerivedCategory.singleFunctor _ 0).obj
      (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ⁻¹ (stdPairing n S)))
    (Fintype.card n) (Fintype.card n)
  obtain ⟨e₂⟩ := nonempty_iso_fourierKernel_convolution Λ n S Ψ hΨ
  obtain ⟨e₃⟩ := nonempty_iso_kernelTransform_shift (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S)
    (𝔸(n; S) ↘ S)
    ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
      (tateObject Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))))
    (-2 * (Fintype.card n : ℤ)) (Fintype.card n + Fintype.card n)
  obtain ⟨e₄⟩ := nonempty_iso_kernelTransform_diagonal Λ (𝔸(n; S) ↘ S)
    (tateObject Λ (𝔸(n; S)) (-(Fintype.card n : ℤ)))
  have hr : -2 * (Fintype.card n : ℤ) + (Fintype.card n + Fintype.card n) = 0 := by ring
  exact ⟨e₁ ≪≫ hk e₂ _ ≪≫ e₃ ≪≫
    eqToIso (congrArg (kernelTransform (ModuleCat.{u + 1} Λ) _ _ _) hr) ≪≫ e₄⟩

/-- Applying the Fourier–Deligne transform twice with the *same* character gives back the
reflection `ι^* K` of the input, Tate twisted by `(-r)`:

`FT_ψ FT_ψ(K) ≅ ι^* K(-r)`,

functorially in `K`, where `ι = AlgebraicGeometry.AffineSpace.neg` is `x ↦ -x`:

```
                 FT_ψ
     D(𝔸(n; S)) ─────▶ D(𝔸(n; S))
              ╲             │
     ι^* ⋙ (-r) ╲           │ FT_ψ
                  ▶         ▼
                    D(𝔸(n; S))
```

It follows from `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_inv`, which
gives `FT_ψ ≅ ι^* ⋙ FT_{ψ⁻¹}`, and inversion
(`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_inv`) for `ψ⁻¹`; the
hypotheses are those of inversion.

Class: torsion; decided by inversion
`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_inv`, which needs
`[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sec-Fourier-inversion`) -/
theorem nonempty_iso_affineFourierTransform_comp_self [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
    [HasCompactification (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) ≫
      pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty (affineFourierTransform Λ n S Ψ ⋙ affineFourierTransform Λ n S Ψ ≅
        D((neg n S)^*[ModuleCat.{u + 1} Λ]) ⋙
          tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))) := by
  have h : Ψ⁻¹ 1 * Ψ 1 = 1 := by
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hΨ' : IsUnit (Ψ⁻¹ 1 - 1) := by
    rw [show Ψ⁻¹ 1 - 1 = -Ψ⁻¹ 1 * (Ψ 1 - 1) by linear_combination h]
    exact (IsUnit.of_mul_eq_one _ h).neg.mul hΨ
  obtain ⟨s⟩ := nonempty_iso_affineFourierTransform_inv Λ n S Ψ⁻¹
  obtain ⟨i⟩ := nonempty_iso_affineFourierTransform_comp_inv Λ n S Ψ⁻¹ hΨ'
  rw [inv_inv] at s i
  exact ⟨Functor.isoWhiskerRight s _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ i⟩

end Inversion

end AlgebraicGeometry.Etale
