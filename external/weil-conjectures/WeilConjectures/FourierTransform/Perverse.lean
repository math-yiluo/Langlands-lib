/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.SixFunctors.Etale.Perverse.Operations

/-!
# The perverse amplitude of the Fourier–Deligne transform

Let `π : V ⟶ Spec k` and `π' : V' ⟶ Spec k` be separated of finite type over a field `k`, in
the intended application the affine line and its dual. The Fourier–Deligne transform
`FT_ψ = Rp₂,!(p₁^*(-) ⊗ᴸ 𝒦_ψ)[1]` has perverse amplitude at most one on both sides: it carries
`ᵖD^{≤0}(V)` into `ᵖD^{≤1}(V')` and `ᵖD^{≥0}(V)` into `ᵖD^{≥-1}(V')`. The proof composes the
three permanence statements of `WeilConjectures.SixFunctors.Etale.Perverse.Operations`:
`p₁^*` raises both indices by the relative dimension one, the tensor product with the lisse
kernel preserves them, and `Rp₂,!` along the affine projection with fibres of dimension at
most one moves them by one in opposite directions; the normalising shift `[1]` lowers both by
one.

## Main statements

- `AlgebraicGeometry.Etale.isLisse_fourierKernel`: the Fourier kernel is lisse.
- `AlgebraicGeometry.Etale.isPerverseLE_fourierTransform`,
  `AlgebraicGeometry.Etale.isPerverseGE_fourierTransform`: the perverse amplitude of the
  transform.

## Implementation notes

The blueprint states the theorem for `V = V' = 𝔸¹_{k₀}`. It is stated here for a general pair
`π`, `π'` under the three geometric facts the proof uses: the first projection
`p₁ : V ×ₖ V' ⟶ V` is smooth of relative dimension one, and the second projection
`p₂ : V ×ₖ V' ⟶ V'` is affine of finite type with fibres of dimension at most one. For the
affine line all three hold, `p₁` and `p₂` being base changes of `𝔸¹ ⟶ Spec k`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
variable {V V' : Scheme.{u}} (π : V ⟶ Spec (.of k)) (π' : V' ⟶ Spec (.of k))
  [CharP Γ(pullback π π', ⊤) p]

omit [HasInvertibleExponent Λ (Spec (.of k))] in
/-- The Fourier kernel `𝒦_ψ = ℒ_{Ψ, b}`, placed in degree zero, is lisse of rank one: it is
the pullback of the Artin–Schreier sheaf `ℒ_Ψ` along the pairing `b`, hence locally constant,
and it is invertible, with inverse `𝒦_{ψ⁻¹}`; so it is dualizable, constructible and of finite
Tor amplitude. `IsLisse` does not record the rank: that the rank is one is recorded only through
the tensor inverse, `AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_inv`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`; blueprint:
`lemma-artin-schreier-character-sheaf`) -/
theorem isLisse_fourierKernel (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) :
    IsLisse ((_root_.DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) :=
  ⟨isDualizable_fourierKernel Λ π π' Ψ b,
    ⟨DerivedCategory.boundedConstructible_singleFunctor_obj _ 0, 0, 0,
      torAmplitudeIn_fourierKernel Λ π π' Ψ b⟩, torAmplitudeIn_fourierKernel Λ π π' Ψ b,
    fourierKernel Λ π π' Ψ b, inferInstance, ⟨Iso.refl _⟩⟩

variable [LocallyOfFiniteType π] [IsSeparated π] [QuasiCompact π] [HasCompactification π]
  [LocallyOfFiniteType π'] [IsSeparated π'] [QuasiCompact π'] [HasCompactification π']
  [SmoothOfRelativeDimension 1 (pullback.fst π π')] [IsAffineHom (pullback.snd π π')]
  [LocallyOfFiniteType (pullback.snd π π')] [QuasiCompact (pullback.snd π π')]
  [HasCompactification (pullback.snd π π')]

/-- The Fourier–Deligne transform is `Rp₂,!(p₁^*(-) ⊗ᴸ 𝒦_ψ)[1]` with the pullback taken
derived: the functor `D(p₁^*)` induced by the exact pullback is the derived pullback. -/
noncomputable def fourierTransformIso (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) :
    fourierTransform Λ π π' Ψ b 1 ≅ L((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
      derivedTensorRight _ _
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ⋙
      R(pullback.snd π π')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ (1 : ℤ) :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ (pullback.fst π π')).symm _

omit [IsSeparated π] [QuasiCompact π] [HasCompactification π] [IsSeparated π']
  [HasCompactification π'] in
/-- **Perverse amplitude of the Fourier transform**, support side: `FT_ψ` carries
`ᵖD^{≤0}(V) ∩ Dctf(V)` into `ᵖD^{≤1}(V')`. -/
theorem isPerverseLE_fourierTransform
    (hfib : ∀ y, topologicalKrullDim ((pullback.snd π π').fiber y) ≤ ((1 : ℕ) : ℕ∞))
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤))
    {K : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsPerverseLE 0 K) (hK' : constructibleFiniteTor (ModuleCat.{u + 1} Λ) V K) :
    IsPerverseLE 1 ((fourierTransform Λ π π' Ψ b 1).obj K) := by
  have hL := isLisse_fourierKernel π π' Ψ b
  have h₁ := isPerverseLE_tensor (isPerverseLE_upperStar π 1 (pullback.fst π π') hK) hL
  have h₂ := isPerverseLE_lowerShriek π' 1 (pullback.snd π π') hfib h₁
    (constructibleFiniteTor_tensor _ _
      (constructibleFiniteTor_leftDerivedUpperStar _ (pullback.fst π π') hK') hL.2.1)
  rw [show (0 : ℤ) + ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = 1 + 1 by norm_num] at h₂
  refine IsPerverseLE.of_iso ((fourierTransformIso π π' Ψ b).app K).symm ?_
  simp only [Functor.comp_obj, derivedTensorRight, derivedTensor, Functor.flip_obj_obj,
    curriedTensor_obj_obj]
  exact (isPerverseLE_shift_iff _ 1 1).2 h₂

/-- **Perverse amplitude of the Fourier transform**, cosupport side: `FT_ψ` carries
`ᵖD^{≥0}(V) ∩ Dctf(V)` into `ᵖD^{≥-1}(V')`. -/
theorem isPerverseGE_fourierTransform [PerfectField k]
    [HasCompactification (pullback.fst π π' ≫ π)]
    [HasCompactification (pullback.snd π π' ≫ π')]
    (hfib : ∀ y, topologicalKrullDim ((pullback.snd π π').fiber y) ≤ ((1 : ℕ) : ℕ∞))
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤))
    {K : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsPerverseGE π 0 K) (hK' : constructibleFiniteTor (ModuleCat.{u + 1} Λ) V K) :
    IsPerverseGE π' (-1) ((fourierTransform Λ π π' Ψ b 1).obj K) := by
  have hL := isLisse_fourierKernel π π' Ψ b
  have h₁ := isPerverseGE_tensor (isPerverseGE_upperStar π 1 (pullback.fst π π') hK) hL
  have h₂ := isPerverseGE_lowerShriek π' 1 (pullback.snd π π') hfib
    (h₁.of_eq pullback.condition)
    (constructibleFiniteTor_tensor _ _
      (constructibleFiniteTor_leftDerivedUpperStar _ (pullback.fst π π') hK') hL.2.1)
  rw [show (0 : ℤ) + ((1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) = 1 + -1 by norm_num] at h₂
  refine IsPerverseGE.of_iso ((fourierTransformIso π π' Ψ b).app K).symm ?_
  simp only [Functor.comp_obj, derivedTensorRight, derivedTensor, Functor.flip_obj_obj,
    curriedTensor_obj_obj]
  exact (isPerverseGE_shift_iff _ 1 (-1)).2 h₂

end AlgebraicGeometry.Etale
