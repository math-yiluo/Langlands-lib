/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.FourierTransform.AffineSpace.KernelTransform
public import WeilConjectures.FourierTransform.AffineSpace.NegProd
public import WeilConjectures.FourierTransform.Defs

/-!
# The Fourier transform on relative affine space

The Fourier–Deligne transform on relative affine space
(`AlgebraicGeometry.Etale.affineFourierTransform`), its value on the skyscraper at the zero
section, and the comparison of the transforms for `ψ` and `ψ⁻¹`
(`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_inv`). Its value on the constant
sheaf is in `WeilConjectures.FourierTransform.AffineSpace.Unit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.AffineSpace

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The Fourier–Deligne transform of affine `n`-space over `S`: the transform of
`AlgebraicGeometry.Etale.fourierTransform` for `𝔸(n; S)` paired with itself by the standard
pairing `⟨x, ξ⟩ = ∑ᵢ xᵢ ξᵢ` and shifted by the relative dimension `r = #n`. On the affine
line this is `FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ ℒ_{ψ(xξ)})[1]`. -/
noncomputable def affineFourierTransform (Ψ : AddChar (ZMod p) Λ) :
    DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fourierTransform Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S) (Fintype.card n)

/-- The skyscraper `δ₀` at the origin of `𝔸(n; S)`: the direct image of the constant sheaf
`Λ` along the zero section. -/
noncomputable def skyscraperZero :
    DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (R((zeroSection n S)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)

/-- The Fourier–Deligne transform of the skyscraper at the origin of `𝔸(n; S)` is the
constant sheaf, shifted by the relative dimension `r = #n`:

`FT_ψ(δ₀) ≅ Λ[r]`.

On the affine line, the blueprint's case, this reads `FT_ψ(δ₀) ≅ Λ[1]`. Unlike
`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit` this holds for every
character: the kernel restricted to `{0} ×_S 𝔸(n; S)` is the Artin–Schreier sheaf of the zero
function.

Class: torsion; decided by compact-support base change of `Rp₂,!` along the zero section,
which needs `[Finite Λ]`. The proof
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_obj_rightDerivedLowerStar`) writes
`δ₀ = Rz_* Λ = Rz_! Λ`, moves `p₁^*` past it by base change, applies the projection formula for
the base change `ξ ↦ (0, ξ)` of `z`, along which the kernel is trivial, and ends with
`R(p₂ ∘ (0, 1))_! = R(𝟙)_!`.
(sketch blueprint: `lemma-fourier-transform-constant-sheaf`) -/
theorem nonempty_iso_affineFourierTransform_skyscraperZero [Finite Λ] (Ψ : AddChar (ZMod p) Λ) :
    Nonempty ((affineFourierTransform Λ n S Ψ).obj (skyscraperZero Λ n S) ≅
        (shiftFunctor _ (Fintype.card n : ℤ)).obj (𝟙_ _)) := by
  let A := ModuleCat.{u + 1} Λ
  -- the base change `ξ ↦ (0, ξ)` of the zero section along the first projection
  let z' : 𝔸(n; S) ⟶ pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) :=
    pullback.lift ((𝔸(n; S) ↘ S) ≫ zeroSection n S) (𝟙 _) (by simp)
  have hz₁ : z' ≫ pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) = (𝔸(n; S) ↘ S) ≫ zeroSection n S :=
    pullback.lift_fst _ _ _
  have hz₂ : z' ≫ pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) = 𝟙 _ := pullback.lift_snd _ _ _
  have sq : IsPullback (𝔸(n; S) ↘ S) z' (zeroSection n S)
      (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) := by
    refine IsPullback.of_bot ?_ hz₁.symm
      (IsPullback.of_hasPullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
    rw [hz₂, zeroSection_comp_over]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  have : IsClosedImmersion z' := MorphismProperty.of_isPullback sq inferInstance
  -- `𝔸(n; S)` has characteristic `p`, being a retract of `𝔸(n; S) ×_S 𝔸(n; S)`
  have hinj : Function.Injective (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)).appTop.hom := by
    refine Function.LeftInverse.injective (g := z'.appTop.hom) fun x ↦ ?_
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz₂, Scheme.Hom.id_appTop,
      CommRingCat.id_apply]
  have : CharP Γ(𝔸(n; S), ⊤) p := ⟨fun m ↦ by
    rw [← CharP.cast_eq_zero_iff Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p,
      ← map_natCast (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)).appTop.hom,
      map_eq_zero_iff _ hinj]⟩
  -- the pairing vanishes along `z'`
  have hb : z'.appTop (stdPairing n S) = 0 := by
    rw [stdPairing, map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz₁, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, zeroSection_appTop_coord, map_zero, zero_mul]
  let := 𝔸(n; S).overSpecZModOfCharP p
  obtain ⟨e₀⟩ := nonempty_iso_artinSchreierSheafOf_zero 𝔸(n; S)
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) (Λ := Λ)
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_singleFunctor Λ z'
    (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)) (𝟙_ _)
    (artinSchreierSheafZModPullbackIso z' Ψ (stdPairing n S) ≪≫
      eqToIso (congrArg (artinSchreierSheafZMod _ Ψ) hb) ≪≫ e₀)
  -- no abbreviation for `𝔸(n; S) ↘ S`: `set` would duplicate the instances mentioning it
  exact nonempty_iso_kernelTransform_obj_rightDerivedLowerStar Λ
    (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
    (zeroSection n S) z' (𝔸(n; S) ↘ S) sq hz₂ _ (e ≪≫ singleFunctorObjUnitIso A _) _

/-- The Fourier–Deligne transform for the inverse character is the transform of the reflected
input, `ι = AlgebraicGeometry.AffineSpace.neg` being `x ↦ -x`:

`FT_{ψ⁻¹}(K) ≅ FT_ψ(ι^* K)`,

naturally in `K`:

```
                 ι^*
     D(𝔸(n; S)) ─────▶ D(𝔸(n; S))
              ╲             │
        FT_ψ⁻¹  ╲           │ FT_ψ
                  ▶         ▼
                    D(𝔸(n; S))
```

The kernel of `FT_{ψ⁻¹}` is the pullback of the kernel of `FT_ψ` along `ι × 1`, by
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_inv` and `b(-x, ξ) = -b(x, ξ)`.
It holds for every character.

The proof is compact-support base change of `Rp₂,!` along the cartesian square with sides
`ι × 1`, `p₂`, `p₂` and `𝟙`, so the same compactification of `p₂` is used on both sides;
`[Finite Λ]` enters through that base change
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`).
(sketch blueprint: `sec-Fourier-inversion`, remark; `lemma-artin-schreier-character-sheaf--2`) -/
theorem nonempty_iso_affineFourierTransform_inv [Finite Λ] (Ψ : AddChar (ZMod p) Λ) :
    Nonempty (affineFourierTransform Λ n S Ψ⁻¹ ≅
        D((neg n S)^*[ModuleCat.{u + 1} Λ]) ⋙ affineFourierTransform Λ n S Ψ) := by
  set π := 𝔸(n; S) ↘ S
  let := (pullback π π).overSpecZModOfCharP p
  have hΨ : Ψ⁻¹.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom =
      (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom)⁻¹ := by
    ext; simp
  -- `σ^* 𝒦_{ψ⁻¹} = ℒ_{ψ⁻¹, -b} ≅ ℒ_{ψ, b} = 𝒦_ψ`, `σ = ι × 1`
  obtain ⟨e₀⟩ := nonempty_iso_artinSchreierSheafOf_neg_inv (pullback π π)
    (Ψ⁻¹.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) (stdPairing n S)
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_singleFunctor Λ (negProd n S)
    (fourierKernel Λ π π Ψ⁻¹ (stdPairing n S)) (fourierKernel Λ π π Ψ (stdPairing n S))
    (artinSchreierSheafZModPullbackIso (negProd n S) Ψ⁻¹ (stdPairing n S) ≪≫
      eqToIso (congrArg (artinSchreierSheafZMod _ Ψ⁻¹) (negProd_appTop_stdPairing n S)) ≪≫
      e₀ ≪≫ eqToIso (congrArg (artinSchreierSheafOf (pullback π π) · (stdPairing n S))
        (by rw [hΨ, inv_inv])))
  exact nonempty_iso_kernelTransform_of_isIso Λ (pullback.fst π π) (pullback.snd π π)
    (negProd n S) (neg n S) (negProd_fst n S) (negProd_snd n S) _ _ e _

end AlgebraicGeometry.Etale
