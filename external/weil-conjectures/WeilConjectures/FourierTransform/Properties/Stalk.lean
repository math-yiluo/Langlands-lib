/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.Defs

/-!

# The stalks of the Fourier–Deligne transform

## Main definitions

- `AlgebraicGeometry.Etale.artinSchreierTwist`: tensoring with the Artin–Schreier sheaf of
  a global function, `K ↦ K ⊗ᴸ ℒ_{Ψ, f}`.
- `AlgebraicGeometry.Etale.fibreToProduct`: the morphism `⟨p₁, p₂ ≫ ξ⟩ : V ×_S T ⟶ V ×_S V'`
  from the fibre of `p₂` over a point `ξ : T ⟶ V'` of the dual.
- `AlgebraicGeometry.Etale.pairingAt`: the function `x ↦ b(x, ξ)` on the base change
  `V ×_S T` of `V` along a point `ξ : T ⟶ V'` of the dual.
- `AlgebraicGeometry.Etale.fourierTransformStalkIso`: the stalk formula as an isomorphism of
  functors.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_geometricStalk`: the stalk of
  `FT_ψ(K)` at a geometric point `ξ` of `V'` is the compactly supported cohomology of
  `K|_{V_ξ} ⊗ᴸ ℒ_{ψ(b(x, ξ))}` on the fibre `V_ξ = V ×_S Ω`, shifted by `r`.

See `WeilConjectures.FourierTransform.Properties` for the implementation notes.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

/-- Twisting by the Artin–Schreier sheaf of a global function: `K ↦ K ⊗ᴸ ℒ_{Ψ, f}`. -/
noncomputable def artinSchreierTwist (X : Scheme.{u}) [CharP Γ(X, ⊤) p]
    (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  derivedTensorRight (ModuleCat.{u + 1} Λ) X
    ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod X Ψ f))

section Stalk

/-- The morphism `⟨p₁, p₂ ≫ ξ⟩ : V ×_S T ⟶ V ×_S V'` from the fibre `V_ξ = V ×_S T` of the
second projection over a point `ξ : T ⟶ V'` of the dual, where `T` lies over `S` via
`ξ ≫ π'`. It is the top arrow of the cartesian square
(`AlgebraicGeometry.Etale.isPullback_fibreToProduct`)

```
                 ⟨p₁, p₂ ≫ ξ⟩
      V ×_S T ─────────────────▶ V ×_S V'
        │                          │
      p₂│                          │p₂
        ▼                          ▼
        T ───────────ξ───────────▶ V'
```
-/
noncomputable def fibreToProduct {T : Scheme.{u}} (ξ : T ⟶ V') :
    pullback π (ξ ≫ π') ⟶ pullback π π' :=
  pullback.lift (pullback.fst π (ξ ≫ π')) (pullback.snd π (ξ ≫ π') ≫ ξ)
    (by rw [Category.assoc]; exact pullback.condition)

@[reassoc (attr := simp)]
lemma fibreToProduct_fst {T : Scheme.{u}} (ξ : T ⟶ V') :
    fibreToProduct π π' ξ ≫ pullback.fst π π' = pullback.fst π (ξ ≫ π') :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma fibreToProduct_snd {T : Scheme.{u}} (ξ : T ⟶ V') :
    fibreToProduct π π' ξ ≫ pullback.snd π π' = pullback.snd π (ξ ≫ π') ≫ ξ :=
  pullback.lift_snd _ _ _

/-- The fibre `V ×_S T` of the second projection `p₂ : V ×_S V' ⟶ V'` over `ξ : T ⟶ V'` is
the fibre product of `p₂` and `ξ`. -/
lemma isPullback_fibreToProduct {T : Scheme.{u}} (ξ : T ⟶ V') :
    IsPullback (fibreToProduct π π' ξ) (pullback.snd π (ξ ≫ π')) (pullback.snd π π') ξ :=
  IsPullback.of_right (h₁₂ := pullback.fst π π') (h₂₂ := π') (v₁₃ := π)
    (by rw [fibreToProduct_fst]; exact IsPullback.of_hasPullback π (ξ ≫ π'))
    (fibreToProduct_snd π π' ξ) (IsPullback.of_hasPullback π π')

/-- The pairing `b` pulled back to the fibre `V_ξ = V ×_S T` of `V` over a point
`ξ : T ⟶ V'` of the dual, where `T` lies over `S` via `ξ ≫ π'`. It is the pullback along the
morphism `AlgebraicGeometry.Etale.fibreToProduct` `V ×_S T ⟶ V ×_S V'` induced by `p₁` and
`p₂ ≫ ξ`:

```
                 ⟨p₁, p₂ ≫ ξ⟩
      V ×_S T ─────────────────▶ V ×_S V'
        │                          │
      p₂│                          │p₂
        ▼                          ▼
        T ───────────ξ───────────▶ V'
```

When `T = Spec Ω` is a geometric point, this is the function `x ↦ b(x, ξ)` on the geometric
fibre `V_ξ`. -/
noncomputable def pairingAt (b : Γ(pullback π π', ⊤)) {T : Scheme.{u}} (ξ : T ⟶ V') :
    Γ(pullback π (ξ ≫ π'), ⊤) :=
  (fibreToProduct π π' ξ).appTop b

section

variable [CharP Γ(pullback π π', ⊤) p] (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤))
  (r : ℤ) {T : Scheme.{u}} (ξ : T ⟶ V') [CharP Γ(pullback π (ξ ≫ π'), ⊤) p]

/-- The pullback of the Fourier kernel to the fibre `V_ξ` is the Artin–Schreier sheaf of the
pairing with `ξ`: `⟨p₁, p₂ ≫ ξ⟩^* 𝒦_ψ ≅ ℒ_{ψ(b(x, ξ))}`, placed in degree `0`. -/
noncomputable def fourierKernelFibreIso :
    D((fibreToProduct π π' ξ)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafZMod (pullback π (ξ ≫ π')) Ψ (pairingAt π π' b ξ)) :=
  ((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _).symm ≪≫
    (singleFunctorCompLeftDerivedUpperStarIso _ _).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (artinSchreierSheafZModPullbackIso (fibreToProduct π π' ξ) Ψ b)

/-- Pulling the Fourier integrand back to the fibre `V_ξ`: with `g = ⟨p₁, p₂ ≫ ξ⟩`,
`g^*(p₁^* K ⊗ᴸ 𝒦_ψ) ≅ (p₁ ∘ g)^* K ⊗ᴸ ℒ_{ψ(b(x, ξ))}`, naturally in `K`. -/
noncomputable def fourierIntegrandFibreIso :
    fourierIntegrand Λ π π' Ψ b ⋙ D((fibreToProduct π π' ξ)^*[ModuleCat.{u + 1} Λ]) ≅
      D((pullback.fst π (ξ ≫ π'))^*[ModuleCat.{u + 1} Λ]) ⋙
        artinSchreierTwist Λ (pullback π (ξ ≫ π')) Ψ (pairingAt π π' b ξ) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ _).symm ≪≫
        derivedTensorRightCompLeftDerivedUpperStarIso _ _ _ ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ _) _ ≪≫
        Functor.isoWhiskerLeft _ ((derivedTensorRightFunctor _ _).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _ ≪≫
            fourierKernelFibreIso Λ π π' Ψ b ξ))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} Λ)
          (fibreToProduct π π' ξ) (pullback.fst π π') (pullback.fst π (ξ ≫ π'))
          (fibreToProduct_fst π π' ξ).symm) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm).symm _

/-- **The stalk formula** as an isomorphism of functors: for a point `ξ : T ⟶ V'` of the
dual,

`ξ^* FT_ψ(K) ≅ Rp₂,!((p₁ ∘ g)^* K ⊗ᴸ ℒ_{ψ(b(x, ξ))})[r]`

on the fibre `V_ξ = V ×_S T`, with `g = ⟨p₁, p₂ ≫ ξ⟩`, naturally in `K`. It is
compact-support base change of `Rp₂,!` along `ξ`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`), followed by the
pullback of the Fourier integrand to `V_ξ`: `Lg^*` is monoidal and
`g^* 𝒦_ψ ≅ ℒ_{ψ(b(x, ξ))}`. For `T = Spec Ω` a geometric point this is the stalk of the
transform at `ξ`; see `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_geometricStalk`.
(sketch blueprint: `proposition-base-change-fourier-inversion--3`; blueprint:
`proposition-base-change-fourier-inversion--3`) -/
noncomputable def fourierTransformStalkIso [Finite Λ] [HasCompactification π]
    [QuasiCompact π] :
    fourierTransform Λ π π' Ψ b r ⋙ D((ξ)^*[ModuleCat.{u + 1} Λ]) ≅
      D((pullback.fst π (ξ ≫ π'))^*[ModuleCat.{u + 1} Λ]) ⋙
        artinSchreierTwist Λ (pullback π (ξ ≫ π')) Ψ (pairingAt π π' b ξ) ⋙
          R(pullback.snd π (ξ ≫ π'))_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ (isPullback_fibreToProduct π π' ξ)
  Functor.isoWhiskerLeft
      (fourierIntegrand Λ π π' Ψ b ⋙ R(pullback.snd π π')_![ModuleCat.{u + 1} Λ])
      (D((ξ)^*[ModuleCat.{u + 1} Λ]).commShiftIso r) ≪≫
    Functor.isoWhiskerLeft (fourierIntegrand Λ π π' Ψ b)
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ ξ).symm ≪≫
          asIso (rightDerivedLowerShriekBaseChangeMap _ (isPullback_fibreToProduct π π' ξ)) ≪≫
          Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ _) _)
        (shiftFunctor _ r) ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fourierIntegrandFibreIso Λ π π' Ψ b ξ) _ ≪≫
    Functor.associator _ _ _

end

/-- For a geometric point `ξ : Spec Ω ⟶ V'` of the dual, with `Ω` separably closed, the
stalk of the Fourier–Deligne transform at `ξ` is the compactly supported cohomology of the
input restricted to the geometric fibre `V_ξ = V ×_S Ω`, twisted by the Artin–Schreier sheaf
of the function `x ↦ b(x, ξ)` of `AlgebraicGeometry.Etale.pairingAt`, shifted by the relative
dimension:

`ξ^* FT_ψ(K) ≅ RΓ_c(V_ξ, K|_{V_ξ} ⊗ᴸ ℒ_{ψ(b(x, ξ))})[r]`,

naturally in `K`. Here `V_ξ` sits in the square

```
                 ⟨p₁, p₂ ≫ ξ⟩
      V_ξ ────────────────────▶ V ×_S V'
        │                          │
      p₂│                          │p₂
        ▼                          ▼
      Spec Ω ────────ξ─────────▶  V'
```

Class: torsion; decided by compact-support base change of `Rp₂,!` along `ξ`, which needs
`[Finite Λ]`. The isomorphism is `AlgebraicGeometry.Etale.fourierTransformStalkIso`.
(sketch blueprint: `proposition-base-change-fourier-inversion--3`; blueprint:
`proposition-base-change-fourier-inversion--3`) -/
theorem nonempty_iso_fourierTransform_geometricStalk [Finite Λ]
    [CharP Γ(pullback π π', ⊤) p] [HasCompactification π] [QuasiCompact π]
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ V')
    [CharP Γ(pullback π (ξ ≫ π'), ⊤) p] :
    Nonempty (fourierTransform Λ π π' Ψ b r ⋙ D((ξ)^*[ModuleCat.{u + 1} Λ]) ≅
      D((pullback.fst π (ξ ≫ π'))^*[ModuleCat.{u + 1} Λ]) ⋙
        artinSchreierTwist Λ (pullback π (ξ ≫ π')) Ψ (pairingAt π π' b ξ) ⋙
          R(pullback.snd π (ξ ≫ π'))_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r) :=
  ⟨fourierTransformStalkIso Λ π π' Ψ b r ξ⟩

end Stalk

end AlgebraicGeometry.Etale
