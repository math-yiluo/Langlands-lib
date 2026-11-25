/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.FourierTransform.Defs

/-!

# Base linearity of the Fourier–Deligne transform

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tensor`: the transform is
  linear over the base.
- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_mapDerivedCategory`: the transform of a
  complex pulled back from the base is the base change of the transform of the unit.
- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tateTwist`: the transform commutes
  with the Tate twist.

See `WeilConjectures.FourierTransform.Properties` for the implementation notes.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

section BaseLinear

variable [Finite Λ] [HasInvertibleExponent Λ S] [CharP Γ(pullback π π', ⊤) p]
  [HasCompactification (pullback.snd π π')] [LocallyOfFiniteType (pullback.snd π π')]

/-- Tensoring the input with a complex pulled back from the base `S` along `π : V ⟶ S` is the
same as tensoring the output with the same complex pulled back along `π' : V' ⟶ S`:

`FT_ψ(K ⊗ᴸ π^* N) ≅ FT_ψ(K) ⊗ᴸ π'^* N`

for `K ∈ Dᵇc(V, Λ)` and `N ∈ Dᵇctf(S, Λ)`, naturally in `K` **and** in `N`: the statement below
asserts that the two functors `Dᵇctf(S, Λ) ⥤ (Dᵇc(V, Λ) ⥤ D(V'_ét))` are isomorphic. For fixed
`N` it is the square

```
     Dᵇc(V) ───FT_ψ───▶ D(V'_ét)
        │                    │
  ⊗π^*N │                    │ ⊗π'^*N
        ▼                    ▼
     D(V_ét) ───FT_ψ───▶ D(V'_ét)
```

The blueprint works over a field of coefficients, where every `N ∈ Dᵇc(S)` has finite Tor
amplitude; over the finite ring `Λ` this is the hypothesis `N ∈ Dᵇctf(S, Λ)`. The particular
case `K = Λ_V` is `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_mapDerivedCategory`.

The proof is that of
`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor_of_hasProjectionFormula`, with the
projection formula for `p₂` at `p₁^* K ⊗ᴸ 𝒦_ψ[r]` (bounded constructible, `𝒦_ψ` being lisse of
rank one) and `π'^* N` (in `Dᵇctf`) given by
`AlgebraicGeometry.Etale.hasProjectionFormula_of_boundedConstructible`.
(sketch blueprint: `proposition-base-change-fourier-inversion--2`; blueprint:
`proposition-base-change-fourier-inversion--2`) -/
theorem nonempty_iso_fourierTransform_tensor (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    Nonempty ((DerivedCategory.boundedConstructibleFiniteTor Λ S).ι ⋙
        derivedTensorRightPullback (ModuleCat.{u + 1} Λ) π ⋙
          (Functor.whiskeringRight _ _ _).obj (fourierTransform Λ π π' Ψ b r) ⋙
            (Functor.whiskeringLeft _ _ _).obj
              (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V).ι ≅
      (DerivedCategory.boundedConstructibleFiniteTor Λ S).ι ⋙
        derivedTensorRightPullback (ModuleCat.{u + 1} Λ) π' ⋙
          (Functor.whiskeringLeft _ _ _).obj (fourierTransform Λ π π' Ψ b r) ⋙
            (Functor.whiskeringLeft _ _ _).obj
              (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V).ι) := by
  have := HasInvertibleExponent.of_hom (Λ := Λ) π'
  refine nonempty_iso_kernelTransform_tensor_of_hasProjectionFormula _ π π' _ _
    ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) r
    fun K hK N hN ↦ hasProjectionFormula_of_boundedConstructible Λ _ _ _ ?_
      (constructibleFiniteTor_mapDerivedCategory_upperStar Λ π' hN)
  -- `p₁^* K ⊗ᴸ 𝒦_ψ[r] ≅ (p₁^* K ⊗ᴸ 𝒦_ψ)[r]` is bounded constructible.
  refine (DerivedCategory.boundedConstructible _ _).prop_of_iso
    ((derivedTensorRightShiftIso _ _ r).app _).symm
    ((DerivedCategory.boundedConstructible _ _).le_shift r _ ?_)
  exact boundedConstructible_tensor Λ _ (hK.mapDerivedCategory_upperStar (pullback.fst π π'))
    (DerivedCategory.boundedConstructible_singleFunctor_obj (fourierKernel Λ π π' Ψ b) 0)
    ⟨0, 0, torAmplitudeIn_fourierKernel Λ π π' Ψ b⟩

/-- The first clause of the base linearity proposition: the transform of a complex pulled back
from the base is the base change of the transform of the unit,

`FT_ψ(π^* N) ≅ FT_ψ(Λ_V) ⊗ᴸ π'^* N`

for `N ∈ Dᵇctf(S, Λ)`, naturally in `N`. It is
`AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tensor` at `K = Λ_V`, composed with the
left unitor `Λ_V ⊗ᴸ π^* N ≅ π^* N`.
(sketch blueprint: `proposition-base-change-fourier-inversion--2`; blueprint:
`proposition-base-change-fourier-inversion--2`, clause (1)) -/
theorem nonempty_iso_fourierTransform_mapDerivedCategory (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    Nonempty ((DerivedCategory.boundedConstructibleFiniteTor Λ S).ι ⋙
        D((π)^*[ModuleCat.{u + 1} Λ]) ⋙ fourierTransform Λ π π' Ψ b r ≅
      (DerivedCategory.boundedConstructibleFiniteTor Λ S).ι ⋙
        derivedTensorRightPullback (ModuleCat.{u + 1} Λ) π' ⋙
          (evaluation _ _).obj
            ((fourierTransform Λ π π' Ψ b r).obj (constantComplex Λ V))) := by
  obtain ⟨e⟩ := nonempty_iso_fourierTransform_tensor Λ π π' Ψ b r
  -- `Λ_V` is bounded constructible: it is the constant sheaf `Λ` placed in degree `0`.
  let K₀ : (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V).FullSubcategory :=
    ⟨constantComplex Λ V, (DerivedCategory.boundedConstructible _ _).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0)⟩
  -- `Λ_V ⊗ᴸ M ≅ M`, naturally in `M`.
  let uV : derivedTensorRightFunctor (ModuleCat.{u + 1} Λ) V ⋙
      (evaluation _ _).obj (constantComplex Λ V) ≅ 𝟭 _ :=
    derivedTensorLeftUnitorNatIso _ V
  exact ⟨Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft D((π)^*[ModuleCat.{u + 1} Λ]) uV.symm) _) ≪≫
    Functor.isoWhiskerRight e ((evaluation _ _).obj K₀)⟩

/-- The Fourier–Deligne transform commutes with the Tate twist: `FT_ψ(K(m)) ≅ FT_ψ(K)(m)`
for every `m : ℤ`, naturally in `K ∈ Dᵇc(V, Λ)`:

```
     Dᵇc(V) ───FT_ψ───▶ D(V'_ét)
        │                    │
    (m) │                    │ (m)
        ▼                    ▼
     D(V_ét) ───FT_ψ───▶ D(V'_ét)
```

This is the second clause of the base linearity proposition, the Tate twist being tensoring
with an invertible complex pulled back from the base: it is
`AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tensor` at `N = Λ_S(m)`, which lies in
`Dᵇctf(S, Λ)`, composed with the identifications `π^* Λ_S(m) ≅ Λ_V(m)` and
`π'^* Λ_S(m) ≅ Λ_{V'}(m)`. That the isomorphism is one of Weil complexes when `K` carries a Weil
structure is `AlgebraicGeometry.nonempty_iso_fourierTransform_tateTwist`.
(sketch blueprint: `proposition-base-change-fourier-inversion--2`; blueprint:
`proposition-base-change-fourier-inversion--2`, clause (2)) -/
theorem nonempty_iso_fourierTransform_tateTwist [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r m : ℤ) :
    Nonempty ((DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V).ι ⋙
        tateTwist Λ V m ⋙ fourierTransform Λ π π' Ψ b r ≅
      (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V).ι ⋙
        fourierTransform Λ π π' Ψ b r ⋙ tateTwist Λ V' m) := by
  obtain ⟨e⟩ := nonempty_iso_fourierTransform_tensor Λ π π' Ψ b r
  -- `K ↦ K ⊗ᴸ f^* Λ_S(m)` is the Tate twist `(m)` on the source of `f`.
  let φ {X : Scheme.{u}} (f : X ⟶ S) :
      (derivedTensorRightPullback (ModuleCat.{u + 1} Λ) f).obj (tateObject Λ S m) ≅
        tateTwist Λ X m :=
    haveI : HasInvertibleExponent Λ X := .of_hom f
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso
      (((leftDerivedUpperStarIsoMapDerivedCategory _ f).app _).symm ≪≫
        leftDerivedUpperStarTateObjectIso f m)
  exact ⟨Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (φ π).symm _) ≪≫
    e.app ⟨tateObject Λ S m, boundedConstructibleFiniteTor_tateObject Λ S m⟩ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (φ π'))⟩

end BaseLinear

end AlgebraicGeometry.Etale
