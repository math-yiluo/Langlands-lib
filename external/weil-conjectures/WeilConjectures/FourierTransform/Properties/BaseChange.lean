/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.Defs

/-!

# Base change of the Fourier–Deligne transform

## Main definitions

- `AlgebraicGeometry.Etale.pairingBaseChange`: the base change of the pairing.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_baseChange`: the transform commutes
  with base change along `S' ⟶ S`.

See `WeilConjectures.FourierTransform.Properties` for the implementation notes.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

section BaseChange

/-- The base change of the pairing `b` along `g : S' ⟶ S`: its pullback to `W ×_{S'} W'`
along the induced morphism of fibre products,

```
      W ──u──▶ V           W' ──u'──▶ V'
      │        │            │         │
     ρ│        │π          ρ'│        │π'
      ▼        ▼            ▼         ▼
      S' ──g──▶ S           S' ──g──▶ S
```

Only commutativity of the two squares is needed to pull the pairing back; the base change
*theorem* below asks them to be cartesian. -/
noncomputable def pairingBaseChange (b : Γ(pullback π π', ⊤)) {S' W W' : Scheme.{u}}
    (g : S' ⟶ S) (ρ : W ⟶ S') (ρ' : W' ⟶ S') (u : W ⟶ V) (u' : W' ⟶ V')
    (hu : u ≫ π = ρ ≫ g) (hu' : u' ≫ π' = ρ' ≫ g) :
    Γ(pullback ρ ρ', ⊤) :=
  (pullback.map ρ ρ' π π' u u' g hu.symm hu'.symm).appTop b

/-- For a morphism `g : S' ⟶ S` and the base changes `W = V ×_S S'`, `W' = V' ×_S S'` with
the pulled back pairing, the Fourier–Deligne transform commutes with the pullbacks
`u^* : D(V_ét) ⥤ D(W_ét)` and `u'^* : D(V'_ét) ⥤ D(W'_ét)`:

`FT_ψ(u^* K) ≅ u'^* FT_ψ(K)`,

naturally in `K`. Both squares

```
      W ──u──▶ V           W' ──u'──▶ V'
      │        │            │         │
     ρ│        │π          ρ'│        │π'
      ▼        ▼            ▼         ▼
      S' ──g──▶ S           S' ──g──▶ S
```

must be **cartesian**; the statement fails for merely commuting squares.

Class: compactification-dependent; decided by independence of the compactification. The
blueprint proof is formal: compact-support base change along the cartesian square
`W ×_{S'} W' ⟶ V ×_S V'`. Here `[Finite Λ]` enters solely through independence of the
compactification (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`), since `R(f)_!` is
computed with a chosen compactification. The same comparison is why
`[QuasiCompact (pullback.snd π π')]` is assumed: compact-support base change
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap` needs the base changed
morphism `f' = pullback.snd ρ ρ'` to be quasi-compact, because it goes through
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`, and `f'` is quasi-compact as a base change
of `pullback.snd π π'` (`MorphismProperty.of_isPullback`).
(sketch blueprint: `proposition-base-change-fourier-inversion--1`) -/
theorem nonempty_iso_fourierTransform_baseChange [Finite Λ]
    [CharP Γ(pullback π π', ⊤) p] [HasCompactification (pullback.snd π π')]
    [LocallyOfFiniteType (pullback.snd π π')] [QuasiCompact (pullback.snd π π')]
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ) {S' W W' : Scheme.{u}}
    (g : S' ⟶ S) (ρ : W ⟶ S') (ρ' : W' ⟶ S') (u : W ⟶ V) (u' : W' ⟶ V')
    (hu : IsPullback u ρ π g) (hu' : IsPullback u' ρ' π' g)
    [CharP Γ(pullback ρ ρ', ⊤) p] [HasCompactification (pullback.snd ρ ρ')] :
    Nonempty (D((u)^*[ModuleCat.{u + 1} Λ]) ⋙
          fourierTransform Λ ρ ρ' Ψ
            (pairingBaseChange π π' b g ρ ρ' u u' hu.w hu'.w) r ≅
        fourierTransform Λ π π' Ψ b r ⋙ D((u')^*[ModuleCat.{u + 1} Λ])) := by
  -- the induced morphism `h : W ×_{S'} W' ⟶ V ×_S V'` of fibre products
  let h : pullback ρ ρ' ⟶ pullback π π' := pullback.map ρ ρ' π π' u u' g hu.w.symm hu'.w.symm
  -- the square of `h` over `u'` is cartesian: pasted with the square of `V ×_S V'` it is the
  -- square of `W ×_{S'} W'` pasted with the cartesian square of `u`
  have hsq : IsPullback h (pullback.snd ρ ρ') (pullback.snd π π') u' := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback π π')
    rw [pullback.lift_fst, hu'.w]
    exact (IsPullback.of_hasPullback ρ ρ').paste_horiz hu
  have : QuasiCompact (pullback.snd ρ ρ') :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq inferInstance
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ hsq
  have hb : pairingBaseChange π π' b g ρ ρ' u u' hu.w hu'.w = h.appTop b := by
    unfold pairingBaseChange; rfl
  rw [hb]
  -- the kernel pulls back to the kernel: `Lh^* 𝒦_ψ ≅ 𝒦'_ψ`
  let eK : L((h)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ ρ ρ' Ψ (h.appTop b)) :=
    (leftDerivedUpperStarIsoMapDerivedCategory _ h).app _ ≪≫
      ((h)^*[ModuleCat.{u + 1} Λ].mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (artinSchreierSheafZModPullbackIso h Ψ b)
  refine ⟨?_⟩
  calc D((u)^*[ModuleCat.{u + 1} Λ]) ⋙ D((pullback.fst ρ ρ')^*[ModuleCat.{u + 1} Λ]) ⋙
        derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback ρ ρ')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ ρ ρ' Ψ (h.appTop b))) ⋙
        R(pullback.snd ρ ρ')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r
      _ ≅ L((u)^*[ModuleCat.{u + 1} Λ]) ⋙ L((pullback.fst ρ ρ')^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback ρ ρ')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ ρ ρ' Ψ (h.appTop b))) ⋙
          R(pullback.snd ρ ρ')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r :=
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ u).symm _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
            (leftDerivedUpperStarIsoMapDerivedCategory _ (pullback.fst ρ ρ')).symm _)
      _ ≅ L((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙ L((h)^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback ρ ρ')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ ρ ρ' Ψ (h.appTop b))) ⋙
          R(pullback.snd ρ ρ')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r :=
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight ((leftDerivedUpperStarComp _ (pullback.fst ρ ρ') u).symm ≪≫
            leftDerivedUpperStarComp _ h (pullback.fst π π') _ (pullback.lift_fst _ _ _).symm) _ ≪≫
          Functor.associator _ _ _
      _ ≅ L((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙ L((h)^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight _ _ (L((h)^*[ModuleCat.{u + 1} Λ]).obj
            ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b))) ⋙
          R(pullback.snd ρ ρ')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r :=
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
          (Functor.isoWhiskerRight ((derivedTensor _ _).flip.mapIso eK.symm) _))
      _ ≅ L((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ⋙
          L((h)^*[ModuleCat.{u + 1} Λ]) ⋙ R(pullback.snd ρ ρ')_![ModuleCat.{u + 1} Λ] ⋙
          shiftFunctor _ r :=
        Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (derivedTensorRightCompLeftDerivedUpperStarIso _ h _).symm _ ≪≫
          Functor.associator _ _ _)
      _ ≅ L((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ⋙
          R(pullback.snd π π')_![ModuleCat.{u + 1} Λ] ⋙ L((u')^*[ModuleCat.{u + 1} Λ]) ⋙
          shiftFunctor _ r :=
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (asIso (rightDerivedLowerShriekBaseChangeMap _ hsq)).symm _ ≪≫
          Functor.associator _ _ _))
      _ ≅ L((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ⋙
          R(pullback.snd π π')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r ⋙
          L((u')^*[ModuleCat.{u + 1} Λ]) :=
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
          (L((u')^*[ModuleCat.{u + 1} Λ]).commShiftIso r).symm))
      _ ≅ D((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ⋙
          R(pullback.snd π π')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r ⋙
          D((u')^*[ModuleCat.{u + 1} Λ]) :=
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ _) _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
            (Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ u'))))

end BaseChange

end AlgebraicGeometry.Etale
