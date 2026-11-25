/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Topology.Sheaves.Abelian

/-! # Module sheafification and localization at an open

Source: Stacks Project, Tag 03DH.
(blueprint: lem-pc-open-localized-module-sheafification)
-/

@[expose] public section

universe u
open CategoryTheory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SheafOfModules

/-- Module sheafification commutes with restriction to the open localized site.

Source: Stacks Project, Tag 03DH, localization of sites; Tag 03CY, module sheafification.
Proof: restrict the sheafification unit to the slice. Every covering sieve of an object
`W → U` is the pullback of a covering sieve of `W`, with the uniquely forced maps to `U`.
The restricted unit is consequently locally injective and locally surjective, and its
codomain is a sheaf on the localized site. Its extension from the sheafification of the
restricted presheaf is an isomorphism. The extension is natural in the presheaf by the
uniqueness clause of the sheafification universal property. Taking its inverse gives
the displayed natural isomorphism. Empty opens and zero rings require no separate case:
the same covering-sieve argument and universal property apply.
(blueprint: lem-pc-open-localized-module-sheafification) -/
theorem exists_open_localized_sheafification
    {X : TopCat.{u}} (A : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : TopologicalSpace.Opens X) :
    let T := PresheafOfModules.sheafification.{u}
      (J := (Opens.grothendieckTopology X).over U) (R := A.over U)
      (𝟙 (A.over U).obj)
    Nonempty
      (PresheafOfModules.sheafification.{u} (R := A) (𝟙 A.obj) ⋙ overFunctor.{u} A U ≅
        PresheafOfModules.pushforward₀.{u} (Over.forget U) A.obj ⋙ T) := by
  dsimp only
  let J := Opens.grothendieckTopology X
  let K := J.over U
  let : K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u}) := inferInstance
  let S := PresheafOfModules.sheafification.{u} (R := A) (𝟙 A.obj)
  let T := PresheafOfModules.sheafification.{u} (J := K) (R := A.over U)
    (𝟙 (A.over U).obj)
  let P : PresheafOfModules.{u} A.obj ⥤ PresheafOfModules.{u} (A.over U).obj :=
    PresheafOfModules.pushforward₀.{u} (Over.forget U) A.obj
  let V := overFunctor.{u} A U
  let a := PresheafOfModules.sheafificationAdjunction.{u} (R := A) (𝟙 A.obj)
  let b := PresheafOfModules.sheafificationAdjunction.{u} (J := K) (R := A.over U)
    (𝟙 (A.over U).obj)
  let t : P ⋙ T ⟶ S ⋙ V :=
    { app M := (b.homEquiv _ _).symm (P.map (a.unit.app M))
      naturality {M N} f := by
        change T.map (P.map f) ≫
          (b.homEquiv (P.obj N) (V.obj (S.obj N))).symm (P.map (a.unit.app N)) =
            (b.homEquiv (P.obj M) (V.obj (S.obj M))).symm (P.map (a.unit.app M)) ≫
              V.map (S.map f)
        erw [← b.homEquiv_naturality_left_symm, ← b.homEquiv_naturality_right_symm]
        congr 1
        change P.map f ≫ P.map (a.unit.app N) =
          P.map (a.unit.app M) ≫
            P.map ((forget A ⋙ PresheafOfModules.restrictScalars (𝟙 A.obj)).map (S.map f))
        rw [← P.map_comp, ← P.map_comp]
        exact congrArg P.map (a.unit.naturality f) }
  have ht (M : PresheafOfModules.{u} A.obj) :
      CategoryTheory.toSheafify K (P.obj M).presheaf ≫
          (PresheafOfModules.toPresheaf (A.over U).obj).map (t.app M).val =
        Functor.whiskerLeft (Over.forget U).op
          (CategoryTheory.toSheafify J M.presheaf) := by
    have h := (b.homEquiv (P.obj M) (V.obj (S.obj M))).apply_symm_apply
      (show P.obj M ⟶ (forget (A.over U) ⋙ PresheafOfModules.restrictScalars
        (𝟙 (A.over U).obj)).obj (V.obj (S.obj M)) from P.map (a.unit.app M))
    have h' := congrArg ((PresheafOfModules.toPresheaf (A.over U).obj).map) h
    change CategoryTheory.toSheafify K (P.obj M).presheaf ≫
      (PresheafOfModules.toPresheaf (A.over U).obj).map (t.app M).val = _ at h'
    exact h'
  have hi (M : PresheafOfModules.{u} A.obj) : IsIso (t.app M) := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (A.over U))]
    apply (Sheaf.isLocallyBijective_iff_isIso (J := K)
      ((SheafOfModules.toSheaf (A.over U)).map (t.app M))).mp
    have h₁ : Presheaf.IsLocallyInjective K
        (Functor.whiskerLeft (Over.forget U).op
          (CategoryTheory.toSheafify J M.presheaf)) :=
      Presheaf.isLocallyInjective_whisker K J (Over.forget U) _
    have h₂ : Presheaf.IsLocallySurjective K
        (Functor.whiskerLeft (Over.forget U).op
          (CategoryTheory.toSheafify J M.presheaf)) :=
      Presheaf.isLocallySurjective_whisker K J (Over.forget U) _
    have : Presheaf.IsLocallyInjective K
        (CategoryTheory.toSheafify K (P.obj M).presheaf) :=
      (K.W_toSheafify _).isLocallyInjective
    have : Presheaf.IsLocallySurjective K
        (CategoryTheory.toSheafify K (P.obj M).presheaf) :=
      (K.W_toSheafify _).isLocallySurjective
    rw [← ht M] at h₁ h₂
    exact ⟨(Presheaf.comp_isLocallyInjective_iff _ _ _).mp h₁,
      (Presheaf.comp_isLocallySurjective_iff _ _ _).mp h₂⟩
  let : ∀ M, IsIso (t.app M) := hi
  let : IsIso t := NatIso.isIso_of_isIso_app t
  exact ⟨(asIso t).symm⟩

end SheafOfModules
