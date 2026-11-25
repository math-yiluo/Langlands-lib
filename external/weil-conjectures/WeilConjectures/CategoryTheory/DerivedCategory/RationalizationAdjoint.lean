/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationRecollement
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Rationalizing a left adjoint

Let `T₁ : C₁ ⥤ D₁` and `T₂ : C₂ ⥤ D₂` be localization functors at the morphisms of pretriangulated
categories whose mapping cone is `M`-torsion. If a triangulated functor `F : C₁ ⥤ C₂` is a left
adjoint and `F ⋙ T₂ ≅ T₁ ⋙ F'`,
```
       F
   C₁ ───→ C₂
   │        │
 T₁│        │T₂
   ↓        ↓
   D₁ ───→ D₂
       F'
```
then `F'` is a left adjoint (`CategoryTheory.Rationalization.isLeftAdjoint_of_isLocalization`):
it is the rationalization of `F`, and the rationalization of an adjunction is an adjunction
(`CategoryTheory.Rationalization.mapAdjunction`).
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.Rationalization

variable {M : Submonoid ℤ}
  {C₁ : Type u₁} [Category.{v₁} C₁] [Preadditive C₁] [HasZeroObject C₁] [HasShift C₁ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [Pretriangulated C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Preadditive C₂] [HasZeroObject C₂] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₂ n).Additive] [Pretriangulated C₂]
  {D₁ : Type u₃} [Category.{v₃} D₁] {D₂ : Type u₄} [Category.{v₄} D₂]

/-- Let `T₁ : C₁ ⥤ D₁` and `T₂ : C₂ ⥤ D₂` be localization functors at the morphisms with
`M`-torsion mapping cone. If a triangulated functor `F : C₁ ⥤ C₂` is a left adjoint and
`F ⋙ T₂ ≅ T₁ ⋙ F'`, then `F'` is a left adjoint: it is the rationalization of `F`, and the
rationalization of an adjunction is an adjunction. -/
theorem isLeftAdjoint_of_isLocalization (T₁ : C₁ ⥤ D₁) (T₂ : C₂ ⥤ D₂)
    [T₁.IsLocalization (W M C₁)] [T₂.IsLocalization (W M C₂)] (F : C₁ ⥤ C₂) [F.CommShift ℤ]
    [F.IsTriangulated] [F.IsLeftAdjoint] (F' : D₁ ⥤ D₂) (e : F ⋙ T₂ ≅ T₁ ⋙ F') :
    F'.IsLeftAdjoint := by
  let adj := Adjunction.ofIsLeftAdjoint F
  let := adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have := adj.isTriangulated_rightAdjoint
  have := adj.right_adjoint_additive
  have := (mapAdjunction M adj).isLeftAdjoint
  let e₁ := Localization.uniq (Q M C₁) T₁ (W M C₁)
  let e₂ := Localization.uniq (Q M C₂) T₂ (W M C₂)
  let : Localization.Lifting (Q M C₁) (W M C₁) (T₁ ⋙ F') (e₁.functor ⋙ F') :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Localization.compUniqFunctor _ _ _) F'⟩
  let : Localization.Lifting (Q M C₁) (W M C₁) (F ⋙ T₂) (map M F ⋙ e₂.functor) :=
    ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (mapFac M F) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F (Localization.compUniqFunctor _ _ _)⟩
  let φ : map M F ⋙ e₂.functor ≅ e₁.functor ⋙ F' :=
    Localization.liftNatIso (Q M C₁) (W M C₁) _ _ _ _ e
  exact Functor.isLeftAdjoint_of_iso (Functor.isoWhiskerLeft e₁.inverse φ ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁.counitIso F' ≪≫
    Functor.leftUnitor F')

end CategoryTheory.Rationalization
