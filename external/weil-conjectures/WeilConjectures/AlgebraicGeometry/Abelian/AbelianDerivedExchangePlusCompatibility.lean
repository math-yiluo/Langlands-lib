/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

set_option linter.privateModule false

/-!
# Restriction of the abelian derived exchange to bounded-below complexes
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem inverse_mate_app
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
    (β : TwoSquare R₁ H G R₂) (K : C₁) :
    ((mateEquiv adj₁ adj₂).symm β).app K =
      L₂.map (G.map (adj₁.unit.app K) ≫ β.app (L₁.obj K)) ≫
        adj₂.counit.app (H.obj (L₁.obj K)) := by
  simp [mateEquiv]

private noncomputable def exactComp {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W)
    (d : U ⟶ W := a ≫ b) (hd : d = a ≫ b := by cat_disch) :
    D(upperStar AddCommGrpCat.{u + 1} d) ≅
      D(upperStar AddCommGrpCat.{u + 1} b) ⋙ D(upperStar AddCommGrpCat.{u + 1} a) :=
  Functor.mapDerivedCategoryNatIso (upperStarComp AddCommGrpCat.{u + 1} a b d hd) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

private noncomputable def exactSquare {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S} (sq : CommSq e h g f) :
    D(upperStar AddCommGrpCat.{u + 1} f) ⋙ D(upperStar AddCommGrpCat.{u + 1} h) ≅
      D(upperStar AddCommGrpCat.{u + 1} g) ⋙ D(upperStar AddCommGrpCat.{u + 1} e) :=
  (exactComp h f (e ≫ g) sq.w).symm ≪≫ exactComp e g

end AlgebraicGeometry.Etale
