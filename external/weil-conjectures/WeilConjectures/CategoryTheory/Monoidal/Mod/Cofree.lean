/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Cofree modules

Let `A` be a monoid object in a monoidal closed category `C`. The internal hom `[A, Y]` is an
`A`-module, with `(a · f)(x) = f (x a)` (`CategoryTheory.Mod.cofreeModObj`); this is the cofree
`A`-module on `Y`, right adjoint to the forgetful functor
(`CategoryTheory.Mod.forgetCofreeAdjunction`).

A lax monoidal functor `F` sends `[A, Y]` to an `F A`-module mapping to the cofree module
`[F A, F Y]` through the comparison map of internal homs (`CategoryTheory.Mod.mapModCofreeHom`).
Hence for a monoidal adjunction `F ⊣ G` whose left adjoint commutes with internal homs out of
`A`, the induced left adjoint on modules sends cofree modules to cofree modules
(`CategoryTheory.Adjunction.modLeftCofreeIso`).
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj MonoidalClosed

namespace CategoryTheory.Mod

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C] (A : C) [MonObj A]

/-- The action `(a · f)(x) = f (x a)` of `A` on `[A, Y]`. -/
def cofreeAct (Y : C) : A ⊗ (ihom A).obj Y ⟶ (ihom A).obj Y :=
  curry ((α_ A A _).inv ≫ μ ▷ _ ≫ (ihom.ev A).app Y)

/-- The uncurried action of `A` on `[A, Y]`. -/
lemma uncurry_cofreeAct (Y : C) :
    uncurry (cofreeAct A Y) = (α_ A A _).inv ≫ μ ▷ _ ≫ (ihom.ev A).app Y := by
  rw [cofreeAct, uncurry_curry]

/-- The `A`-module structure on `[A, Y]`. -/
@[implicit_reducible]
def cofreeModObj (Y : C) : ModObj A ((ihom A).obj Y) :=
  .mk' A (cofreeAct A Y)
    (by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_cofreeAct, uncurry_eq,
        associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, MonObj.mul_one]
      simp)
    (by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_cofreeAct, uncurry_natural_left, uncurry_natural_left,
        uncurry_cofreeAct, associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc]
      have hμ : A ◁ μ ≫ μ = (α_ A A A).inv ≫ μ ▷ A ≫ μ := by
        rw [MonObj.mul_assoc, Iso.inv_hom_id_assoc]
      rw [hμ, associator_inv_naturality_right_assoc, whisker_exchange_assoc, ← uncurry_eq,
        uncurry_cofreeAct]
      simp only [comp_whiskerRight, Category.assoc]
      monoidal)

/-- The action of `A` on `[A, Y]` is natural in `Y`. -/
lemma cofreeAct_natural {Y Y' : C} (f : Y ⟶ Y') :
    cofreeAct A Y ≫ (ihom A).map f = A ◁ (ihom A).map f ≫ cofreeAct A Y' := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_cofreeAct, uncurry_natural_left, uncurry_cofreeAct]
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ihom.ev_naturality]

/-- The cofree `A`-module `[A, Y]` on an object `Y`, right adjoint to the forgetful functor. -/
@[simps]
def cofree : C ⥤ Mod C A where
  obj Y :=
    letI := cofreeModObj A Y
    ⟨(ihom A).obj Y⟩
  map {Y Y'} f :=
    letI := cofreeModObj A Y
    letI := cofreeModObj A Y'
    homMk (M := ⟨(ihom A).obj Y⟩) (N := ⟨(ihom A).obj Y'⟩) ((ihom A).map f)
      (cofreeAct_natural A f)
  map_id _ := Mod.hom_ext _ _ ((ihom A).map_id _)
  map_comp _ _ := Mod.hom_ext _ _ ((ihom A).map_comp _ _)

/-- The action on the cofree module. -/
lemma act_cofree_obj (Y : C) : act ((cofree A).obj Y).X = cofreeAct A Y := rfl

/-- Evaluation at `1`, `[A, Y] ⟶ Y`. -/
def cofreeEval (Y : C) : (ihom A).obj Y ⟶ Y :=
  (λ_ _).inv ≫ η ▷ _ ≫ (ihom.ev A).app Y

/-- Evaluating `a · f` at `1` is evaluating `f` at `a`. -/
lemma cofreeAct_comp_cofreeEval (Y : C) :
    cofreeAct A Y ≫ cofreeEval A Y = (ihom.ev A).app Y := by
  rw [cofreeEval, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, ← uncurry_eq,
    uncurry_cofreeAct, associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc]
  rw [MonObj.one_mul]
  simp


/-- The morphism of modules `P ⟶ [A, Y]` adjoint to `u : P ⟶ Y`, `p ↦ (a ↦ u (a p))`. -/
def toCofree {P : Mod C A} {Y : C} (u : P.X ⟶ Y) : P ⟶ (cofree A).obj Y :=
  homMk (curry (act P.X ≫ u)) (by
    change act P.X ≫ curry (act P.X ≫ u) = A ◁ curry (act P.X ≫ u) ≫ cofreeAct A Y
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left, uncurry_cofreeAct,
      associator_inv_naturality_right_assoc, whisker_exchange_assoc, ← uncurry_eq,
      uncurry_curry, mul_act_assoc, Iso.inv_hom_id_assoc])

/-- The adjunction between the forgetful functor and the cofree module functor. -/
def forgetCofreeAdjunction : forget A ⊣ cofree A :=
  Adjunction.mkOfHomEquiv
    { homEquiv P Y :=
        { toFun u := toCofree A u
          invFun v := v.hom ≫ cofreeEval A Y
          left_inv u := by
            change curry (act P.X ≫ u) ≫ cofreeEval A Y = u
            rw [cofreeEval, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
              ← uncurry_eq, uncurry_curry, one_act_assoc, Iso.inv_hom_id_assoc]
          right_inv v := Mod.hom_ext _ _ (by
            change curry (act P.X ≫ v.hom ≫ cofreeEval A Y) = v.hom
            rw [curry_eq_iff, uncurry_eq, act_hom_assoc]
            exact congrArg _ (cofreeAct_comp_cofreeEval A Y)) }
      homEquiv_naturality_left_symm f g := by
        simp
      homEquiv_naturality_right f g := Mod.hom_ext _ _ (by
        simp [toCofree, curry_natural_right]) }

end CategoryTheory.Mod

namespace CategoryTheory.Mod

open Functor.LaxMonoidal

open scoped Obj

variable {C D : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]
  [Category D] [MonoidalCategory D] [MonoidalClosed D] (A : C) [MonObj A]
  (F : C ⥤ D) [F.LaxMonoidal]

omit [MonoidalClosed C] [MonoidalClosed D] in
/-- The action on the image of a module under a lax monoidal functor. -/
lemma act_mapMod_obj (M : Mod C A) :
    act ((F.mapMod A).obj M).X = Functor.LaxMonoidal.μ F A M.X ≫ F.map (act M.X) := rfl

/-- The image of a cofree module under a lax monoidal functor maps to a cofree module. -/
def mapModCofreeHom (Y : C) :
    (F.mapMod A).obj ((cofree A).obj Y) ⟶ (cofree (F.obj A)).obj (F.obj Y) :=
  homMk ((ihomComparison F A).app Y) (by
    change (Functor.LaxMonoidal.μ F A ((ihom A).obj Y) ≫ F.map (cofreeAct A Y)) ≫
        (ihomComparison F A).app Y =
      F.obj A ◁ (ihomComparison F A).app Y ≫ cofreeAct (F.obj A) (F.obj Y)
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_eq, ihomComparison_ev, uncurry_natural_left,
      uncurry_cofreeAct]
    erw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ihomComparison_ev]
    rw [ MonoidalCategory.whiskerLeft_comp_assoc, μ_natural_right_assoc,
      ← F.map_comp, ← uncurry_eq, uncurry_cofreeAct, Functor.obj.μ_def]
    have hass := Functor.LaxMonoidal.associativity F A A ((ihom A).obj Y)
    rw [← cancel_epi (α_ (F.obj A) (F.obj A) (F.obj ((ihom A).obj Y))).hom]
    rw [← reassoc_of% hass]
    simp only [Functor.map_comp, Category.assoc, comp_whiskerRight]
    rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
    erw [Iso.hom_inv_id_assoc, μ_natural_left_assoc]
    rfl)

end CategoryTheory.Mod

namespace CategoryTheory.Mod

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

/-- A cofree module along an isomorphism of monoids. -/
noncomputable def comapCofreeIso {B B' : C} [MonObj B] [MonObj B'] (f : B ⟶ B') [IsMonHom f]
    [IsIso f]
    (Z : C) : (comap f).obj ((cofree B').obj Z) ≅ (cofree B).obj Z :=
  isoMk (asIso ((pre f).app Z)) (by
    change (f ▷ _ ≫ cofreeAct B' Z) ≫ (pre f).app Z = B ◁ (pre f).app Z ≫ cofreeAct B Z
    apply uncurry_injective
    have h1 : uncurry ((f ▷ _ ≫ cofreeAct B' Z) ≫ (pre f).app Z) =
        (α_ B B _).inv ≫ (μ ≫ f) ▷ _ ≫ (ihom.ev B').app Z := by
      rw [uncurry_pre_app, uncurry_natural_left, uncurry_cofreeAct,
        associator_inv_naturality_middle_assoc, associator_inv_naturality_left_assoc,
        ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, ← tensorHom_def,
        IsMonHom.mul_hom]
    have h2 : uncurry (B ◁ (pre f).app Z ≫ cofreeAct B Z) =
        (α_ B B _).inv ≫ (μ ≫ f) ▷ _ ≫ (ihom.ev B').app Z := by
      rw [uncurry_natural_left, uncurry_cofreeAct, associator_inv_naturality_right_assoc,
        whisker_exchange_assoc, ← uncurry_eq, uncurry_pre, comp_whiskerRight_assoc]
    rw [h1, h2])

end CategoryTheory.Mod

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Mod

open scoped Obj

variable {C D : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]
  [Category D] [MonoidalCategory D] [MonoidalClosed D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]
  {A : C} {B : D} [MonObj A] [MonObj B] (φ : A ⟶ G.obj B) [IsMonHom φ]
  [IsIso ((adj.homEquiv _ _).symm φ)] [IsMonHom ((adj.homEquiv _ _).symm φ)]

/-- If `F` commutes with internal homs out of `A`, the left adjoint on modules sends cofree
`A`-modules to cofree `B`-modules. -/
noncomputable def modLeftCofreeIso [IsIso (Functor.LaxMonoidal.ihomComparison F A)] :
    cofree A ⋙ adj.modLeft φ ≅ F ⋙ cofree B :=
  NatIso.ofComponents (fun Y ↦
    have : IsIso (mapModCofreeHom A F Y) := by
      have : IsIso ((forget _).map (mapModCofreeHom A F Y)) :=
        inferInstanceAs (IsIso ((Functor.LaxMonoidal.ihomComparison F A).app Y))
      exact isIso_of_reflects_iso _ (forget _)
    (comap (inv ((adj.homEquiv _ _).symm φ))).mapIso (asIso (mapModCofreeHom A F Y)) ≪≫
      comapCofreeIso _ (F.obj Y)) (fun {Y Y'} f ↦ Mod.hom_ext _ _ (by
    change F.map ((ihom A).map f) ≫ (Functor.LaxMonoidal.ihomComparison F A).app Y' ≫
        (MonoidalClosed.pre _).app (F.obj Y') =
      ((Functor.LaxMonoidal.ihomComparison F A).app Y ≫
        (MonoidalClosed.pre _).app (F.obj Y)) ≫ (ihom B).map (F.map f)
    have h1 := (Functor.LaxMonoidal.ihomComparison F A).naturality f
    have h2 := (MonoidalClosed.pre (inv ((adj.homEquiv _ _).symm φ))).naturality (F.map f)
    simp only [Functor.comp_map] at h1 h2
    rw [reassoc_of% h1, h2, Category.assoc]))

end CategoryTheory.Adjunction
