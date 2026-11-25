/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.MapBijectiveAcyclic

/-!
# Sections of sheaves of modules and of their underlying abelian sheaves

Let `T` be a terminal object of a site, `Λ` a ring and `Λ_X`, `ℤ_X` the constant sheaves. For a
sheaf `Y` of `Λ`-modules, morphisms `Λ_X ⟶ Y` and morphisms `ℤ_X ⟶ Y` of abelian sheaves are
both the global sections `Y(T)`. The class `u : ℤ_X ⟶ Λ_X` of `1 ∈ Λ` identifies them:
`f ↦ u ≫ f` is bijective (`CategoryTheory.Sheaf.bijective_comp_forget₂_map`).

Together with `CategoryTheory.Functor.bijective_mapExtComp` this identifies `Ext^n(Λ_X, Y)`
(cohomology computed with sheaves of `Λ`-modules) with `Hⁿ(Y)` (cohomology of the underlying
abelian sheaf) as soon as injective sheaves of `Λ`-modules are acyclic as abelian sheaves.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory.Sheaf

section constantHomEquiv

variable {C : Type*} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] {T : C} (hT : IsTerminal T)

/-- Morphisms out of the constant sheaf `ℤ` are global sections: the value at `1` over the
terminal object. -/
noncomputable def constantHomEquiv (F : Sheaf J AddCommGrpCat.{w}) :
    ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) ≃
      F.obj.obj (op T) :=
  ((constantSheafAdj J AddCommGrpCat.{w} hT).homEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv

lemma constantHomEquiv_comp {F G : Sheaf J AddCommGrpCat.{w}}
    (f : (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F)
    (g : F ⟶ G) :
    constantHomEquiv hT G (f ≫ g) = g.hom.app (op T) (constantHomEquiv hT F f) := by
  simp only [constantHomEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    Adjunction.homEquiv_naturality_right]
  rfl

lemma constantHomEquiv_naturality {F : Sheaf J AddCommGrpCat.{w}}
    (f : (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) {W : C}
    (ρ : W ⟶ T) :
    f.hom.app (op W) (((constantSheaf J AddCommGrpCat.{w}).obj
        (AddCommGrpCat.of (ULift ℤ))).obj.map ρ.op
          (constantHomEquiv hT _ (𝟙 _))) =
      F.obj.map ρ.op (constantHomEquiv hT F f) := by
  rw [← ConcreteCategory.comp_apply, f.hom.naturality, ConcreteCategory.comp_apply,
    ← constantHomEquiv_comp, Category.id_comp]

end constantHomEquiv

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {T : C} (hT : IsTerminal T)
  (Λ : Type w) [CommRing Λ] [HasWeakSheafify J (ModuleCat.{w} Λ)]
  [HasSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- The forgetful functor from sheaves of `Λ`-modules to abelian sheaves. -/
noncomputable abbrev forget₂Module :
    Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J AddCommGrpCat.{w} :=
  sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})

/-- The constant sheaf `Λ_X`. -/
noncomputable abbrev constantRing : Sheaf J (ModuleCat.{w} Λ) :=
  (constantSheaf J (ModuleCat.{w} Λ)).obj (ModuleCat.of Λ Λ)

/-- The constant sheaf `ℤ_X`. -/
noncomputable abbrev constantInt : Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

/-- Morphisms `Λ_X ⟶ Y` are the global sections of `Y`. -/
noncomputable def constantRingHomEquiv (Y : Sheaf J (ModuleCat.{w} Λ)) :
    (constantRing J Λ ⟶ Y) ≃ Y.obj.obj (op T) :=
  ((constantSheafAdj J (ModuleCat.{w} Λ) hT).homEquiv _ _).trans
    (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf Λ Λ _).toEquiv)

omit [HasSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})] in
lemma constantRingHomEquiv_comp {Y Y' : Sheaf J (ModuleCat.{w} Λ)} (f : constantRing J Λ ⟶ Y)
    (g : Y ⟶ Y') :
    constantRingHomEquiv J hT Λ Y' (f ≫ g) =
      g.hom.app (op T) (constantRingHomEquiv J hT Λ Y f) := by
  rw [constantRingHomEquiv, Equiv.trans_apply, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_right]
  rfl

/-- The class `u : ℤ_X ⟶ Λ_X` of the global section `1`. -/
noncomputable def constantIntToRing : constantInt J ⟶ (forget₂Module J Λ).obj (constantRing J Λ) :=
  (constantHomEquiv hT _).symm (constantRingHomEquiv J hT Λ _ (𝟙 _))

/-- **Morphisms out of `Λ_X` are morphisms out of `ℤ_X`.** For a sheaf `Y` of `Λ`-modules,
`f ↦ u ≫ f`, `Hom(Λ_X, Y) ⟶ Hom(ℤ_X, Y)`, is bijective: both are the global sections of `Y`. -/
theorem bijective_comp_forget₂_map (Y : Sheaf J (ModuleCat.{w} Λ)) :
    Function.Bijective fun f : constantRing J Λ ⟶ Y ↦
      constantIntToRing J hT Λ ≫ (forget₂Module J Λ).map f := by
  have key : (fun f : constantRing J Λ ⟶ Y ↦
      constantIntToRing J hT Λ ≫ (forget₂Module J Λ).map f) =
      (constantHomEquiv hT _).symm ∘ (constantRingHomEquiv J hT Λ Y) := by
    funext f
    refine (constantHomEquiv hT _).injective ?_
    rw [Function.comp_apply, Equiv.apply_symm_apply, constantHomEquiv_comp, constantIntToRing,
      Equiv.apply_symm_apply]
    conv_rhs => rw [← Category.id_comp f, constantRingHomEquiv_comp]
    rfl
  rw [key]
  exact (constantHomEquiv hT _).symm.bijective.comp (constantRingHomEquiv J hT Λ Y).bijective

end CategoryTheory.Sheaf
