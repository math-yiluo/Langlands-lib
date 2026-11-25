/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.DimensionShifting
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Sheaf cohomology as the right derived functors of global sections

For a site `(C, J)` with a terminal object `T`, the `Ext`-groups
`Hᵠ(F) = Extᵠ(ℤ, F)` (`CategoryTheory.Sheaf.H`) of an abelian sheaf `F` are the right derived
functors of the global sections functor `F ↦ F(T)`
(`CategoryTheory.Sheaf.nonempty_rightDerived_sections_iso_functorH`): both are cohomological
δ-functors which agree in degree zero and are effaceable, so dimension shifting
(`CategoryTheory.ObjectProperty.nonempty_iso_of_connecting`) identifies them.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

/-- The isomorphism between right derived functors induced by an isomorphism of functors. -/
@[simps]
noncomputable def NatIso.rightDerived {C D : Type*} [Category C] [Category D] [Abelian C]
    [HasInjectiveResolutions C] [Abelian D] {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})] {T : C}

/-- The global sections functor `F ↦ F(T)` on abelian sheaves, for an object `T` of the site
(typically a terminal object). -/
noncomputable abbrev Sheaf.sectionsFunctorAt (T : C) :
    Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op T)

/-- **Sheaf cohomology is the right derived functor of global sections.** On a site with a
terminal object `T`, the functors `F ↦ Rᵠ(Γ(T, -))(F)` and `F ↦ Hᵠ(F)` are isomorphic. -/
theorem Sheaf.nonempty_rightDerived_sections_iso_functorH (hT : IsTerminal T) (q : ℕ) :
    Nonempty ((⊤ : ObjectProperty (Sheaf J AddCommGrpCat.{w})).ι ⋙
        (Sheaf.sectionsFunctorAt J T).rightDerived q ≅
      (⊤ : ObjectProperty (Sheaf J AddCommGrpCat.{w})).ι ⋙ Sheaf.functorH.{w} J q) := by
  let := HasDerivedCategory.standard (Sheaf J AddCommGrpCat.{w})
  let := HasDerivedCategory.standard AddCommGrpCat.{w}
  let Γ := Sheaf.sectionsFunctorAt J T
  refine (⊤ : ObjectProperty (Sheaf J AddCommGrpCat.{w})).nonempty_iso_of_connecting
    (fun _ _ ↦ ⟨trivial, trivial⟩)
    (fun q ↦ Γ.rightDerived q) (fun q ↦ Sheaf.functorH.{w} J q)
    (fun S hS _ q ↦ hS.rightDerivedδ Γ q) (fun S hS _ q ↦ Sheaf.functorHδ hS q)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ q
  · intro S₁ S₂ φ h₁ h₂ _ _ q
    exact ShortComplex.ShortExact.rightDerivedδ_naturality Γ h₁ h₂ φ q
  · intro S₁ S₂ φ h₁ h₂ _ _ q
    exact Sheaf.functorHδ_naturality h₁ q h₂ φ
  · intro S hS _ q x
    have h := (ShortComplex.ab_exact_iff _).1 (hS.rightDerivedδ_exact₂ Γ q)
    refine ⟨fun hx ↦ h x hx, ?_⟩
    rintro ⟨y, rfl⟩
    change ((Γ.rightDerived q).map S.g ≫ hS.rightDerivedδ Γ q) y = 0
    rw [hS.comp_rightDerivedδ Γ q]
    rfl
  · intro S hS _ q x
    exact Sheaf.functorHδ_eq_zero_iff hS q x
  · intro S hS _ q hinj y
    have h := (ShortComplex.ab_exact_iff _).1 (hS.rightDerivedδ_exact₃ Γ q)
    have hz : IsZero ((Γ.rightDerived (q + 1)).obj S.X₂) :=
      Γ.isZero_rightDerived_obj_injective_succ q S.X₂
    exact h y ((AddCommGrpCat.isZero_iff_subsingleton.1 hz).elim _ _)
  · intro S hS _ q hinj
    have : Subsingleton (Sheaf.H S.X₂ (q + 1)) := Abelian.Ext.subsingleton_of_injective _ _ _
    exact Sheaf.functorHδ_surjective hS q
  · exact Functor.isoWhiskerLeft _ (Γ.rightDerivedZeroIsoSelf ≪≫ (Sheaf.functorHZeroIso J hT).symm)

/-- **Sheaf cohomology is the right derived functor of global sections**, objectwise: on a site
with a terminal object `T`, `Rᵠ(Γ(T, -))(F) ≅ Hᵠ(F)` for every abelian sheaf `F`. -/
theorem Sheaf.nonempty_rightDerived_sections_obj_iso_functorH (hT : IsTerminal T) (q : ℕ)
    (F : Sheaf J AddCommGrpCat.{w}) :
    Nonempty (((Sheaf.sectionsFunctorAt J T).rightDerived q).obj F ≅
      (Sheaf.functorH.{w} J q).obj F) :=
  ⟨((Sheaf.nonempty_rightDerived_sections_iso_functorH J hT q).some.app ⟨F, trivial⟩)⟩

/-- On a site with a terminal object `T`, `Hᵠ(F)` vanishes if and only if
`Rᵠ(Γ(T, -))(F)` does. -/
theorem Sheaf.subsingleton_H_iff_isZero_rightDerived (hT : IsTerminal T) (q : ℕ)
    (F : Sheaf J AddCommGrpCat.{w}) :
    Subsingleton (Sheaf.H F q) ↔
      IsZero (((Sheaf.sectionsFunctorAt J T).rightDerived q).obj F) := by
  obtain ⟨e⟩ := Sheaf.nonempty_rightDerived_sections_obj_iso_functorH J hT q F
  rw [e.isZero_iff, AddCommGrpCat.isZero_iff_subsingleton]
  rfl

end CategoryTheory
