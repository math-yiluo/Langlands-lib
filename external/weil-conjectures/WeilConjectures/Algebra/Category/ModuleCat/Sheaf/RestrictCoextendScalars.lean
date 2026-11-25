/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-!
# The unit and counit of restriction and coextension of scalars for sheaves

The adjunction `CategoryTheory.Sheaf.restrictCoextendScalarsAdj` between restriction and
coextension of scalars of sheaves of modules over a constant ring is computed sectionwise: its
unit and counit are given on sections by the unit and counit of
`ModuleCat.restrictCoextendScalarsAdj`.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)

/-- The unit of `res ⊣ coext` on sheaves is computed sectionwise. -/
lemma restrictCoextendScalarsAdj_unit_app_hom_app (G : Sheaf J (ModuleCat.{w} S)) (U : Cᵒᵖ) :
    ((restrictCoextendScalarsAdj J f).unit.app G).hom.app U =
      (ModuleCat.restrictCoextendScalarsAdj f).unit.app (G.obj.obj U) := by
  have h := congr_app (Adjunction.map_restrictFullyFaithful_unit_app (L := restrictScalars J f)
    (R := sheafCompose J (ModuleCat.coextendScalars f))
    ((ModuleCat.restrictCoextendScalarsAdj f).whiskerRight Cᵒᵖ)
    (fullyFaithfulSheafToPresheaf J _) (fullyFaithfulSheafToPresheaf J _) (Iso.refl _)
    (Iso.refl _) G) U
  rw [restrictCoextendScalarsAdj]
  simpa using h

/-- The counit of `res ⊣ coext` on sheaves is computed sectionwise. -/
lemma restrictCoextendScalarsAdj_counit_app_hom_app (G : Sheaf J (ModuleCat.{w} R)) (U : Cᵒᵖ) :
    ((restrictCoextendScalarsAdj J f).counit.app G).hom.app U =
      (ModuleCat.restrictCoextendScalarsAdj f).counit.app (G.obj.obj U) := by
  have h := congr_app (Adjunction.map_restrictFullyFaithful_counit_app (L := restrictScalars J f)
    (R := sheafCompose J (ModuleCat.coextendScalars f))
    ((ModuleCat.restrictCoextendScalarsAdj f).whiskerRight Cᵒᵖ)
    (fullyFaithfulSheafToPresheaf J _) (fullyFaithfulSheafToPresheaf J _) (Iso.refl _)
    (Iso.refl _) G) U
  rw [restrictCoextendScalarsAdj]
  refine h.trans ?_
  dsimp
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

end CategoryTheory.Sheaf
