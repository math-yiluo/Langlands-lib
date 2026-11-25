/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-!
# The isomorphisms between functors induced on derived categories commute with shifts

For exact functors between abelian categories, the isomorphisms
`Functor.mapDerivedCategoryNatIso e : D(F) ≅ D(G)` and
`Functor.mapDerivedCategoryCompIso F G : D(F ⋙ G) ≅ D(F) ⋙ D(G)` commute with the shifts.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

instance commShift_mapDerivedCategoryNatIso_hom {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    NatTrans.CommShift (mapDerivedCategoryNatIso e).hom ℤ := by
  have eq : whiskerLeft DerivedCategory.Qh (mapDerivedCategoryNatIso e).hom =
      F.mapDerivedCategoryFactorsh.hom ≫
        whiskerRight (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ G.mapDerivedCategoryFactorsh.inv := by
    ext K
    dsimp
    rw [← mapDerivedCategoryNatIso_fach_assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have : NatTrans.CommShift (whiskerLeft DerivedCategory.Qh
      (mapDerivedCategoryNatIso e).hom) ℤ := by
    rw [eq]; infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)

instance commShift_mapDerivedCategoryCompIso_hom (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    NatTrans.CommShift (mapDerivedCategoryCompIso F G).hom ℤ := by
  infer_instance

end CategoryTheory.Functor
