/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Naturality of `H^n(RF(X[0])) ≅ RⁿF X`

The identification `Functor.homologyRightDerivedFunctorObjSingleFunctorIso` of the homology of
the unbounded total right derived functor applied to an object placed in degree `0` with the
classical right derived functor is natural in the object
(`CategoryTheory.Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso`).
-/

@[expose] public section

open CategoryTheory Abelian Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C] [HasKInjectiveResolutions C]

/-- The isomorphism `H^n(RF(X[0])) ≅ RⁿF X` is natural in `X`: it is the composite of the
compatibility of `RF` with `R⁺F`, a natural isomorphism, and the natural isomorphism
`H^n(R⁺F(X[0])) ≅ RⁿF X`. -/
@[reassoc]
lemma homologyRightDerivedFunctorObjSingleFunctorIso_hom_naturality {X Y : C} (f : X ⟶ Y)
    (n : ℕ) :
    (DerivedCategory.homologyFunctor D n).map
        (F.rightDerivedFunctor.map ((DerivedCategory.singleFunctor C 0).map f)) ≫
      (F.homologyRightDerivedFunctorObjSingleFunctorIso Y n).hom =
    (F.homologyRightDerivedFunctorObjSingleFunctorIso X n).hom ≫ (F.rightDerived n).map f := by
  have h := F.rightDerivedFunctorPlusCompatibility.inv.naturality
    ((DerivedCategory.Plus.singleFunctor C 0).map f)
  have h' := F.homologyRightDerivedFunctorPlusObjSingleFunctorIso_hom_naturality f n
  simp only [homologyRightDerivedFunctorObjSingleFunctorIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [← h', ← Functor.map_comp_assoc]
  erw [h]
  rw [Functor.map_comp_assoc]
  rfl

/-- The natural isomorphism `H^n(RF(X[0])) ≅ RⁿF X` of functors `C ⥤ D`. -/
noncomputable def singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso (n : ℕ) :
    DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor D n ≅ F.rightDerived n :=
  NatIso.ofComponents (fun X ↦ F.homologyRightDerivedFunctorObjSingleFunctorIso X n)
    fun f ↦ F.homologyRightDerivedFunctorObjSingleFunctorIso_hom_naturality f n

end CategoryTheory.Functor
