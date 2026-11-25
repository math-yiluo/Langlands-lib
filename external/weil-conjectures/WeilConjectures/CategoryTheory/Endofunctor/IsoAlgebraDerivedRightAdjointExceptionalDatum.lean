/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointWeilDatum
public import WeilConjectures.CategoryTheory.WeilEquivariance

/-!
# The Weil structure of a derived right adjoint is the right Weil datum

In the setting of `CategoryTheory.Endofunctor.IsoAlgebra.exists_forget_obj_iso_counit_comm`
(a right derived functor `RL` with right adjoint `R'` on full subcategories, lifted to Weil
objects), the exchange `RL ⋙ G ≅ F ⋙ RL` restricts to the full subcategories
(`CategoryTheory.Endofunctor.IsoAlgebra.liftedDerivedCommIso`), so that the *right Weil datum*
`CategoryTheory.Adjunction.rightWeilDatum` of the structure of `L'` is a Weil datum on `R' Y`
for which the counit is equivariant (`CategoryTheory.Adjunction.isWeilEquivariant_counit`). By
uniqueness it is the Weil structure of `RW L'`, read through the comparison `θ : U (RW L') ≅ R' Y`
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_forget_obj_iso_isWeilEquivariant_rightWeilDatum`).
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v'

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C]

omit [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)] in
/-- The exchange `RL ⋙ G ≅ F ⋙ RL` restricted to the full subcategories `P_C`, `P_D`. -/
def liftedDerivedCommIso (PC : ObjectProperty (DerivedCategory C))
    (PD : ObjectProperty (DerivedCategory D))
    (hPC_F : ∀ K, PC (F.mapDerivedCategory.obj K) ↔ PC K)
    (hPD_G : ∀ K, PD K → PD (G.mapDerivedCategory.obj K))
    (hR : ∀ K, PC K → PD (L.rightDerivedFunctor.obj K)) :
    PC.liftFullSubcategory PD L.rightDerivedFunctor hR ⋙
        PD.liftFullSubcategory PD G.mapDerivedCategory hPD_G ≅
      PC.liftFullSubcategory PC F.mapDerivedCategory (fun K hK ↦ (hPC_F K).2 hK) ⋙
        PC.liftFullSubcategory PD L.rightDerivedFunctor hR :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ ((derivedCommIso e).app K.obj))
    (fun f ↦ ObjectProperty.hom_ext _ ((derivedCommIso e).hom.naturality f.hom))

omit [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)] in
@[simp]
lemma liftedDerivedCommIso_hom_app_hom (PC : ObjectProperty (DerivedCategory C))
    (PD : ObjectProperty (DerivedCategory D))
    (hPC_F : ∀ K, PC (F.mapDerivedCategory.obj K) ↔ PC K)
    (hPD_G : ∀ K, PD K → PD (G.mapDerivedCategory.obj K))
    (hR : ∀ K, PC K → PD (L.rightDerivedFunctor.obj K)) (K : PC.FullSubcategory) :
    ((liftedDerivedCommIso e PC PD hPC_F hPD_G hR).hom.app K).hom =
      (derivedCommIso e).hom.app K.obj :=
  rfl

/-- **The Weil structure of a right adjoint of Weil complexes is the right Weil datum.** In the
setting of `exists_forget_obj_iso_counit_comm`, the comparison `θ : U (RW L') ≅ R' Y` is
equivariant for the derived structure isomorphism of `RW L'` and the right Weil datum
(`CategoryTheory.Adjunction.rightWeilDatum`) on `R' Y` of the structure of `L'`, for the
adjunction `RL ⊣ R'` and the exchange `RL ⋙ G ≅ F ⋙ RL`. -/
theorem exists_forget_obj_iso_isWeilEquivariant_rightWeilDatum
    (PC : ObjectProperty (DerivedCategory C)) (PD : ObjectProperty (DerivedCategory D))
    [PC.IsClosedUnderIsomorphisms] [PD.IsClosedUnderIsomorphisms]
    (hPC : ∀ K, PC K → DerivedCategory.TStructure.t.bounded K)
    (hPC_shift : ∀ (K : DerivedCategory C) (n : ℤ), PC K → PC (K⟦n⟧))
    (hPC_F : ∀ K, PC (F.mapDerivedCategory.obj K) ↔ PC K)
    (hPD_G : ∀ K, PD K → PD (G.mapDerivedCategory.obj K))
    (hR : ∀ K, PC K → PD (L.rightDerivedFunctor.obj K))
    {R' : PD.FullSubcategory ⥤ PC.FullSubcategory}
    (adj : PC.liftFullSubcategory PD L.rightDerivedFunctor hR ⊣ R')
    (hcoprod : ∀ (X : ℤ → DerivedCategory C) (a : ℤ), (∀ n, (X n).IsGE a) →
      PreservesColimit (Discrete.functor X) L.rightDerivedFunctor)
    (PCW : ObjectProperty (DerivedCategory (IsoAlgebra F)))
    (PDW : ObjectProperty (DerivedCategory (IsoAlgebra G)))
    (hPCW : ∀ M, PCW M ↔ PC ((forget F).mapDerivedCategory.obj M))
    (hPDW : ∀ M, PDW M ↔ PD ((forget G).mapDerivedCategory.obj M))
    (hRW : ∀ M, PCW M → PDW ((mapOfNatIso e).rightDerivedFunctor.obj M))
    {RW : PDW.FullSubcategory ⥤ PCW.FullSubcategory}
    (adjW : PCW.liftFullSubcategory PDW (mapOfNatIso e).rightDerivedFunctor hRW ⊣ RW)
    (L' : PDW.FullSubcategory) :
    ∃ θ : (forget F).mapDerivedCategory.obj (RW.obj L').obj ≅
        (R'.obj ⟨(forget G).mapDerivedCategory.obj L'.obj, (hPDW _).1 L'.property⟩).obj,
      IsWeilEquivariant F.mapDerivedCategory ((derivedStrIso F).hom.app (RW.obj L').obj)
        (Adjunction.rightWeilDatum adj (liftedDerivedCommIso e PC PD hPC_F hPD_G hR)
          (ObjectProperty.homMk
            (X := (PD.liftFullSubcategory PD G.mapDerivedCategory hPD_G).obj
              ⟨(forget G).mapDerivedCategory.obj L'.obj, (hPDW _).1 L'.property⟩)
            (Y := ⟨(forget G).mapDerivedCategory.obj L'.obj, (hPDW _).1 L'.property⟩)
            ((derivedStrIso G).hom.app L'.obj))).hom θ.hom := by
  obtain ⟨θ, -, hb⟩ := exists_forget_obj_iso_counit_comm e PC PD hPC hPC_shift hPC_F hPD_G hR
    adj hcoprod PCW PDW hPCW hPDW hRW adjW L'
  refine ⟨θ, ?_⟩
  set Y : PD.FullSubcategory :=
    ⟨(forget G).mapDerivedCategory.obj L'.obj, (hPDW _).1 L'.property⟩ with hY
  have h := adj.isWeilEquivariant_counit (liftedDerivedCommIso e PC PD hPC_F hPD_G hR)
    (ObjectProperty.homMk (X := (PD.liftFullSubcategory PD G.mapDerivedCategory hPD_G).obj Y)
      (Y := Y) ((derivedStrIso G).hom.app L'.obj))
  have h' : G.mapDerivedCategory.map (adj.counit.app Y).hom ≫ (derivedStrIso G).hom.app L'.obj =
      ((derivedCommIso e).hom.app (R'.obj Y).obj ≫
        L.rightDerivedFunctor.map
          (Adjunction.rightWeilDatum adj (liftedDerivedCommIso e PC PD hPC_F hPD_G hR)
            (ObjectProperty.homMk
              (X := (PD.liftFullSubcategory PD G.mapDerivedCategory hPD_G).obj Y) (Y := Y)
              ((derivedStrIso G).hom.app L'.obj))).hom) ≫
        (adj.counit.app Y).hom :=
    congrArg InducedCategory.Hom.hom h
  unfold IsWeilEquivariant
  exact hb _ (by rw [h', Category.assoc])

end CategoryTheory.Endofunctor.IsoAlgebra
