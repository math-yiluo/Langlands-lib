/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionLocalData
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionLocalTensorSquare

/-! # Canonical projection-formula models

## References

* Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6
* Stacks Project, Tags 04J0, 08FI, 0FN5, 07A4 and 0B56
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

/-- The uncurried projection map is the adjunct of tensor comparison and counit. -/
private theorem projection_eq
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (t : T ⋙ L ≅ (L.prod L) ⋙ U) (E : B) (P : A) :
    derivedProjectionFormulaMate L R adj T U t E P =
      adj.homEquiv _ _ (t.hom.app (R.obj E, P) ≫
        U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (L.obj P)))) := by
  simp [derivedProjectionFormulaMate, Adjunction.rightAdjointProjectionMap_app_app]

/-- The counit mate equation and a tensor square imply projection compatibility. -/
private theorem projection_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D} {K : C ⥤ D} {S : D ⥤ C}
    (adj : F ⊣ R) (adj' : K ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C) (W : D × D ⥤ D)
    (tF : T ⋙ F ≅ (F.prod F) ⋙ U) (tG : T ⋙ G ≅ (G.prod G) ⋙ V)
    (tH : U ⋙ H ≅ (H.prod H) ⋙ W) (tK : V ⋙ K ≅ (K.prod K) ⋙ W)
    (theta : G ⋙ K ≅ F ⋙ H) (beta : R ⋙ G ⟶ H ⋙ S)
    (hb : ∀ Z : B, K.map (beta.app Z) ≫ adj'.counit.app (H.obj Z) =
      theta.hom.app (R.obj Z) ≫ H.map (adj.counit.app Z))
    (hc : ∀ P Q : A,
      theta.hom.app (T.obj (P, Q)) ≫ H.map (tF.hom.app (P, Q)) ≫
        tH.hom.app (F.obj P, F.obj Q) =
      K.map (tG.hom.app (P, Q)) ≫ tK.hom.app (G.obj P, G.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (theta.hom.app P) (theta.hom.app Q)))
    (E : B) (Q : A) :
    G.map (derivedProjectionFormulaMate F R adj T U tF E Q) ≫
        beta.app (U.obj (E, F.obj Q)) ≫
        S.map (tH.hom.app (E, F.obj Q) ≫
          W.map (CategoryTheory.Prod.mkHom (𝟙 (H.obj E)) (theta.inv.app Q))) =
      tG.hom.app (R.obj E, Q) ≫
        V.map (CategoryTheory.Prod.mkHom (beta.app E) (𝟙 (G.obj Q))) ≫
        derivedProjectionFormulaMate K S adj' V W tK (H.obj E) (G.obj Q) := by
  rw [projection_eq, projection_eq]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  let pi := adj.homEquiv _ _ (tF.hom.app (R.obj E, Q) ≫
    U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))))
  apply (adj'.homEquiv _ _).symm.injective
  change (adj'.homEquiv _ _).symm (G.map pi ≫ beta.app _ ≫ S.map _) = _
  rw [adj'.homEquiv_naturality_left_symm,
    adj'.homEquiv_naturality_right_symm]
  rw [adj'.homEquiv_counit, hb]
  simp only [Functor.id_obj, Functor.comp_obj,
    Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  have hn := theta.hom.naturality pi
  dsimp at hn
  dsimp only [Functor.id_obj] at *
  simp only [← Category.assoc]
  rw [hn]
  have hpi : F.map pi ≫ adj.counit.app (U.obj (E, F.obj Q)) =
      tF.hom.app (R.obj E, Q) ≫
        U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))) :=
    (adj.homEquiv _ _).symm_apply_apply _
  simp only [Category.assoc]
  rw [← H.map_comp_assoc, hpi, H.map_comp, Category.assoc]
  have htH := tH.hom.naturality
    (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))
  have htK := tK.hom.naturality
    (CategoryTheory.Prod.mkHom (beta.app E) (𝟙 (G.obj Q)))
  dsimp at htH htK
  rw [reassoc_of% htH, reassoc_of% htK]
  rw [reassoc_of% (hc (R.obj E) Q)]
  simp only [← W.map_comp]
  congr 2
  congr 1
  ext
  · simpa using (hb E).symm
  · simp

/-- A normalized global projection package admits compatible localization at any object. -/
theorem localModel_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (g : Global f R_Y R_X c) (V : Y.ProEt) :
    ∃ l : Local f R_Y R_X c g V, l.ProjectionCompatible := by
  obtain ⟨l⟩ := localData_exists f R_Y R_X c g V
  refine ⟨l, ?_⟩
  let := l.restrictionYAdditive
  let := l.restrictionXAdditive
  intro E P
  simpa only [Local.sourceIso, Local.targetIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.mapIso_hom, CategoryTheory.Iso.prod_hom, Iso.refl_hom, Iso.app_hom,
    Iso.symm_inv, Functor.comp_obj, Category.assoc] using
    projection_square g.operation.derivedAdjunction l.operation.derivedAdjunction
      g.tensorY.functor g.tensorX.functor l.tensorY.functor l.tensorX.functor
      g.tensorComparison.comparison l.restrictionTensorY.comparison
      l.restrictionTensorX.comparison l.tensorComparison.comparison
      l.pullback.symm l.directImage.hom l.mate_counit
      (localTensorSquare f R_Y R_X c g V l) E P

end AlgebraicGeometry.Scheme.ProjectionRestriction
