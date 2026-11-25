/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows

/-!
# Mate coherence from tensor-square coherence

Source: Stacks 07A4, 0D6D and 0E48
(blueprint: lemma-weil-pbc-projection-mate-square-coherence).
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v' u'' v'' u''' v'''

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A tensor square identity implies the corresponding identity for projection mates.
This is the abstract mate calculation used by the concrete pro-etale specialization below.
The proof is the transpose calculation: apply the right adjunction hom-equivalence, use
naturality of the square isomorphism and of all four tensor comparisons, and cancel the
unit and counit by the triangle identities. -/
theorem projectionMate_square_of_tensor_coherence
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D} {K : C ⥤ D} {S : D ⥤ C}
    (adj : F ⊣ R) (adj' : K ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C) (W : D × D ⥤ D)
    (tF : T ⋙ F ⟶ (F.prod F) ⋙ U) (tG : T ⋙ G ⟶ (G.prod G) ⋙ V)
    (tH : U ⋙ H ⟶ (H.prod H) ⋙ W) (tK : V ⋙ K ⟶ (K.prod K) ⋙ W)
    (theta : G ⋙ K ≅ F ⋙ H)
    (hc : ∀ P Q : A,
      theta.hom.app (T.obj (P, Q)) ≫ H.map (tF.app (P, Q)) ≫
        tH.app (F.obj P, F.obj Q) =
      K.map (tG.app (P, Q)) ≫ tK.app (G.obj P, G.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (theta.hom.app P) (theta.hom.app Q)))
    (E : B) (Q : A) :
    G.map (adj.homEquiv _ _ (tF.app (R.obj E, Q) ≫
        U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))))) ≫
      (mateEquiv adj adj' (TwoSquare.mk G F K H theta.hom)).app
        (U.obj (E, F.obj Q)) ≫
      S.map (tH.app (E, F.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (𝟙 (H.obj E)) (theta.inv.app Q))) =
    tG.app (R.obj E, Q) ≫
      V.map (CategoryTheory.Prod.mkHom
        ((mateEquiv adj adj' (TwoSquare.mk G F K H theta.hom)).app E)
        (𝟙 (G.obj Q))) ≫
      adj'.homEquiv _ _ (tK.app (S.obj (H.obj E), G.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (adj'.counit.app (H.obj E))
          (𝟙 (K.obj (G.obj Q))))) := by
  let ex := (mateEquiv adj adj' (TwoSquare.mk G F K H theta.hom))
  let pi := adj.homEquiv _ _ (tF.app (R.obj E, Q) ≫
    U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))))
  have hex (Z : B) : K.map (ex.app Z) ≫ adj'.counit.app (H.obj Z) =
      theta.hom.app (R.obj Z) ≫ H.map (adj.counit.app Z) :=
    mateEquiv_counit adj adj' (TwoSquare.mk G F K H theta.hom) Z
  dsimp only [Functor.id_obj, Functor.comp_obj]
  apply (adj'.homEquiv _ _).symm.injective
  change (adj'.homEquiv _ _).symm (G.map pi ≫ ex.app _ ≫ S.map _) = _
  rw [adj'.homEquiv_naturality_left_symm,
    adj'.homEquiv_naturality_right_symm]
  rw [adj'.homEquiv_counit, hex]
  simp only [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  have hn := theta.hom.naturality pi
  dsimp at hn
  dsimp only [Functor.id_obj] at *
  simp only [← Category.assoc]
  rw [hn]
  have hpi : F.map pi ≫ adj.counit.app (U.obj (E, F.obj Q)) =
      tF.app (R.obj E, Q) ≫
        U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))) := by
    exact (adj.homEquiv _ _).symm_apply_apply _
  simp only [Category.assoc]
  rw [← H.map_comp_assoc, hpi, H.map_comp, Category.assoc]
  have htH := tH.naturality
    (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))
  have htK := tK.naturality
    (CategoryTheory.Prod.mkHom (ex.app E) (𝟙 (G.obj Q)))
  dsimp at htH htK
  rw [reassoc_of% htH, reassoc_of% htK]
  rw [reassoc_of% (hc (R.obj E) Q)]
  simp only [← W.map_comp]
  congr 2
  congr 1
  ext
  · simpa using (hex E).symm
  · simp

end CategoryTheory

namespace CategoryTheory

/-- The mate coherence identity in the right-adjoint projection-map presentation. -/
theorem projectionMate_square_of_tensor_coherence_projection
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D} {K : C ⥤ D} {S : D ⥤ C}
    (adj : F ⊣ R) (adj' : K ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C) (W : D × D ⥤ D)
    (tF : T ⋙ F ≅ (F.prod F) ⋙ U) (tG : T ⋙ G ⟶ (G.prod G) ⋙ V)
    (tH : U ⋙ H ⟶ (H.prod H) ⋙ W) (tK : V ⋙ K ≅ (K.prod K) ⋙ W)
    (theta : G ⋙ K ≅ F ⋙ H)
    (hc : ∀ P Q : A,
      theta.hom.app (T.obj (P, Q)) ≫ H.map (tF.hom.app (P, Q)) ≫
        tH.app (F.obj P, F.obj Q) =
      K.map (tG.app (P, Q)) ≫ tK.hom.app (G.obj P, G.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (theta.hom.app P) (theta.hom.app Q)))
    (E : B) (Q : A) :
    G.map (derivedProjectionFormulaMate F R adj T U
      tF E Q) ≫
      (mateEquiv adj adj' (TwoSquare.mk G F K H theta.hom)).app (U.obj (E, F.obj Q)) ≫
      S.map (tH.app (E, F.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (𝟙 (H.obj E)) (theta.inv.app Q))) =
    tG.app (R.obj E, Q) ≫
      V.map (CategoryTheory.Prod.mkHom
        ((mateEquiv adj adj' (TwoSquare.mk G F K H theta.hom)).app E) (𝟙 (G.obj Q))) ≫
      derivedProjectionFormulaMate K S adj' V W tK (H.obj E) (G.obj Q) := by
  simpa [derivedProjectionFormulaMate,
    CategoryTheory.Adjunction.rightAdjointProjectionMap_app_app,
    Functor.curry, Functor.curryObj, Functor.curry_obj_obj_obj,
    Functor.curry_obj_map_app, Functor.curry_map_app_app, Functor.curryObjProdComp_hom_app_app,
    NatTrans.comp_app, Iso.trans_hom, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Functor.map_comp, Functor.map_id, Category.comp_id, Category.id_comp] using
    projectionMate_square_of_tensor_coherence adj adj' T U V W tF.hom tG tH tK.hom theta hc E Q

end CategoryTheory
