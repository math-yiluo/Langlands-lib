/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSemilinearHomology

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The exact homology comparison respects composition and natural transformations. -/
theorem tensorResolution_homology_composition
    {C : Type u} {D : Type v} {E : Type w}
    [Category C] [Category D] [Category E] [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesHomology] [G.PreservesHomology] [H.PreservesHomology]
    (e : F ⋙ G ⟶ H) (S : ShortComplex C) :
    G.map (S.mapHomologyIso F).inv ≫ ((S.map F).mapHomologyIso G).inv ≫
        ShortComplex.homologyMap (S.mapNatTrans e) =
      e.app S.homology ≫ (S.mapHomologyIso H).inv := by
  let h := S.homologyData.left
  let δ : ShortComplex.LeftHomologyMapData (S.mapNatTrans e)
      ((h.map F).map G) (h.map H) :=
    { φK := e.app h.K
      φH := e.app h.H
      commi := by exact (e.naturality h.i).symm
      commf' := by
        simpa only [ShortComplex.LeftHomologyData.map_f', Functor.comp_map,
          ShortComplex.mapNatTrans_τ₁] using e.naturality h.f'
      commπ := by exact e.naturality h.π }
  rw [δ.homologyMap_eq, (h.map F).mapHomologyIso_eq G]
  have hh : h.homologyIso = Iso.refl _ := tensorResolution_chosenHomologyIso S
  have hF : S.mapHomologyIso F = (h.map F).homologyIso := by
    rw [h.mapHomologyIso_eq F, hh]
    ext
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    erw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hH : S.mapHomologyIso H = (h.map H).homologyIso := by
    rw [h.mapHomologyIso_eq H, hh]
    ext
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    erw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  rw [hF, hH]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc]
  rfl

end AlgebraicGeometry
