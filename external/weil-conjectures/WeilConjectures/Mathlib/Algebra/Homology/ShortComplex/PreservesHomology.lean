/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Coherence of the isomorphisms `ShortComplex.mapHomologyIso`

For a functor `F` preserving the left homology of a short complex `S`, Mathlib provides the
canonical isomorphisms `S.mapCyclesIso F : (S.map F).cycles ≅ F.obj S.cycles` and
`S.mapHomologyIso F : (S.map F).homology ≅ F.obj S.homology`. In this file we show that
these isomorphisms are natural in the functor `F` (`ShortComplex.mapCyclesIso_hom_comp_app`,
`ShortComplex.mapHomologyIso_hom_comp_app`) and compatible with the composition of functors
(`ShortComplex.mapCyclesIso_comp_hom`, `ShortComplex.mapHomologyIso_comp_hom`).

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
  (S : ShortComplex C)

section

variable (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of `S.mapCyclesIso F` is compatible with the inclusions of the cycles. -/
@[reassoc (attr := simp)]
lemma mapCyclesIso_inv_iCycles [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  rw [Iso.inv_comp_eq, mapCyclesIso_hom_iCycles]

set_option backward.isDefEq.respectTransparency false in
/-- When `F` preserves the left homology of `S`, the image by `F` of the inclusion of the
cycles of `S` is a monomorphism. -/
instance mono_map_iCycles [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    Mono (F.map S.iCycles) := by
  rw [← mapCyclesIso_inv_iCycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `S.mapHomologyIso F` is characterized by its compatibility with the
projections from the cycles and with `S.mapCyclesIso F`. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_mapHomologyIso_hom [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [LeftHomologyData.mapHomologyIso_eq S.leftHomologyData,
    LeftHomologyData.mapCyclesIso_eq S.leftHomologyData]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc, assoc]
  rw [← F.map_comp, ← LeftHomologyData.π_comp_homologyIso_inv, F.map_comp]
  rfl

end

section NatTrans

variable {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `S.mapCyclesIso F` is natural in the functor `F`. -/
@[reassoc]
lemma mapCyclesIso_hom_comp_app [S.HasLeftHomology] [(S.map F).HasLeftHomology]
    [(S.map G).HasLeftHomology] [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).hom ≫ τ.app S.cycles =
      cyclesMap (S.mapNatTrans τ) ≫ (S.mapCyclesIso G).hom := by
  rw [← cancel_mono (S.mapCyclesIso G).inv, assoc, assoc, Iso.hom_inv_id, comp_id,
    ← cancel_mono (S.map G).iCycles, assoc, assoc, mapCyclesIso_inv_iCycles, ← τ.naturality,
    mapCyclesIso_hom_iCycles_assoc, cyclesMap_i, mapNatTrans_τ₂]

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `S.mapHomologyIso F` is natural in the functor `F`. This strengthens Mathlib's
`ShortComplex.homologyMap_mapNatTrans` (and `NatTrans.app_homology`) by only assuming that `F`
and `G` preserve the left homology of `S`. -/
@[reassoc]
lemma mapHomologyIso_hom_comp_app [S.HasHomology] [(S.map F).HasHomology]
    [(S.map G).HasHomology] [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S] :
    (S.mapHomologyIso F).hom ≫ τ.app S.homology =
      homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso G).hom := by
  rw [← cancel_epi (S.map F).homologyπ, homologyπ_comp_mapHomologyIso_hom_assoc,
    homologyπ_naturality_assoc, homologyπ_comp_mapHomologyIso_hom, τ.naturality,
    mapCyclesIso_hom_comp_app_assoc]

end NatTrans

section Comp

variable (F : C ⥤ D) (G : D ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `S.mapCyclesIso (F ⋙ G)` is the composition of `(S.map F).mapCyclesIso G`
and of the image by `G` of `S.mapCyclesIso F`. -/
lemma mapCyclesIso_comp_hom [S.HasLeftHomology] [(S.map F).HasLeftHomology]
    [((S.map F).map G).HasLeftHomology]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf (S.map F)]
    [(F ⋙ G).PreservesLeftHomologyOf S] :
    (S.mapCyclesIso (F ⋙ G)).hom =
      ((S.map F).mapCyclesIso G).hom ≫ G.map (S.mapCyclesIso F).hom := by
  rw [← cancel_mono ((F ⋙ G).map S.iCycles)]
  simp only [mapCyclesIso_hom_iCycles, assoc, Functor.comp_map, ← G.map_comp]
  exact S.mapCyclesIso_hom_iCycles (F ⋙ G)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `S.mapHomologyIso (F ⋙ G)` is the composition of
`(S.map F).mapHomologyIso G` and of the image by `G` of `S.mapHomologyIso F`. -/
lemma mapHomologyIso_comp_hom [S.HasHomology] [(S.map F).HasHomology]
    [((S.map F).map G).HasHomology] [(S.map (F ⋙ G)).HasHomology]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf (S.map F)]
    [(F ⋙ G).PreservesLeftHomologyOf S] :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  rw [← cancel_epi (S.map (F ⋙ G)).homologyπ, S.homologyπ_comp_mapHomologyIso_hom (F ⋙ G)]
  refine Eq.trans ?_ ((S.map F).homologyπ_comp_mapHomologyIso_hom_assoc G _).symm
  rw [← G.map_comp, homologyπ_comp_mapHomologyIso_hom, G.map_comp, mapCyclesIso_comp_hom,
    assoc]
  rfl

end Comp

end ShortComplex

end CategoryTheory
