/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TwoOpenComparisonDiagram

/-! # Transport of two-open realizations

Source: Stacks Project, Tag 09RF, the local compatibility calculation.
(blueprint: lem-pc-two-open-comparison-realization).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry

private theorem comparison_leg
    {C D A W P T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* W] [Category* P] [Category* T]
    (L : C ⥤ D) (TU : C ⥤ A) (TW : C ⥤ W) (SU : A ⥤ W)
    (RU : D ⥤ P) (RW : D ⥤ T) (SP : P ⥤ T) (HU : A ⥤ P) (HW : W ⥤ T)
    (α : TU ⋙ SU ≅ TW) (τ : RU ⋙ SP ≅ RW)
    (β : L ⋙ RU ≅ TU ⋙ HU) (βW : L ⋙ RW ≅ TW ⋙ HW)
    (γ : HU ⋙ SP ≅ SU ⋙ HW)
    (F : C) (E : D) (A' : A) (i : TU.obj F ≅ A') (θ : HU.obj A' ≅ RU.obj E)
    (hc : τ.inv.app (L.obj F) ≫ SP.map (β.hom.app F) ≫ γ.hom.app (TU.obj F) =
      βW.hom.app F ≫ HW.map (α.inv.app F)) :
    τ.inv.app (L.obj F) ≫ SP.map ((β.app F ≪≫ HU.mapIso i ≪≫ θ).hom) ≫ τ.hom.app E =
      βW.hom.app F ≫ HW.map (α.inv.app F ≫ SU.map i.hom) ≫
        γ.inv.app A' ≫ SP.map θ.hom ≫ τ.hom.app E := by
  have hb : τ.inv.app (L.obj F) ≫ SP.map (β.hom.app F) =
      βW.hom.app F ≫ HW.map (α.inv.app F) ≫ γ.inv.app (TU.obj F) := by
    have h := congrArg (fun f ↦ f ≫ γ.inv.app (TU.obj F)) hc
    simpa only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id] using h
  have hn := γ.inv.naturality i.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    ← Category.assoc]
  rw [hb]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]

/-- Coherent two-open comparisons transport any realization of a compatible transition.
Source: Stacks Project, Tag 09RF, compatibility of local comparisons before gluing.
(blueprint: lem-pc-two-open-comparison-realization).

Proof: Compose each comparison β with the image of its local realization i and θ.
Expand the canonical restriction of each resulting map. Coherence replaces the β
restriction by βW followed by HW of α inverse; naturality of γ inverse moves the
local map through γ. Substitute the prescribed transition equation and then the
image under HW of the realization equation. The two expressions coincide.
No faithfulness, perfectness, nonempty overlap, or existence of F is needed. -/
theorem TwoOpenComparisonDiagram.realization
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    {L : C ⥤ D} {TU : C ⥤ A} {TV : C ⥤ B} {TW : C ⥤ W}
    {SU : A ⥤ W} {SV : B ⥤ W}
    {RU : D ⥤ P} {RV : D ⥤ Q} {RW : D ⥤ T}
    {SP : P ⥤ T} {SQ : Q ⥤ T}
    {αU : TU ⋙ SU ≅ TW} {αV : TV ⋙ SV ≅ TW}
    {τU : RU ⋙ SP ≅ RW} {τV : RV ⋙ SQ ≅ RW}
    (d : TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ αU αV τU τV)
    {A' : A} {B' : B} {E : D}
    (e : SU.obj A' ≅ SV.obj B')
    (θU : d.HU.obj A' ≅ RU.obj E) (θV : d.HV.obj B' ≅ RV.obj E)
    (hθ : d.γU.inv.app A' ≫ SP.map θU.hom ≫ τU.hom.app E =
      d.HW.map e.hom ≫ d.γV.inv.app B' ≫ SQ.map θV.hom ≫ τV.hom.app E)
    (F : C) (iU : TU.obj F ≅ A') (iV : TV.obj F ≅ B')
    (hi : αU.inv.app F ≫ SU.map iU.hom ≫ e.hom =
      αV.inv.app F ≫ SV.map iV.hom) :
    ∃ (pU : RU.obj (L.obj F) ≅ RU.obj E) (pV : RV.obj (L.obj F) ≅ RV.obj E),
      τU.inv.app (L.obj F) ≫ SP.map pU.hom ≫ τU.hom.app E =
        τV.inv.app (L.obj F) ≫ SQ.map pV.hom ≫ τV.hom.app E := by
  refine ⟨d.βU.app F ≪≫ d.HU.mapIso iU ≪≫ θU,
    d.βV.app F ≪≫ d.HV.mapIso iV ≪≫ θV, ?_⟩
  rw [comparison_leg L TU TW SU RU RW SP d.HU d.HW αU τU d.βU d.βW d.γU
      F E A' iU θU (d.coherenceU F),
    comparison_leg L TV TW SV RV RW SQ d.HV d.HW αV τV d.βV d.βW d.γV
      F E B' iV θV (d.coherenceV F)]
  rw [hθ]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ d.βW.hom.app F ≫ f ≫ d.γV.inv.app B' ≫
      SQ.map θV.hom ≫ τV.hom.app E) (congrArg d.HW.map hi)

end AlgebraicGeometry
