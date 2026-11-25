/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import all WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawTransportIso

/-! # Counit-compatible transport of derived scalar extension

Source: Stacks Project, Tag 06Y6, and the right Kan extension universal property.
(blueprint: lem-pc-derived-extension-ring-equiv-raw-counit-equation)
-/

@[expose] public section
set_option autoImplicit false
universe u v w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kan_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F) [L.IsRightKanExtension α] :
    L.IsRightKanExtension (Functor.whiskerRight i.inv L ≫ α ≫ j.hom) := by
  classical
  let T := ((Functor.rightExtensionEquivalenceOfIso₁ i F).trans
    (Functor.rightExtensionEquivalenceOfIso₂ Q' j)).functor
  refine ⟨⟨?_⟩⟩
  apply CategoryTheory.Limits.IsTerminal.ofIso
    ((CategoryTheory.Limits.IsTerminal.isTerminalIffObj T _).toFun
      (L.isUniversalOfIsRightKanExtension α))
  exact CostructuredArrow.isoMk (Iso.refl _) (by
    ext X
    change (𝟙 _) ≫ (L.map (i.inv.app X) ≫ α.app X ≫ j.hom.app X) = _
    simp only [Category.id_comp]
    change L.map (i.inv.app X) ≫ (α.app X ≫ j.hom.app X) =
      (L.map (i.inv.app X) ≫ α.app X) ≫ j.hom.app X
    simp only [Category.assoc])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem complex_universal
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (F : C ⥤ D) [F.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    L.IsRightKanExtension
      ((Functor.associator (HomotopyCategory.quotient C (.up ℤ)) DerivedCategory.Qh L).hom ≫
        Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) ε) := by
  let := h
  let := Functor.IsLeftDerivedFunctor.isRightKanExtension L ε
    (HomotopyCategory.quasiIso _ (.up ℤ))
  exact kan_precomp_full (HomotopyCategory.quotient C (.up ℤ)) DerivedCategory.Qh _ L ε

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The former arbitrary-isomorphism equation was STATEMENT-DISPUTED: replacing an
-- isomorphism by its negative changes the left side alone. The corrected result
-- constructs the comparison together with its counit equation.
/-- Existence of a counit-compatible transported derived-functor isomorphism.
Source: Stacks Project, Tag 06Y6.
Proof: for additive functors between abelian categories, transport the two universal
counits through additive equivalences and
compare their right Kan extensions. The canonical comparison commutes with the
counits by the defining factorization equation of a right Kan extension lift.
(blueprint: lem-pc-derived-extension-ring-equiv-raw-counit-equation). -/
theorem raw_transport_counit_equation
    {C₀ D₀ C D : Type u}
    [Category.{v} C₀] [Category.{v} D₀] [Category.{v} C] [Category.{v} D]
    [Abelian C₀] [Abelian D₀] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C₀] [HasDerivedCategory.{w} D₀]
    [HasDerivedCategory.{w'} C] [HasDerivedCategory.{w'} D]
    (F₀ : C₀ ⥤ D₀) (F : C ⥤ D) [F₀.Additive] [F.Additive]
    (L₀ : DerivedCategory C₀ ⥤ DerivedCategory D₀)
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε₀ : DerivedCategory.Qh ⋙ L₀ ⟶
      F₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h₀ : L₀.IsLeftDerivedFunctor ε₀ (HomotopyCategory.quasiIso _ (.up ℤ)))
    (h : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (eR : C ≌ C₀) (eB : D ≌ D₀) [eR.functor.Additive] [eB.functor.Additive] :
    ∀ (E : DerivedCategory D ⥤ DerivedCategory D₀)
      (q : (HomotopyCategory.quotient D (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ E ≅
        eB.functor.mapHomologicalComplex (.up ℤ) ⋙
          (HomotopyCategory.quotient D₀ (.up ℤ) ⋙ DerivedCategory.Qh))
      (t : eR.functor.mapHomologicalComplex (.up ℤ) ⋙
        F₀.mapHomologicalComplex (.up ℤ) ≅
        F.mapHomologicalComplex (.up ℤ) ⋙
          eB.functor.mapHomologicalComplex (.up ℤ)),
      ∃ a : eR.functor.mapHomologicalComplex (.up ℤ) ⋙
        HomotopyCategory.quotient C₀ (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L₀ ≅
        HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L ⋙ E,
        ∀ K : CochainComplex C ℤ,
          a.hom.app K ≫ E.map (ε.app
            ((HomotopyCategory.quotient C (.up ℤ)).obj K)) ≫
            q.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
          ε₀.app ((HomotopyCategory.quotient C₀ (.up ℤ)).obj
            ((eR.functor.mapHomologicalComplex (.up ℤ)).obj K)) ≫
            ((HomotopyCategory.quotient D₀ (.up ℤ) ⋙ DerivedCategory.Qh).map
              (t.hom.app K)) := by
  intro E q t
  -- Compare universal counits on complexes, where the supplied square t lives.
  let SR := eR.functor.mapHomologicalComplex (.up ℤ)
  let T₀ := F₀.mapHomologicalComplex (.up ℤ)
  let T := F.mapHomologicalComplex (.up ℤ)
  let QB₀ := HomotopyCategory.quotient D₀ (.up ℤ) ⋙ DerivedCategory.Qh
  let cB := DerivedCategory.quotientCompQhIso D
  let cB₀ := DerivedCategory.quotientCompQhIso D₀
  let sR := eR.functor
  let sB := eB.functor
  let _ : SR.IsEquivalence :=
    eR.mapHomologicalComplex (.up ℤ)
      |>.isEquivalence_functor
  let _ : sR.mapDerivedCategory.IsEquivalence :=
    derived_equivalence eR
  let P₀ := HomotopyCategory.quotient C₀ (.up ℤ)
  let P := HomotopyCategory.quotient C (.up ℤ)
  let QB := HomotopyCategory.quotient D (.up ℤ) ⋙ DerivedCategory.Qh
  let α₀raw := (Functor.associator P₀ DerivedCategory.Qh L₀).hom ≫
    Functor.whiskerLeft P₀ ε₀
  let := complex_universal F₀ L₀ ε₀ h₀
  let j₀ : P₀ ⋙ F₀.mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh ≅ T₀ ⋙ QB₀ :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (F₀.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _
  let α₀ := Functor.whiskerRight
    (DerivedCategory.quotientCompQhIso C₀).inv L₀ ≫ α₀raw ≫ j₀.hom
  let := kan_change_iso L₀
    (DerivedCategory.quotientCompQhIso C₀) j₀ α₀raw
  let αpre := (Functor.associator SR DerivedCategory.Q L₀).hom ≫
    Functor.whiskerLeft SR α₀
  have hpre := (Functor.isRightKanExtension_iff_precomp L₀ SR α₀).mp
    (inferInstance : L₀.IsRightKanExtension α₀)
  let β₀ := (Functor.associator DerivedCategory.Q sR.mapDerivedCategory L₀).inv ≫
    Functor.whiskerRight sR.mapDerivedCategoryFactors.hom L₀ ≫ αpre
  let hβ₀ := (Functor.isRightKanExtension_iff_postcomp₁ sR.mapDerivedCategory
    sR.mapDerivedCategoryFactors αpre).mp hpre
  let := hβ₀
  -- Localization makes q descend uniquely to an isomorphism of derived functors.
  let qe : DerivedCategory.Q ⋙ E ≅ DerivedCategory.Q ⋙ sB.mapDerivedCategory :=
    Functor.isoWhiskerRight cB.symm E ≪≫ q ≪≫
      Functor.isoWhiskerLeft _ cB₀ ≪≫ sB.mapDerivedCategoryFactors.symm
  let pre := (Functor.whiskeringLeft (CochainComplex D ℤ)
    (DerivedCategory D) (DerivedCategory D₀)).obj
      DerivedCategory.Q
  let _ : pre.Full := Localization.full_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso D (.up ℤ)) _
  let _ : pre.Faithful := Localization.faithful_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso D (.up ℤ)) _
  let e : E ≅ sB.mapDerivedCategory := pre.preimageIso qe
  let _ : sB.mapDerivedCategory.IsEquivalence :=
    derived_equivalence eB
  let _ : E.IsEquivalence := Functor.isEquivalence_of_iso e.symm
  let αraw := (Functor.associator P DerivedCategory.Qh L).hom ≫
    Functor.whiskerLeft P ε
  let := complex_universal F L ε h
  let j : P ⋙ F.mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh ≅ T ⋙ QB :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _
  let α := Functor.whiskerRight
    (DerivedCategory.quotientCompQhIso C).inv L ≫ αraw ≫ j.hom
  let := kan_change_iso L (DerivedCategory.quotientCompQhIso C) j αraw
  let αpost := (Functor.associator DerivedCategory.Q L E).inv ≫ Functor.whiskerRight α E
  let := kan_postcomp_equivalence DerivedCategory.Q _ L E α
  let β := αpost ≫ (Functor.associator T QB E).hom
  let hβ := kan_change_iso (L ⋙ E) (Iso.refl DerivedCategory.Q)
    (Functor.associator T QB E) αpost
  let _ : (L ⋙ E).IsRightKanExtension β := by
    simpa [β] using hβ
  -- The supplied comparison t is the ordinary functor square needed for transport.
  let ordinary : SR ⋙ T₀ ⋙ QB₀ ≅ T ⋙ QB ⋙ E :=
    (Functor.associator SR T₀ QB₀).symm ≪≫
      Functor.isoWhiskerRight t QB₀ ≪≫
      Functor.associator T _ QB₀ ≪≫
      Functor.isoWhiskerLeft T q.symm
  -- Uniqueness of universal extensions supplies the derived comparison.
  let a := Functor.rightKanExtensionUniqueOfIso
    (eR.functor.mapDerivedCategory ⋙ L₀) β₀ ordinary (L ⋙ E) β
  let r := eR.functor.mapDerivedCategoryFactors
  let cR := DerivedCategory.quotientCompQhIso C
  let cR₀ := DerivedCategory.quotientCompQhIso C₀
  let acomplex := Functor.isoWhiskerLeft SR
      ((Functor.associator _ _ L₀).symm ≪≫ Functor.isoWhiskerRight cR₀ L₀) ≪≫
    (Functor.associator SR DerivedCategory.Q L₀).symm ≪≫
    Functor.isoWhiskerRight r.symm L₀ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Q a ≪≫
    Functor.isoWhiskerRight cR.symm (L ⋙ E) ≪≫
    Functor.associator _ _ _
  refine ⟨acomplex, ?_⟩
  intro K
  have ha := (L ⋙ E).liftOfIsRightKanExtension_fac_app β
    (sR.mapDerivedCategory ⋙ L₀) (β₀ ≫ ordinary.hom) K
  change a.hom.app (DerivedCategory.Q.obj K) ≫ β.app K =
    (β₀ ≫ ordinary.hom).app K at ha
  generalize hφ : a.hom.app (DerivedCategory.Q.obj K) = φ at ha
  dsimp only [β, αpost, α, αraw, j, β₀, αpre, α₀, α₀raw, j₀, ordinary,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.trans_hom,
    Iso.symm_hom] at ha
  simp only [Functor.mapHomotopyCategoryFactors, CategoryTheory.Quotient.lift.isLift_hom,
    Category.id_comp, Category.comp_id] at ha
  change φ ≫ E.map (L.map (cR.inv.app K) ≫ (𝟙 _ ≫ ε.app (P.obj K)) ≫
      DerivedCategory.Qh.map (𝟙 _)) =
    (L₀.map (r.hom.app K) ≫ 𝟙 _ ≫ L₀.map (cR₀.inv.app (SR.obj K)) ≫
      (𝟙 _ ≫ ε₀.app (P₀.obj (SR.obj K))) ≫ DerivedCategory.Qh.map (𝟙 _)) ≫
      QB₀.map (t.hom.app K) ≫ 𝟙 _ ≫ q.inv.app (T.obj K) at ha
  erw [(DerivedCategory.Qh (C := D)).map_id,
    (DerivedCategory.Qh (C := D₀)).map_id] at ha
  simp only [Category.id_comp] at ha
  simp only [Functor.map_comp] at ha
  erw [E.map_id] at ha
  simp only [Category.comp_id] at ha
  have hh := congrArg (fun f ↦
    L₀.map (cR₀.hom.app (SR.obj K)) ≫ L₀.map (r.inv.app K) ≫
      f ≫ q.hom.app (T.obj K)) ha
  dsimp only [acomplex, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id]
  rw [hφ]
  simp only [Functor.comp_map]
  dsimp only [r] at hh
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Iso.hom_inv_id_app] at hh
  erw [L₀.map_id] at hh
  simp only [Category.id_comp] at hh
  conv_rhs at hh =>
    rw (config := { transparency := .default }) [Category.comp_id]
    arg 2
    rw (config := { transparency := .default }) [Category.id_comp]
  simpa only [Functor.map_comp, Category.assoc, Functor.comp_map,
    SR, P, P₀, T, QB₀, r, cR, cR₀] using hh
end ModuleCat
