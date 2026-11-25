/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Equivalence

/-! # Transport of derived scalar extension through ring equivalences -/

@[expose] public section
set_option autoImplicit false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Precomposition with a functor `P` along which whiskering is fully faithful preserves right
Kan extensions. -/
theorem kan_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    [((Functor.whiskeringLeft A C H).obj P).Full]
    [((Functor.whiskeringLeft A C H).obj P).Faithful]
    (α : Q ⋙ L ⟶ F) [L.IsRightKanExtension α] :
    L.IsRightKanExtension ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α) := by
  classical
  let W := (Functor.whiskeringLeft A C H).obj P
  let β := (Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α
  let lift (s : Functor.RightExtension (P ⋙ Q) (P ⋙ F)) : s.left ⟶ L :=
    L.liftOfIsRightKanExtension α s.left
      (W.preimage ((Functor.associator P Q s.left).inv ≫ s.hom))
  have fac (s : Functor.RightExtension (P ⋙ Q) (P ⋙ F)) :
      Functor.whiskerLeft (P ⋙ Q) (lift s) ≫ β = s.hom := by
    have hf := L.liftOfIsRightKanExtension_fac α s.left
      (W.preimage ((Functor.associator P Q s.left).inv ≫ s.hom))
    have hh := congrArg (fun f ↦ W.map f) hf
    simp only [Functor.map_comp, Functor.map_preimage] at hh
    ext X
    have hX := congr_app hh X
    simpa [lift, β, W] using hX
  refine ⟨⟨CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (fun s ↦ CostructuredArrow.homMk (lift s) (fac s)) ?_⟩⟩
  intro s m
  apply CostructuredArrow.hom_ext
  apply L.hom_ext_of_isRightKanExtension α
  apply W.map_injective
  have hm := m.w
  have hf := fac s
  ext X
  have hmX := congr_app hm X
  have hfX := congr_app hf X
  dsimp at hmX
  dsimp [β] at hfX
  simp only [Category.id_comp] at hmX hfX
  simpa [β, W, Category.id_comp] using hmX.trans hfX.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_postcomp_equivalence
    {C D H H' : Type*} [Category C] [Category D] [Category H] [Category H']
    (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H) (E : H ⥤ H') [E.IsEquivalence]
    (α : Q ⋙ L ⟶ F) [L.IsRightKanExtension α] :
    (L ⋙ E).IsRightKanExtension
      ((Functor.associator Q L E).inv ≫ Functor.whiskerRight α E) := by
  classical
  let T := Functor.RightExtension.postcompose₂ Q F E
  have : T.IsEquivalence := by
    let i : (Functor.whiskeringRight D H H').obj E ⋙
        (Functor.whiskeringLeft C D H').obj Q ≅
      (Functor.whiskeringLeft C D H).obj Q ⋙
        (Functor.whiskeringRight C H H').obj E :=
      NatIso.ofComponents (fun X ↦ (Functor.associator Q X E).symm) (by
        intro X Y f
        ext x
        simp)
    change (CostructuredArrow.map₂ i.hom (𝟙 (F ⋙ E))).IsEquivalence
    let _ : IsIso (𝟙 (F ⋙ E)) := inferInstance
    apply CostructuredArrow.isEquivalenceMap₂
  exact ⟨⟨CategoryTheory.Limits.IsTerminal.ofIso
    ((CategoryTheory.Limits.IsTerminal.isTerminalIffObj T _).toFun
      (L.isUniversalOfIsRightKanExtension α))
    (Functor.RightExtension.postcompose₂ObjMkIso E α)⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kan_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F) [L.IsRightKanExtension α] :
    ∃ β : Q' ⋙ L ⟶ F', L.IsRightKanExtension β := by
  classical
  let T := ((Functor.rightExtensionEquivalenceOfIso₁ i F).trans
    (Functor.rightExtensionEquivalenceOfIso₂ Q' j)).functor
  refine ⟨(T.obj (Functor.RightExtension.mk L α)).hom, ⟨⟨?_⟩⟩⟩
  exact (CategoryTheory.Limits.IsTerminal.isTerminalIffObj T _).toFun
    (L.isUniversalOfIsRightKanExtension α)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem complex_universal
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (F : C ⥤ D) [F.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    ∃ α : DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      L.IsRightKanExtension α := by
  let := h
  let := Functor.IsLeftDerivedFunctor.isRightKanExtension L ε
    (HomotopyCategory.quasiIso _ (.up ℤ))
  let P := HomotopyCategory.quotient C (.up ℤ)
  let α := (Functor.associator P DerivedCategory.Qh L).hom ≫ Functor.whiskerLeft P ε
  let := kan_precomp_full P DerivedCategory.Qh _ L ε
  let j : P ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  exact kan_change_iso L (DerivedCategory.quotientCompQhIso C) j α

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_equivalence
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (e : C ≌ D) [e.functor.Additive] : e.functor.mapDerivedCategory.IsEquivalence := by
  let ec := e.mapHomologicalComplex (.up ℤ)
  let F := e.functor.mapHomologicalComplex (.up ℤ)
  let G := e.inverse.mapHomologicalComplex (.up ℤ)
  let α : (F ⋙ DerivedCategory.Q) ⋙ e.inverse.mapDerivedCategory ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F e.inverse.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ec.unitIso.symm DerivedCategory.Q ≪≫
      Functor.leftUnitor _
  let β : (G ⋙ DerivedCategory.Q) ⋙ e.functor.mapDerivedCategory ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G e.functor.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ec.counitIso DerivedCategory.Q ≪≫
      Functor.leftUnitor _
  exact Localization.isEquivalence
    (DerivedCategory.Q (C := C)) (HomologicalComplex.quasiIso C (.up ℤ))
    (DerivedCategory.Q (C := D)) (HomologicalComplex.quasiIso D (.up ℤ))
    (F ⋙ DerivedCategory.Q) e.functor.mapDerivedCategory
    (G ⋙ DerivedCategory.Q) e.inverse.mapDerivedCategory α β

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- Existence of the transported derived-functor isomorphism, before its counit equation.
Source: Stacks Project, Tag 06Y6.
The proof uses uniqueness of left derived functors after transport through ring equivalences.
(blueprint: lem-pc-derived-extension-ring-equiv-raw-transport-iso). -/
theorem exists_raw_transport_iso
    {R₀ B₀ R B : Type u}
    [CommRing R₀] [CommRing B₀] [CommRing R] [CommRing B]
    [Algebra R₀ B₀] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (L₀ : DerivedCategory (ModuleCat.{u} R₀) ⥤ DerivedCategory (ModuleCat.{u} B₀))
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε₀ : DerivedCategory.Qh ⋙ L₀ ⟶
      (extendScalars (algebraMap R₀ B₀)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h₀ : L₀.IsLeftDerivedFunctor ε₀ (HomotopyCategory.quasiIso _ (.up ℤ)))
    (h : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (eR : R₀ ≃+* R) (eB : B₀ ≃+* B)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom) :
    ∀ (E : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B₀))
      (q : (HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ E ≅
        (restrictScalars.{u} eB.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
          (HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh))
      (t : (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
        (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ) ≅
        (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ) ⋙
          (restrictScalars.{u} eB.toRingHom).mapHomologicalComplex (.up ℤ)),
      Nonempty ((restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
        HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L₀ ≅
        HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L ⋙ E) :=
  by
  intro E q t
  -- Compare universal counits on complexes, where the supplied square t lives.
  let SR := (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ)
  let T₀ := (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ)
  let T := (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)
  let QB₀ := HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh
  let cB := DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)
  let cB₀ := DerivedCategory.quotientCompQhIso (ModuleCat.{u} B₀)
  let sR := restrictScalars.{u} eR.toRingHom
  let sB := restrictScalars.{u} eB.toRingHom
  let _ : SR.IsEquivalence :=
    (restrictScalarsEquivalenceOfRingEquiv eR).mapHomologicalComplex (.up ℤ)
      |>.isEquivalence_functor
  let _ : sR.mapDerivedCategory.IsEquivalence :=
    derived_equivalence (restrictScalarsEquivalenceOfRingEquiv eR)
  obtain ⟨α₀, hα₀⟩ := complex_universal (extendScalars (algebraMap R₀ B₀)) L₀ ε₀ h₀
  let := hα₀
  let αpre := (Functor.associator SR DerivedCategory.Q L₀).hom ≫
    Functor.whiskerLeft SR α₀
  have hpre := (Functor.isRightKanExtension_iff_precomp L₀ SR α₀).mp hα₀
  let β₀ := (Functor.associator DerivedCategory.Q sR.mapDerivedCategory L₀).inv ≫
    Functor.whiskerRight sR.mapDerivedCategoryFactors.hom L₀ ≫ αpre
  let hβ₀ := (Functor.isRightKanExtension_iff_postcomp₁ sR.mapDerivedCategory
    sR.mapDerivedCategoryFactors αpre).mp hpre
  let := hβ₀
  -- Localization makes q descend uniquely to an isomorphism of derived functors.
  let qe : DerivedCategory.Q ⋙ E ≅ DerivedCategory.Q ⋙ sB.mapDerivedCategory :=
    Functor.isoWhiskerRight cB.symm E ≪≫ q ≪≫
      Functor.isoWhiskerLeft _ cB₀ ≪≫ sB.mapDerivedCategoryFactors.symm
  let pre := (Functor.whiskeringLeft (CochainComplex (ModuleCat.{u} B) ℤ)
    (DerivedCategory (ModuleCat.{u} B)) (DerivedCategory (ModuleCat.{u} B₀))).obj
      DerivedCategory.Q
  let _ : pre.Full := Localization.full_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)) _
  let _ : pre.Faithful := Localization.faithful_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)) _
  let e : E ≅ sB.mapDerivedCategory := pre.preimageIso qe
  let _ : sB.mapDerivedCategory.IsEquivalence :=
    derived_equivalence (restrictScalarsEquivalenceOfRingEquiv eB)
  let _ : E.IsEquivalence := Functor.isEquivalence_of_iso e.symm
  obtain ⟨α, hα⟩ := complex_universal (extendScalars (algebraMap R B)) L ε h
  let := hα
  let αpost := (Functor.associator DerivedCategory.Q L E).inv ≫ Functor.whiskerRight α E
  let := kan_postcomp_equivalence DerivedCategory.Q _ L E α
  obtain ⟨β, hβ⟩ := kan_change_iso (L ⋙ E) (Iso.refl DerivedCategory.Q)
    (Functor.associator T DerivedCategory.Q E) αpost
  let := hβ
  -- The ordinary comparison needs only t; its construction already encodes hRB.
  let ordinary : SR ⋙ T₀ ⋙ DerivedCategory.Q ≅ T ⋙ DerivedCategory.Q ⋙ E :=
    Functor.isoWhiskerLeft SR (Functor.isoWhiskerLeft T₀ cB₀.symm) ≪≫
      (Functor.associator SR T₀ QB₀).symm ≪≫
      Functor.isoWhiskerRight t QB₀ ≪≫
      Functor.associator T _ QB₀ ≪≫
      Functor.isoWhiskerLeft T q.symm ≪≫
      Functor.isoWhiskerLeft T (Functor.isoWhiskerRight cB E) ≪≫
      Functor.associator T DerivedCategory.Q E
  -- Uniqueness of universal extensions supplies the derived comparison.
  let a := Functor.rightKanExtensionUniqueOfIso
    ((restrictScalars.{u} eR.toRingHom).mapDerivedCategory ⋙ L₀) β₀ ordinary (L ⋙ E) β
  let r := (restrictScalars.{u} eR.toRingHom).mapDerivedCategoryFactors
  let cR := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  let cR₀ := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R₀)
  refine ⟨?_⟩
  exact Functor.isoWhiskerLeft SR
      ((Functor.associator _ _ L₀).symm ≪≫ Functor.isoWhiskerRight cR₀ L₀) ≪≫
    (Functor.associator SR DerivedCategory.Q L₀).symm ≪≫
    Functor.isoWhiskerRight r.symm L₀ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Q a ≪≫
    Functor.isoWhiskerRight cR.symm (L ⋙ E) ≪≫
    Functor.associator _ _ _
end ModuleCat
