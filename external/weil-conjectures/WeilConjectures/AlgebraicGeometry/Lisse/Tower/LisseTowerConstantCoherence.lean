/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantComplexPresentation
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantComplexPresentation
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstantsModel

/-! # Coherence of the ordinary constant comparisons

The ordinary constant comparisons are compatible with restriction of coefficients along
consecutive quotients; localization gives the coherence of the derived comparisons.

## References

* Stacks Project, Modules on Sites, Tags 03CY and 03DA
* Sites, Tag 0H7J
* Derived Categories, Tag 05RU
-/

public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor

namespace CategoryTheory

section ConstantUnit

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  {D B : Type*} [Category* D] [Category* B] (U : D ⥤ B) [HasWeakSheafify J D]
  [HasWeakSheafify J B] [J.PreservesSheafification U] [J.HasSheafCompose U]

/-- The unit of the constant sheaf adjunction is compatible with `constantCommuteCompose`. -/
theorem constantSheafAdj_unit_app_comp_constantCommuteCompose_inv {T : C}
    (hT : IsTerminal T) (M : D) :
    (constantSheafAdj J B hT).unit.app (U.obj M) ≫
        ((sheafSections J B).obj (Opposite.op T)).map
          ((constantCommuteCompose J U).inv.app M) =
      U.map ((constantSheafAdj J D hT).unit.app M) := by
  refine Eq.trans ((constantSheafAdj J B hT).homEquiv_unit _ _ _).symm ?_
  apply ((constantSheafAdj J B hT).homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  have hc := constantSheafAdj_counit_w J U ((constantSheaf J D).obj M) hT
  have hn := (constantCommuteCompose J U).hom.naturality ((constantSheafAdj J D hT).unit.app M)
  have ht := (constantSheafAdj J D hT).left_triangle_components M
  simp only [Functor.comp_map] at hn
  rw [← cancel_epi ((constantCommuteCompose J U).hom.app M), Iso.hom_inv_id_app]
  erw [← reassoc_of% hn]
  erw [hc]
  rw [← Functor.map_comp]
  erw [ht]
  exact ((sheafCompose J U).map_id _).symm

end ConstantUnit


section Glue

variable {C₀ C₁ E₀ E₁ P₀ P₁ T₀ T₁ Z₀ Z₁ W₀ W₁ V A' : Type*}
  [Category C₀] [Category C₁] [Category E₀] [Category E₁] [Category P₀] [Category P₁]
  [Category T₀] [Category T₁] [Category Z₀] [Category Z₁] [Category W₀] [Category W₁]
  [Category V] [Category A']
  {R : C₀ ⥤ C₁} {sE : E₀ ⥤ E₁} {sP : P₀ ⥤ P₁} {sT : T₀ ⥤ T₁} {sZ : Z₀ ⥤
      Z₁}
  {CE₀ : C₀ ⥤ E₀} {CE₁ : C₁ ⥤ E₁} {CP₀ : C₀ ⥤ P₀} {CP₁ : C₁ ⥤ P₁}
  {CT₀ : C₀ ⥤ T₀} {CT₁ : C₁ ⥤ T₁} {CZ₀ : C₀ ⥤ Z₀} {CZ₁ : C₁ ⥤ Z₁}
  {cu₀ : E₀ ⥤ P₀} {cu₁ : E₁ ⥤ P₁} {ua₀ : P₀ ⥤ T₀} {ua₁ : P₁ ⥤ T₁}
  {ub₀ : T₀ ⥤ Z₀} {ub₁ : T₁ ⥤ Z₁} {F₀ : Z₀ ⥤ W₀} {F₁ : Z₁ ⥤ W₁}
  {Rq : W₀ ⥤ W₁} {H₀ : W₀ ⥤ V} {H₁ : W₁ ⥤ V}
  {Q₀ : C₀ ⥤ W₀} {Q₁ : C₁ ⥤ W₁} {Af₀ : C₀ ⥤ A'} {Af₁ : C₁ ⥤ A'} {Fin :
      A' ⥤ V}

/-- The pasted constant model. -/
def constantModelPaste {C E P T Z W : Type*} [Category C] [Category E] [Category P]
    [Category T] [Category Z] [Category W] {CE : C ⥤ E} {cu : E ⥤ P} {CP : C ⥤ P}
    {ua : P ⥤ T} {CT : C ⥤ T} {ub : T ⥤ Z} {CZ : C ⥤ Z} {F : Z ⥤ W} {Q : C ⥤ W}
    (e₁ : CE ⋙ cu ≅ CP) (e₂ : CP ⋙ ua ≅ CT) (e₃ : CT ⋙ ub ≅ CZ) (o : CZ ⋙ F ≅
        Q) :
    CE ⋙ (cu ⋙ ua) ⋙ ub ⋙ F ≅ Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e₁ _ ≪≫ e₂) _ ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₃ _ ≪≫ o

/-- Pasting the coefficient compatibilities of the constant comparisons. -/
theorem constantComparisons_paste
    (cccE : CE₀ ⋙ sE ≅ R ⋙ CE₁) (cccP : CP₀ ⋙ sP ≅ R ⋙ CP₁)
    (cccT : CT₀ ⋙ sT ≅ R ⋙ CT₁) (cccZ : CZ₀ ⋙ sZ ≅ R ⋙ CZ₁)
    (nCu : sE ⋙ cu₁ ≅ cu₀ ⋙ sP) (nA : sP ⋙ ua₁ ≅ ua₀ ⋙ sT) (nB : sT ⋙ ub₁
        ≅ ub₀ ⋙ sZ)
    (c : sZ ⋙ F₁ ≅ F₀ ⋙ Rq) (rc : Rq ⋙ H₁ ≅ H₀)
    (e₁₀ : CE₀ ⋙ cu₀ ≅ CP₀) (e₁₁ : CE₁ ⋙ cu₁ ≅ CP₁)
    (e₂₀ : CP₀ ⋙ ua₀ ≅ CT₀) (e₂₁ : CP₁ ⋙ ua₁ ≅ CT₁)
    (e₃₀ : CT₀ ⋙ ub₀ ≅ CZ₀) (e₃₁ : CT₁ ⋙ ub₁ ≅ CZ₁)
    (o₀ : CZ₀ ⋙ F₀ ≅ Q₀) (o₁ : CZ₁ ⋙ F₁ ≅ Q₁)
    (r₀ : Af₀ ⋙ Fin ≅ Q₀ ⋙ H₀) (r₁ : Af₁ ⋙ Fin ≅ Q₁ ⋙ H₁) (alg : R ⋙
        Af₁ ≅ Af₀)
    (h₁ : ∀ X, e₁₁.hom.app (R.obj X) ≫ cccP.inv.app X =
      cu₁.map (cccE.inv.app X) ≫ nCu.hom.app (CE₀.obj X) ≫ sP.map (e₁₀.hom.app X))
    (h₂ : ∀ X, e₂₁.hom.app (R.obj X) ≫ cccT.inv.app X =
      ua₁.map (cccP.inv.app X) ≫ nA.hom.app (CP₀.obj X) ≫ sT.map (e₂₀.hom.app X))
    (h₃ : ∀ X, e₃₁.hom.app (R.obj X) ≫ cccZ.inv.app X =
      ub₁.map (cccT.inv.app X) ≫ nB.hom.app (CT₀.obj X) ≫ sZ.map (e₃₀.hom.app X))
    (h₄ : ∀ X, H₁.map (F₁.map (cccZ.inv.app X)) ≫ H₁.map (c.hom.app (CZ₀.obj X)) ≫
        rc.hom.app (F₀.obj (CZ₀.obj X)) ≫ H₀.map (o₀.hom.app X) ≫ r₀.inv.app X =
      H₁.map (o₁.hom.app (R.obj X)) ≫ r₁.inv.app (R.obj X) ≫ Fin.map (alg.hom.app X)) :
    (AlgebraicGeometry.Scheme.lisseTowerPasteConstantScalar R sE sT CE₀ CE₁ (cu₀ ⋙ ua₀)
        (cu₁ ⋙ ua₁) (ub₀ ⋙ F₀)
        (ub₁ ⋙ F₁) H₀ H₁ cccE.symm
        ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight nCu ua₁ ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft cu₀ nA ≪≫
          (Functor.associator _ _ _).symm)
        (Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight nB F₁ ≪≫ Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft ub₀ c ≪≫ (Functor.associator _ _ _).symm) H₁ ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (ub₀ ⋙ F₀) rc ≪≫
          (Functor.associator ub₀ F₀ H₀).symm) ≪≫
      (Functor.isoWhiskerRight (constantModelPaste e₁₀ e₂₀ e₃₀ o₀) H₀ ≪≫
        r₀.symm)).hom =
    (Functor.isoWhiskerLeft R
        (Functor.isoWhiskerRight (constantModelPaste e₁₁ e₂₁ e₃₁ o₁) H₁ ≪≫
          r₁.symm) ≪≫ Functor.isoWhiskerRight alg Fin).hom := by
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp only [constantModelPaste, AlgebraicGeometry.Scheme.lisseTowerPasteConstantScalar,
      Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.map_comp, Category.id_comp, Category.comp_id,
    Category.assoc, Functor.comp_obj, Functor.comp_map]
  have A1 : ∀ {Y Y' : Z₀} (φ : Y ⟶ Y'), H₁.map (c.hom.app Y) ≫ rc.hom.app (F₀.obj Y)
      ≫
      H₀.map (F₀.map φ) = H₁.map (F₁.map (sZ.map φ)) ≫ H₁.map (c.hom.app Y') ≫
        rc.hom.app (F₀.obj Y') := by
    intro Y Y' φ
    have h1 := rc.hom.naturality (F₀.map φ)
    have h2 := c.hom.naturality φ
    simp only [Functor.comp_map] at h1 h2
    rw [← h1, ← Category.assoc, ← H₁.map_comp, ← h2, H₁.map_comp, Category.assoc]
  have A2 : ∀ {Y Y' : T₀} (φ : Y ⟶ Y'), H₁.map (F₁.map (nB.hom.app Y)) ≫
      H₁.map (F₁.map (sZ.map (ub₀.map φ))) =
        H₁.map (F₁.map (ub₁.map (sT.map φ))) ≫ H₁.map (F₁.map (nB.hom.app Y')) := by
    intro Y Y' φ
    have h := nB.hom.naturality φ
    simp only [Functor.comp_map] at h
    simp only [← Functor.map_comp, h]
  have A3 : ∀ {Y Y' : P₀} (φ : Y ⟶ Y'), H₁.map (F₁.map (ub₁.map (nA.hom.app Y))) ≫
      H₁.map (F₁.map (ub₁.map (sT.map (ua₀.map φ)))) =
        H₁.map (F₁.map (ub₁.map (ua₁.map (sP.map φ)))) ≫
          H₁.map (F₁.map (ub₁.map (nA.hom.app Y'))) := by
    intro Y Y' φ
    have h := nA.hom.naturality φ
    simp only [Functor.comp_map] at h
    simp only [← Functor.map_comp, h]
  have B1 : H₁.map (F₁.map (ub₁.map (ua₁.map (cu₁.map (cccE.inv.app X))))) ≫
      H₁.map (F₁.map (ub₁.map (ua₁.map (nCu.hom.app (CE₀.obj X))))) ≫
        H₁.map (F₁.map (ub₁.map (ua₁.map (sP.map (e₁₀.hom.app X))))) =
      H₁.map (F₁.map (ub₁.map (ua₁.map (e₁₁.hom.app (R.obj X))))) ≫
        H₁.map (F₁.map (ub₁.map (ua₁.map (cccP.inv.app X)))) := by
    simp only [← Functor.map_comp, h₁]
  have B2 : H₁.map (F₁.map (ub₁.map (ua₁.map (cccP.inv.app X)))) ≫
      H₁.map (F₁.map (ub₁.map (nA.hom.app (CP₀.obj X)))) ≫
        H₁.map (F₁.map (ub₁.map (sT.map (e₂₀.hom.app X)))) =
      H₁.map (F₁.map (ub₁.map (e₂₁.hom.app (R.obj X)))) ≫
        H₁.map (F₁.map (ub₁.map (cccT.inv.app X))) := by
    simp only [← Functor.map_comp, h₂]
  have B3 : H₁.map (F₁.map (ub₁.map (cccT.inv.app X))) ≫
      H₁.map (F₁.map (nB.hom.app (CT₀.obj X))) ≫
        H₁.map (F₁.map (sZ.map (e₃₀.hom.app X))) =
      H₁.map (F₁.map (e₃₁.hom.app (R.obj X))) ≫ H₁.map (F₁.map (cccZ.inv.app X)) := by
    simp only [← Functor.map_comp, h₃]
  rw [reassoc_of% A1, reassoc_of% A2, reassoc_of% A3, reassoc_of% B1]
  rw [reassoc_of% A1, reassoc_of% A2, reassoc_of% B2]
  rw [reassoc_of% A1, reassoc_of% B3, h₄]

end Glue


section Glue4

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  {RA R₁ R₀ : Sheaf J RingCat.{u + 1}} (p₁ : RA ⟶ R₁) (p₀ : RA ⟶ R₀) (qt : R₁ ⟶
      R₀)

/-- Sections of a restricted module sheaf. -/
def restrictElem {R S : Sheaf J RingCat.{u + 1}} (φ : R ⟶ S) (M : SheafOfModules.{u + 1} S)
    (V : Cᵒᵖ) (y : M.val.obj V) : ((SheafOfModules.restrictScalars.{u + 1} φ).obj M).val.obj V
        :=
  y

/-- Elements of a module with restricted scalars. -/
def moduleRestrictElem {R S : Type (u + 1)} [Ring R] [Ring S] (f : R →+* S)
    (N : ModuleCat.{u + 1} S) (x : N) : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f).obj N :=
  x

/-- A section of a restricted module sheaf is determined by an injective comparison of
the underlying abelian sheaf. -/
theorem eq_restrictElem_of_injective {R S : Sheaf J RingCat.{u + 1}} (φ : R ⟶ S)
    {X : SheafOfModules.{u + 1} R} {M : SheafOfModules.{u + 1} S}
    (f : X ⟶ (SheafOfModules.restrictScalars.{u + 1} φ).obj M) {G : Sheaf J AddCommGrpCat.{u +
        1}}
    (F : (SheafOfModules.toSheaf.{u + 1} S).obj M ⟶ G) (V : Cᵒᵖ)
    (hF : Function.Injective (F.hom.app V)) (x : X.val.obj V) (y : M.val.obj V)
    (h : F.hom.app V (f.val.app V x) = F.hom.app V y) :
    f.val.app V x = restrictElem φ M V y :=
  hF h

/-- An elementwise consequence of a square normalized on underlying abelian sheaves. -/
theorem restrictElem_of_normalized {R₁' R₀' : Sheaf J RingCat.{u + 1}} (φ : R₁' ⟶ R₀')
    {A₁ : SheafOfModules.{u + 1} R₁'} {A₀ : SheafOfModules.{u + 1} R₀'}
    {G₁ G₀ : Sheaf J AddCommGrpCat.{u + 1}}
    (c : A₁ ⟶ (SheafOfModules.restrictScalars.{u + 1} φ).obj A₀)
    (F₁ : (SheafOfModules.toSheaf.{u + 1} R₁').obj A₁ ⟶ G₁)
    (F₀ : (SheafOfModules.toSheaf.{u + 1} R₀').obj A₀ ⟶ G₀)
    (r : (SheafOfModules.toSheaf.{u + 1} R₁').obj ((SheafOfModules.restrictScalars.{u + 1}
        φ).obj A₀) ⟶
      (SheafOfModules.toSheaf.{u + 1} R₀').obj A₀) (t : G₁ ⟶ G₀)
    (h : (SheafOfModules.toSheaf.{u + 1} R₁').map c ≫ r ≫ F₀ = F₁ ≫ t)
    (V : Cᵒᵖ) (hF : Function.Injective (F₀.hom.app V))
    (hr : ∀ z : A₀.val.obj V, r.hom.app V (restrictElem φ A₀ V z) = z)
    (a₁ : A₁.val.obj V) (a₀ : A₀.val.obj V) (y : G₀.obj.obj V)
    (h₁ : t.hom.app V (F₁.hom.app V a₁) = y) (h₀ : F₀.hom.app V a₀ = y) :
    c.val.app V a₁ = restrictElem φ A₀ V a₀ := by
  let z : A₀.val.obj V := c.val.app V a₁
  change restrictElem φ A₀ V z = restrictElem φ A₀ V a₀
  congr 1
  apply hF
  have e := congrArg (fun w ↦ w.hom.app V a₁) h
  change F₀.hom.app V (r.hom.app V (restrictElem φ A₀ V z)) = t.hom.app V (F₁.hom.app V
      a₁) at e
  rw [hr] at e
  exact e.trans (h₁.trans h₀.symm)

/-- Paste elementwise identities of the realization layer. -/
theorem realizationLayer_paste {I : Type*} (V : Cᵒᵖ)
    {S Y₁ W₁ : SheafOfModules.{u + 1} R₁} {Y₀ W₀ : SheafOfModules.{u + 1} R₀}
    {T T' : SheafOfModules.{u + 1} RA}
    (a : S ⟶ Y₁) (c : Y₁ ⟶ (SheafOfModules.restrictScalars.{u + 1} qt).obj Y₀)
    (rc : (SheafOfModules.restrictScalars.{u + 1} p₁).obj
      ((SheafOfModules.restrictScalars.{u + 1} qt).obj Y₀) ⟶
        (SheafOfModules.restrictScalars.{u + 1} p₀).obj Y₀)
    (o₀ : Y₀ ⟶ W₀) (r₀ : (SheafOfModules.restrictScalars.{u + 1} p₀).obj W₀ ⟶ T)
    (o₁ : S ⟶ W₁) (r₁ : (SheafOfModules.restrictScalars.{u + 1} p₁).obj W₁ ⟶ T')
    (alg : T' ⟶ T)
    [IsIso a] [IsIso c] [IsIso rc] [IsIso o₀] [IsIso r₀] [IsIso o₁] [IsIso r₁] [IsIso alg]
    (s : I → S.val.obj V) (y₁ : I → Y₁.val.obj V) (y₀ : I → Y₀.val.obj V)
    (w₀ : I → W₀.val.obj V) (w₁ : I → W₁.val.obj V) (t' : I → T'.val.obj V)
    (t : I → T.val.obj V)
    (ha : ∀ i, a.val.app V (s i) = y₁ i)
    (hc : ∀ i, c.val.app V (y₁ i) = restrictElem qt Y₀ V (y₀ i))
    (hrc : ∀ y, rc.val.app V (restrictElem p₁ _ V (restrictElem qt Y₀ V y)) =
      restrictElem p₀ Y₀ V y)
    (ho₀ : ∀ i, o₀.val.app V (y₀ i) = w₀ i)
    (hr₀ : ∀ i, r₀.val.app V (restrictElem p₀ W₀ V (w₀ i)) = t i)
    (ho₁ : ∀ i, o₁.val.app V (s i) = w₁ i)
    (hr₁ : ∀ i, r₁.val.app V (restrictElem p₁ W₁ V (w₁ i)) = t' i)
    (halg : ∀ i, alg.val.app V (t' i) = t i)
    (hgen : ∀ {Y : SheafOfModules.{u + 1} RA} (φ ψ : T ⟶ Y),
      (∀ i, φ.val.app V (t i) = ψ.val.app V (t i)) → φ = ψ) :
    (SheafOfModules.restrictScalars.{u + 1} p₁).map a ≫
        (SheafOfModules.restrictScalars.{u + 1} p₁).map c ≫ rc ≫
        (SheafOfModules.restrictScalars.{u + 1} p₀).map o₀ ≫ r₀ =
      (SheafOfModules.restrictScalars.{u + 1} p₁).map o₁ ≫ r₁ ≫ alg := by
  set L := (SheafOfModules.restrictScalars.{u + 1} p₁).map a ≫
        (SheafOfModules.restrictScalars.{u + 1} p₁).map c ≫ rc ≫
        (SheafOfModules.restrictScalars.{u + 1} p₀).map o₀ ≫ r₀ with hL
  set R := (SheafOfModules.restrictScalars.{u + 1} p₁).map o₁ ≫ r₁ ≫ alg with hR
  have hLs : ∀ i, L.val.app V (restrictElem p₁ S V (s i)) = t i := by
    intro i
    rw [hL]
    change r₀.val.app V (o₀.val.app V (rc.val.app V (c.val.app V (a.val.app V (s i))))) = t i
    rw [ha, hc]
    erw [hrc]
    rw [← hr₀, ← ho₀]
    rfl
  have hRs : ∀ i, R.val.app V (restrictElem p₁ S V (s i)) = t i := by
    intro i
    rw [hR]
    change alg.val.app V (r₁.val.app V (o₁.val.app V (s i))) = t i
    rw [ho₁]
    erw [hr₁]
    exact halg i
  have hinv : inv L = inv R := by
    apply hgen
    intro i
    have h1 := congrArg (fun z ↦ (inv L).val.app V z) (hLs i)
    have h2 := congrArg (fun z ↦ (inv R).val.app V z) (hRs i)
    simp only at h1 h2
    rw [← h1, ← h2]
    change (L ≫ inv L).val.app V _ = (R ≫ inv R).val.app V _
    rw [IsIso.hom_inv_id, IsIso.hom_inv_id]
  calc L = inv (inv L) := (IsIso.inv_inv (f := L)).symm
    _ = inv (inv R) := by simp only [hinv]
    _ = R := IsIso.inv_inv

end Glue4

end CategoryTheory

namespace AlgebraicGeometry.Scheme


section Layers

/- The constant inverse-image comparison is characterized by its adjunct. -/
private theorem fixedProEtaleConstantIso_homEquiv {X Y : Scheme.{u}} (f : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] (N : ModuleCat.{u + 1} B) :
    ((constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} B) terminalIsTerminal).comp
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)).homEquiv _ _
        ((fixedProEtaleConstantIso f B).hom.app N) =
      (constantSheafAdj (ProEt.topology Y) (ModuleCat.{u + 1} B)
        ((terminalIsTerminal : IsTerminal (⊤_ X.ProEt)).isTerminalObj
          (proEtaleBaseChange f) _)).unit.app N := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} B) terminalIsTerminal).comp
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)).ofNatIsoRight
        (Iso.refl _))
    (constantSheafAdj (ProEt.topology Y) (ModuleCat.{u + 1} B)
        ((terminalIsTerminal : IsTerminal (⊤_ X.ProEt)).isTerminalObj
          (proEtaleBaseChange f) _)) N
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  exact (Category.comp_id _).symm.trans h

/- Constants pulled back along `f` are compatible with restriction of coefficients. -/
private theorem fixedProEtaleConstantIso_restrictScalars {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    letI := ProEt.isContinuous_overPullback f
    Functor.whiskerLeft (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)
        (fixedProEtaleConstantIso f R).hom ≫
      (constantCommuteCompose (ProEt.topology Y)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).inv =
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (constantCommuteCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).inv
        (ProEtale.upperStar (ModuleCat.{u + 1} R) f) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} S))
        (G := sheafCompose (ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
            ProEtale.upperStar (ModuleCat.{u + 1} R) f)
        (H := ProEtale.upperStar (ModuleCat.{u + 1} S) f ⋙
          sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
        (normalizationPullbackIso (ProEt.topology X)
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (ProEt.topology Y) q).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (fixedProEtaleConstantIso f S).hom
        (sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) := by
  let := ProEt.isContinuous_overPullback f
  let hX : IsTerminal (⊤_ X.ProEt) := terminalIsTerminal
  let hY := hX.isTerminalObj (proEtaleBaseChange f) (⊤_ X.ProEt)
  let adj := (constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} R) hX).comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
  refine NatTrans.ext (funext fun M ↦ ?_)
  apply (adj.homEquiv _ _).injective
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  rw [Adjunction.homEquiv_naturality_right]
  have e1 := fixedProEtaleConstantIso_homEquiv f R ((ModuleCat.restrictScalars q).obj M)
  erw [e1]
  erw [constantSheafAdj_unit_app_comp_constantCommuteCompose_inv (ProEt.topology Y)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) hY M]
  have e2 := fixedProEtaleConstantIso_homEquiv f S M
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app] at e2 ⊢
  have hm := unit_mateEquiv_symm (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) f)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
    (TwoSquare.mk (ProEtale.lowerStar (ModuleCat.{u + 1} S) f)
      (sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
      (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
      (ProEtale.lowerStar (ModuleCat.{u + 1} R) f) (𝟙 _)) ((constantSheaf (ProEt.topology X)
          (ModuleCat.{u + 1} S)).obj M)
  have hl := constantSheafAdj_unit_app_comp_constantCommuteCompose_inv (ProEt.topology X)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) hX M
  have hn := (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.naturality
    ((constantCommuteCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).inv.app M)
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map, Functor.id_map] at e2 hn ⊢
  set Γ := (sheafSections (ProEt.topology X) (ModuleCat.{u + 1} R)).obj (op (⊤_ X.ProEt))
    with hΓ
  have step1 : Γ.map ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app
      ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj
        ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q).obj M))) ≫
      Γ.map ((ProEtale.lowerStar (ModuleCat.{u + 1} R) f).map
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) f).map ((constantCommuteCompose
          (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).inv.app M))) =
      Γ.map ((constantCommuteCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).inv.app M) ≫
      Γ.map ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app
        ((sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).obj
          ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} S)).obj M))) := by
    rw [← Γ.map_comp, ← Γ.map_comp]
    exact congrArg Γ.map hn.symm
  have step2 : Γ.map ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app
        ((sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).obj
          ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} S)).obj M))) ≫
      Γ.map ((ProEtale.lowerStar (ModuleCat.{u + 1} R) f).map
        ((normalizationPullbackIso (ProEt.topology X)
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (ProEt.topology Y) q).hom.app
            ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} S)).obj M))) =
      Γ.map ((sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          q)).map
        ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) f).unit.app
          ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} S)).obj M))) := by
    rw [← Γ.map_comp]
    congr 1
    erw [NatTrans.id_app, Category.comp_id] at hm
    exact hm.symm
  erw [reassoc_of% step1]
  rw [← Category.assoc, hl]
  erw [reassoc_of% step2]
  rw [← e2]
  simp only [Functor.map_comp]
  rfl


/- Adjuncts and the comparison of right adjoints. -/
private theorem homEquiv_comp_rightAdjointUniq_hom_app {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') {x : C} {y : D}
    (f : F.obj x ⟶ y) :
    adj1.homEquiv _ _ f ≫ (adj1.rightAdjointUniq adj2).hom.app y = adj2.homEquiv _ _ f := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc]
  have hn := (adj1.rightAdjointUniq adj2).hom.naturality f
  rw [hn, ← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]

/- The comparison of constants is characterized by its adjunct. -/
private theorem comparisonConstantIso_homEquiv (X : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] (N : ModuleCat.{u + 1} B) :
    ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} B)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X)).homEquiv _ _
        ((ProEtale.constantSheafCompComparisonUpperStarIso (ModuleCat.{u + 1} B) X).hom.app N) =
      (constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} B)
        (ProEt.isTerminalMkId X)).unit.app N := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} B)).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X)).ofNatIsoRight
        (ProEtale.comparisonLowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} B) X))
    (constantSheafΓAdj (ProEt.topology X) (ModuleCat.{u + 1} B)) N
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have hu := Adjunction.unit_rightAdjointUniq_hom_app
    (constantSheafΓAdj (ProEt.topology X) (ModuleCat.{u + 1} B))
    (constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} B) (ProEt.isTerminalMkId X)) N
  rw [← hu]
  erw [← h]
  simp only [ProEtale.comparisonLowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.refl_hom,
    Category.assoc, Category.id_comp]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  exact (homEquiv_comp_rightAdjointUniq_hom_app
    (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} B)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)) _).symm

private theorem comparisonConstantIso_restrictScalars (X : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    Functor.whiskerLeft (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)
        (ProEtale.constantSheafCompComparisonUpperStarIso (ModuleCat.{u + 1} R) X).hom ≫
      (constantCommuteCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).inv =
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (constantCommuteCompose X.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).inv
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))
        (G := sheafCompose X.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X)
        (H := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X ⋙
          sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
        (normalizationPullbackIso X.smallEtaleTopology
          (toProEt X) (ProEt.topology X) q).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (ProEtale.constantSheafCompComparisonUpperStarIso (ModuleCat.{u + 1} S)
          X).hom
        (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) := by
  let hX := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
  let hY := ProEt.isTerminalMkId X
  let adj := (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} R) hX).comp
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X)
  refine NatTrans.ext (funext fun M ↦ ?_)
  apply (adj.homEquiv _ _).injective
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  rw [Adjunction.homEquiv_naturality_right]
  have e1 := comparisonConstantIso_homEquiv X R ((ModuleCat.restrictScalars q).obj M)
  erw [e1]
  erw [constantSheafAdj_unit_app_comp_constantCommuteCompose_inv (ProEt.topology X)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) hY M]
  have e2 := comparisonConstantIso_homEquiv X S M
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app] at e2 ⊢
  have hm := unit_mateEquiv_symm (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} S) X)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X)
    (TwoSquare.mk (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} S) X)
      (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
      (sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} R) X) (𝟙 _)) ((constantSheaf
          X.smallEtaleTopology (ModuleCat.{u + 1} S)).obj M)
  have hl := constantSheafAdj_unit_app_comp_constantCommuteCompose_inv X.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) hX M
  have hn := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).unit.naturality
    ((constantCommuteCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).inv.app M)
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map, Functor.id_map] at e2 hn ⊢
  set Γ := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
    (op (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem @AlgebraicGeometry.Etale
        X)))
    with hΓ
  have step1 : Γ.map ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).unit.app
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
        ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q).obj M))) ≫
      Γ.map ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} R) X).map
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).map ((constantCommuteCompose
          X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).inv.app M))) =
      Γ.map ((constantCommuteCompose X.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).inv.app M) ≫
      Γ.map ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).unit.app
        ((sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)).obj M))) := by
    rw [← Γ.map_comp, ← Γ.map_comp]
    exact congrArg Γ.map hn.symm
  have step2 : Γ.map ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).unit.app
        ((sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)).obj M))) ≫
      Γ.map ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} R) X).map
        ((normalizationPullbackIso X.smallEtaleTopology
          (toProEt X) (ProEt.topology X) q).hom.app
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)).obj M))) =
      Γ.map ((sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          q)).map
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} S) X).unit.app
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)).obj M))) := by
    rw [← Γ.map_comp]
    congr 1
    erw [NatTrans.id_app, Category.comp_id] at hm
    exact hm.symm
  erw [reassoc_of% step1]
  rw [← Category.assoc, hl]
  erw [reassoc_of% step2]
  rw [← e2]
  simp only [Functor.map_comp]
  rfl

end Layers


section Realization

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso

/- The pulled-back constant section of a constant module sheaf. -/
private def pulledConstantSection {X Z : Scheme.{u}} (g : Z ⟶ X) (B : Type (u + 1)) [CommRing B]
    (N : ModuleCat.{u + 1} B) (x : N) :
    ((proEtaleRingModulePullback g (adicLisseConstantRing X B)
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _)).obj
        ((adicLisseConstantModules X B).obj N)).val.obj
          (op ((proEtaleBaseChange g).obj (⊤_ X.ProEt))) :=
  ((proEtaleRingModuleAdjunction g (adicLisseConstantRing X B)
    ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _)).unit.app
      ((adicLisseConstantModules X B).obj N)).val.app (op (⊤_ X.ProEt))
        (constantAdicModuleSection X B N (op (⊤_ X.ProEt)) x)

/- Maps out of a pulled-back constant module sheaf are determined by the pulled-back
constant sections. -/
private theorem pulledConstant_ext {X Z : Scheme.{u}} (g : Z ⟶ X) (B : Type (u + 1))
    [CommRing B] (N : ModuleCat.{u + 1} B)
    {Y : proEtaleRingModules Z ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))}
    (φ ψ : (proEtaleRingModulePullback g (adicLisseConstantRing X B)
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _)).obj
        ((adicLisseConstantModules X B).obj N) ⟶ Y)
    (h : ∀ x : N, φ.val.app _ (pulledConstantSection g B N x) =
      ψ.val.app _ (pulledConstantSection g B N x)) : φ = ψ := by
  let adj := (PresheafOfModules.sheafificationAdjunction.{u + 1} (adicLisseConstantUnit X B)).comp
    (proEtaleRingModuleAdjunction g (adicLisseConstantRing X B)
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _))
  apply (adj.homEquiv _ _).injective
  refine PresheafOfModules.hom_ext (fun V ↦ ?_)
  ext x
  have hV : ∀ f : (proEtaleRingModulePullback g (adicLisseConstantRing X B)
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _)).obj
        ((adicLisseConstantModules X B).obj N) ⟶ Y,
      (adj.homEquiv _ _ f).app V x = Y.val.map
        ((proEtaleBaseChange g).map (terminal.from V.unop)).op
          (f.val.app _ (pulledConstantSection g B N x)) := by
    intro f
    rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
    simp only [PresheafOfModules.comp_app, Functor.comp_map, ModuleCat.comp_apply]
    rw [← PresheafOfModules.naturality_apply]
    unfold pulledConstantSection constantAdicModuleSection
    have n1 := PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction.{u + 1} (adicLisseConstantUnit X B)).unit.app
        ((siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) B ⋙
          PresheafOfModules.pushforward₀
            ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
            ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of B))).obj N))
      (terminal.from V.unop).op x
    have n2 := PresheafOfModules.naturality_apply
      ((proEtaleRingModuleAdjunction g (adicLisseConstantRing X B)
        ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _)).unit.app
          ((adicLisseConstantModules X B).obj N)).val (terminal.from V.unop).op
      (((PresheafOfModules.sheafificationAdjunction.{u + 1} (adicLisseConstantUnit X B)).unit.app
        ((siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) B ⋙
          PresheafOfModules.pushforward₀
            ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
            ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of B))).obj N)).app
              (op (⊤_ X.ProEt)) x)
    exact congrArg _ ((congrArg _ n1).trans n2)
  exact (hV φ).trans ((congrArg _ (h x)).trans (hV ψ).symm)


/- The realization section of a fixed-coefficient section. -/
private def fsrSection {X Z : Scheme.{u}} (g : Z ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (j : ℕ)
    (K : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1))))
    (V : Z.ProEtᵒᵖ) (y : K.obj.obj V) :
    ((lisseTowerFiniteSheafRealization g d j).obj K).val.obj V :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1} (lisseTowerFiniteScalarMap g d j)).unit.app
    ((ProEtale.finiteCoefficientModulePresheaf Z.ProEt (A ⧸ d.ideal ^ (j + 1))).obj K.obj)).app V
        y

/- Forgetting the realized module structure returns the original section. -/
private theorem fixedForgetIso_fsrSection {X Z : Scheme.{u}} (g : Z ⟶ X) {A : Type (u + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)
    (K : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)))
    (V : Z.ProEtᵒᵖ) (y : K.obj.obj V) :
    ((lisseTowerFixedForgetIso g d j).hom.app K).hom.app V
      (fsrSection g d j ((sheafCompose (ProEt.topology Z)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal j))).obj
          K) V y) = y := by
  unfold lisseTowerFixedForgetIso lisseTowerCoefficientRealizationForgetIso
  simp only [Functor.comp_obj, id_eq, Iso.trans_hom, Functor.isoWhiskerLeft_hom, asIso_hom,
    NatTrans.comp_app, ObjectProperty.ι_obj, Functor.associator_hom_app, Functor.id_obj,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.comp_id,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    sheafificationAdjunction_counit_app_val, NatTrans.id_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply]
  have h := toSheafify_sheafifyLift (ProEt.topology Z)
    (𝟙 ((sheafCompose (ProEt.topology Z) (forget₂ (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))
      AddCommGrpCat.{u + 1})).obj K).obj)
    ((sheafCompose (ProEt.topology Z) (forget₂ (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))
      AddCommGrpCat.{u + 1})).obj K).property
  exact congrArg (fun φ ↦ (φ.app V).hom y) h




/- Pulled-back constant sections are natural in the module. -/
private theorem pulledConstantSection_naturality {X Z : Scheme.{u}} (g : Z ⟶ X)
    (B : Type (u + 1)) [CommRing B] {N N' : ModuleCat.{u + 1} B} (f : N ⟶ N') (x : N) :
    ((adicLisseConstantModules X B ⋙ proEtaleRingModulePullback g (adicLisseConstantRing X B)
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _)).map f).val.app _
        (pulledConstantSection g B N x) = pulledConstantSection g B N' (f x) := by
  have h1 := (proEtaleRingModuleAdjunction g (adicLisseConstantRing X B)
    ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _)).unit.naturality
      ((adicLisseConstantModules X B).map f)
  have h2 := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (adicLisseConstantUnit X B)).unit.naturality
      ((siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) B ⋙
        PresheafOfModules.pushforward₀
          ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
          ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of B))).map f)
  have e1 := congrArg (fun φ ↦ (φ.val.app (op (⊤_ X.ProEt)))
    (constantAdicModuleSection X B N (op (⊤_ X.ProEt)) x)) h1
  have e2 := congrArg (fun φ ↦ (φ.app (op (⊤_ X.ProEt))) x) h2
  simp only [Functor.id_map, Functor.comp_map] at e1 e2
  unfold pulledConstantSection
  refine Eq.trans ?_ (e1.symm.trans ?_)
  · rfl
  · exact congrArg (fun z ↦ ((proEtaleRingModuleAdjunction g (adicLisseConstantRing X B)
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _)).unit.app
        ((adicLisseConstantModules X B).obj N')).val.app (op (⊤_ X.ProEt)) z) e2.symm


/- The restriction/pullback comparison sends pulled-back sections to pulled-back sections. -/
private theorem pullbackInv_unit {U V : Scheme.{u}} (f : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)
    (M : proEtaleRingModules V SV) (W : V.ProEtᵒᵖ) (c : M.val.obj W) :
    ((proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm).app M).val.app
        ((proEtaleBaseChange f).op.obj W)
      (((proEtaleRingModuleAdjunction f RV RU cR).unit.app
        ((proEtaleRingRestrictScalars aV).obj M)).val.app W (restrictElem _ M W c)) =
    restrictElem _ ((proEtaleRingModulePullback f SV SU cS).obj M) _
      (((proEtaleRingModuleAdjunction f SV SU cS).unit.app M).val.app W c) := by
  let adj := proEtaleRingModuleAdjunction f RV RU cR
  let ψ := (proEtaleRingRestrictScalars aV).map
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app M) ≫
    (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app
      ((proEtaleRingModulePullback f SV SU cS).obj M)
  have hInv : (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm).app M =
      (adj.homEquiv _ _).symm ψ := by
    rw [Adjunction.homEquiv_counit]
    change proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M = _
    unfold proEtaleRingRestrictionPullbackApp
    rw [Functor.map_comp, Category.assoc]
  have key : adj.unit.app _ ≫ (proEtaleRingModuleDirectImage f RV RU cR).map
      ((proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm).app M) = ψ := by
    rw [hInv]
    exact (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have e := congrArg (fun φ ↦ φ.val.app W (restrictElem _ M W c)) key
  refine e.trans ?_
  exact (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique
    f RV SV RU SU aV aU cR cS comm)).1 _ W _

/- Sections of a sheaf with restricted coefficients. -/
private def sheafRestrictElem {Z : Scheme.{u}} {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (K : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} S)) (V : Z.ProEtᵒᵖ)
    (y : K.obj.obj V) :
    ((sheafCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)).obj K).obj.obj V :=
  y

/- Chaining four elementwise equations. -/
private theorem chain4_eq {α β γ δ ε : Type*} {f₁ : α → β} {f₂ : β → γ} {f₃ : γ
    → δ}
    {f₄ : δ → ε} {x : α} {a : β} {b : γ} {c : δ} {y : ε} (h₁ : f₁ x = a) (h₂ :
        f₂ a = b)
    (h₃ : f₃ b = c) (h₄ : f₄ c = y) : f₄ (f₃ (f₂ (f₁ x))) = y := by
  rw [h₁, h₂, h₃, h₄]

/- The constant section over the base-changed terminal object. -/
private def constSection {X Z : Scheme.{u}} (g : Z ⟶ X) (B : Type (u + 1)) [CommRing B]
    (N : ModuleCat.{u + 1} B) (x : N) :
    ((constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} B)).obj N).obj.obj
      (op ((proEtaleBaseChange g).obj (⊤_ X.ProEt))) :=
  (constantSheafAdj (ProEt.topology Z) (ModuleCat.{u + 1} B)
    ((terminalIsTerminal : IsTerminal (⊤_ X.ProEt)).isTerminalObj
      (proEtaleBaseChange g) _)).unit.app N x


/- The constant compositor sends constant sections to constant sections. -/
private theorem constantCommuteCompose_hom_constSection {X Z : Scheme.{u}} (g : Z ⟶ X)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) (N : ModuleCat.{u + 1} S)
    (z : N) :
    ((constantCommuteCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).hom.app N).hom.app _
        (sheafRestrictElem q _ _ (constSection g S N z)) =
      constSection g R _ (moduleRestrictElem q N z) := by
  have h := constantSheafAdj_unit_app_comp_constantCommuteCompose_inv (ProEt.topology Z)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)
    ((terminalIsTerminal : IsTerminal (⊤_ X.ProEt)).isTerminalObj (proEtaleBaseChange g) _) N
  have e := congrArg (fun φ ↦ ((constantCommuteCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).hom.app N).hom.app
        (op ((proEtaleBaseChange g).obj (⊤_ X.ProEt))) (φ z)) h
  refine e.symm.trans ?_
  change (((constantCommuteCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).inv.app N ≫
    (constantCommuteCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).hom.app N).hom.app _) _ = _
  rw [Iso.inv_hom_id_app]
  rfl


/- The constant presentation section. -/
private def betaSection {X Z : Scheme.{u}} (g : Z ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (j : ℕ) (M : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1)))
    (w : M) :
    ((constantPresentation (lisseTowerFiniteScalarMap g d j)).obj M).val.obj
      (op ((proEtaleBaseChange g).obj (⊤_ X.ProEt))) :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1} (lisseTowerFiniteScalarMap g d j)).unit.app
    ((constantModulePresheaf (C := Z.ProEt) (A ⧸ d.ideal ^ (j + 1))).obj M)).app _ w

/- The fixed-coefficient comparison of constant presentations on sections. -/
private theorem fixedConstantIso_inv_section {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)
    (M : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1))) (w : M) :
    letI : (ProEt.topology Z).PreservesSheafification
        (forget₂ (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1))) AddCommGrpCat.{u + 1}) :=
      Sheaf.preservesSheafification_of_adjunction (ProEt.topology Z)
        (ModuleCat.forget₂CoinduceAdj _)
    ((fixedConstantIso (ProEt.topology Z) (lisseTowerFiniteScalarMap g d j)).inv.app M).val.app _
      (fsrSection g d j ((constantSheaf (ProEt.topology Z)
        (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1)))).obj M) _ (constSection g _ M w)) =
    betaSection g d j M w := by
  let : (ProEt.topology Z).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1))) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction (ProEt.topology Z)
      (ModuleCat.forget₂CoinduceAdj _)
  have hh : ((fixedConstantIso (ProEt.topology Z) (lisseTowerFiniteScalarMap g d j)).hom.app
      M).val.app _ (betaSection g d j M w) = fsrSection g d j ((constantSheaf (ProEt.topology Z)
        (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1)))).obj M) _ (constSection g _ M w) := by
    have hn := (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (lisseTowerFiniteScalarMap g d j)).unit.naturality
        (fixedConstantSeed (ProEt.topology Z) (A ⧸ d.ideal ^ (j + 1)) M)
    exact (congrArg (fun φ ↦ φ.app (op ((proEtaleBaseChange g).obj (⊤_ X.ProEt))) w) hn).symm
  rw [← hh]
  change (((fixedConstantIso (ProEt.topology Z) (lisseTowerFiniteScalarMap g d j)).hom.app M ≫
    (fixedConstantIso (ProEt.topology Z) (lisseTowerFiniteScalarMap g d j)).inv.app M).val.app _)
      _ = _
  rw [Iso.hom_inv_id_app]
  rfl


/- The constant presentation section on the base. -/
private def alphaSection (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (j : ℕ) (M : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1)))
    (w : M) :
    ((constantPresentation (sourceScalarMap X d j)).obj M).val.obj (op (⊤_ X.ProEt)) :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1} (sourceScalarMap X d j)).unit.app
    ((constantModulePresheaf (C := X.ProEt) (A ⧸ d.ideal ^ (j + 1))).obj M)).app _ w

/- The pulled-back constant presentation comparison on sections. -/
private theorem canonicalPresentationPullIso_inv_section {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)
    (M : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1))) (w : M) :
    ((canonicalPresentationPullIso g ((pbcAdicRings X d).obj (op j)) (sourceScalarMap X d j)
      (lisseTowerFiniteScalarMap g d j) (sourceScalarMap_pull g d j)).inv.app M).val.app _
        (betaSection g d j M w) =
    ((proEtaleRingModuleAdjunction g ((pbcAdicRings X d).obj (op j))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op j))) (Iso.refl _)).unit.app
        ((constantPresentation (sourceScalarMap X d j)).obj M)).val.app (op (⊤_ X.ProEt))
      (alphaSection X d j M w) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (canonicalPresentationPullAdj g ((pbcAdicRings X d).obj (op j)) (sourceScalarMap X d j)
      (lisseTowerFiniteScalarMap g d j) (sourceScalarMap_pull g d j))
    (presentationAdjunction (lisseTowerFiniteScalarMap g d j)
      ((proEtaleBaseChange g).obj (⊤_ X.ProEt))
      ((terminalIsTerminal : IsTerminal (⊤_ X.ProEt)).isTerminalObj (proEtaleBaseChange g) _)) M
  have hk : ((canonicalPresentationPullIso g ((pbcAdicRings X d).obj (op j))
      (sourceScalarMap X d j) (lisseTowerFiniteScalarMap g d j)
        (sourceScalarMap_pull g d j)).hom.app M).val.app _
      (((proEtaleRingModuleAdjunction g ((pbcAdicRings X d).obj (op j))
        ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op j))) (Iso.refl _)).unit.app
          ((constantPresentation (sourceScalarMap X d j)).obj M)).val.app (op (⊤_ X.ProEt))
        (alphaSection X d j M w)) = betaSection g d j M w :=
    congrArg (fun f ↦ f w) h
  rw [← hk]
  change ((canonicalPresentationPullIso g ((pbcAdicRings X d).obj (op j))
      (sourceScalarMap X d j) (lisseTowerFiniteScalarMap g d j)
        (sourceScalarMap_pull g d j)).hom.app M ≫ (canonicalPresentationPullIso g
          ((pbcAdicRings X d).obj (op j)) (sourceScalarMap X d j) (lisseTowerFiniteScalarMap g d j)
            (sourceScalarMap_pull g d j)).inv.app M).val.app _ _ = _
  rw [Iso.hom_inv_id_app]
  rfl



/- Elementwise naturality of the module sheafification unit. -/
private theorem sheafification_map_unit_apply
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {B : Type (u + 1)} [CommRing B] {R : Sheaf J RingCat.{u + 1}}
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {P Q : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of B))} (f : P ⟶ Q)
    (V : Cᵒᵖ) (x : P.obj V) :
    ((PresheafOfModules.sheafification α).map f).val.app V
      (((PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.app P).app V x) =
    ((PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.app Q).app V (f.app V x) :=
  (congrArg (fun φ ↦ φ.app V x)
    ((PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.naturality f)).symm

/- The raw coefficient comparison on unit sections. -/
private theorem rawMap_unit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (r : R →+* S)
    {T U : Sheaf J RingCat.{u + 1}} (a : T ⟶ U)
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ T.obj)
    (β : (Functor.const Cᵒᵖ).obj (RingCat.of S) ⟶ U.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (ha : (Functor.const Cᵒᵖ).map (RingCat.ofHom r) ≫ β = α ≫ a.hom)
    (P : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of S))) (V : Cᵒᵖ)
    (x : P.obj V) :
    ((CoefficientSheafificationSquare.rawIso J r a α β ha).hom.app P).val.app V
      (((PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.app
        ((CoefficientSheafificationSquare.rawRestriction r).obj P)).app V x) =
    restrictElem a _ V (((PresheafOfModules.sheafificationAdjunction.{u + 1} β).unit.app P).app V
        x) := by
  unfold CoefficientSheafificationSquare.rawIso
  simp only [NatIso.ofComponents_hom_app, asIso_hom]
  have h : (PresheafOfModules.sheafificationAdjunction.{u + 1} α).homEquiv _ _
      (CoefficientSheafificationSquare.rawMap J r a α β ha P) =
      CoefficientSheafificationSquare.rawSeed J r a α β ha P := by
    unfold CoefficientSheafificationSquare.rawMap
    exact Equiv.apply_symm_apply (PresheafOfModules.sheafificationHomEquiv α) _
  rw [Adjunction.homEquiv_unit] at h
  have e := congrArg (fun φ ↦ φ.app V x) h
  refine e.trans ?_
  unfold CoefficientSheafificationSquare.rawSeed
  rfl

/- Transport of constant presentations sends unit sections to unit sections. -/
private theorem presentationTransportIso_section
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {B : Type (u + 1)} [CommRing B] {R S : Sheaf J RingCat.{u + 1}}
    (e : R ≅ S)
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    (β : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (h : β = α ≫ e.hom.hom) (M : ModuleCat.{u + 1} B) (V : Cᵒᵖ)
    (w : ((constantModulePresheaf (C := C) B).obj M).obj V) :
    ((canonicalPresentationTransportIso J e α β h).hom.app M).val.app V
      (((PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.app
        ((constantModulePresheaf (C := C) B).obj M)).app V w) =
    restrictElem e.hom _ V
      (((PresheafOfModules.sheafificationAdjunction.{u + 1} β).unit.app
        ((constantModulePresheaf (C := C) B).obj M)).app V w) := by
  unfold canonicalPresentationTransportIso
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp]
  rw [SheafOfModules.comp_val, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    PresheafOfModules.comp_app, ModuleCat.comp_apply, ModuleCat.comp_apply]
  refine (congrArg (fun z ↦ (((constantModulePresheaf (C := C) B).associator
    (PresheafOfModules.sheafification β) (SheafOfModules.restrictScalars e.hom)).symm.hom.app
      M).val.app V (((CoefficientSheafificationSquare.rawIso J (RingHom.id B) e.hom α β
        (by simpa using h)).hom.app ((constantModulePresheaf (C := C) B).obj M)).val.app V z))
    (sheafification_map_unit_apply α ((constantPresheafTransport (C := C) B).hom.app M) V
        w)).trans ?_
  have htw : ((constantPresheafTransport (C := C) B).hom.app M).app V w = w := rfl
  have h2 := rawMap_unit J (RingHom.id B) e.hom α β (by simpa using h)
    ((constantModulePresheaf (C := C) B).obj M) V w
  refine Eq.trans ?_ h2
  rfl


/- The source presentation comparison on sections. -/
private theorem canonicalSourcePresentationIso_section (X : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)
    (M : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1))) (w : M) :
    ((canonicalSourcePresentationIso X d j).hom.app M).val.app (op (⊤_ X.ProEt))
      (alphaSection X d j M w) =
    restrictElem ((adicLisseForget X).map (pbcLevelConstantComparison X d j).inv) _
      (op (⊤_ X.ProEt))
      (constantAdicModuleSection X (A ⧸ d.ideal ^ (j + 1)) M (op (⊤_ X.ProEt)) w) := by
  have h1 := presentationTransportIso_section (ProEt.topology X)
    ((adicLisseForget X).mapIso (pbcLevelConstantComparison X d j).symm) (sourceScalarMap X d j)
    (adicLisseConstantUnit X (A ⧸ d.ideal ^ (j + 1))) (by
        unfold sourceScalarMap
        rw [Category.assoc]
        change _ = _ ≫ ((adicLisseForget X).map (pbcLevelConstantComparison X d j).hom).hom ≫
          ((adicLisseForget X).map (pbcLevelConstantComparison X d j).inv).hom
        rw [← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp,
          Iso.hom_inv_id, CategoryTheory.Functor.map_id]
        rfl) M (op (⊤_ X.ProEt)) w
  have h2 := sheafification_map_unit_apply (adicLisseConstantUnit X (A ⧸ d.ideal ^ (j + 1)))
    ((adicConstantPresheafIso X (A ⧸ d.ideal ^ (j + 1))).hom.app M) (op (⊤_ X.ProEt)) w
  unfold canonicalSourcePresentationIso
  rw [Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  refine (congrArg (fun z ↦ ((Functor.isoWhiskerRight (Functor.isoWhiskerRight
    (adicConstantPresheafIso X (A ⧸ d.ideal ^ (j + 1)))
    (PresheafOfModules.sheafification (adicLisseConstantUnit X (A ⧸ d.ideal ^ (j + 1)))))
      (SheafOfModules.restrictScalars.{u + 1}
        ((adicLisseForget X).mapIso (pbcLevelConstantComparison X d j).symm).hom)).hom.app
      M).val.app (op (⊤_ X.ProEt)) z) h1).trans ?_
  exact h2

/- The fixed realization section of a section. -/
private def fixedSection {X Z : Scheme.{u}} (g : Z ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (j : ℕ)
    (K : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)))
    (V : Z.ProEtᵒᵖ) (y : K.obj.obj V) :
    ((lisseTowerFixedSheafRealization g d j).obj K).val.obj V :=
  fsrSection g d j ((sheafCompose (ProEt.topology Z)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal j))).obj K) V
      (sheafRestrictElem _ K V y)

/- The pulled-back constant section of a constant quotient module. -/
private def qSection {X Z : Scheme.{u}} (g : Z ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (j : ℕ) (N : ModuleCat.{u + 1} (lisseTowerEtaleRing d j))
    (x : N) :
    ((constantAdicQuotientModules X d j ⋙ proEtaleRingModulePullback g
      ((pbcAdicRings X d).obj (op j))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op j))) (Iso.refl _)).obj N).val.obj
        (op ((proEtaleBaseChange g).obj (⊤_ X.ProEt))) :=
  ((proEtaleRingModuleAdjunction g ((pbcAdicRings X d).obj (op j))
    ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op j))) (Iso.refl _)).unit.app
      ((constantAdicQuotientModules X d j).obj N)).val.app (op (⊤_ X.ProEt))
    (restrictElem _ _ _ (constantAdicModuleSection X (A ⧸ d.ideal ^ (j + 1))
      ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal j)).obj N)
        (op (⊤_ X.ProEt)) (moduleRestrictElem _ N x)))




/- Realization sections are natural. -/
private theorem fsrSection_naturality {X Z : Scheme.{u}} (g : Z ⟶ X) {A : Type (u + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)
    {K K' : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1)))} (ψ : K ⟶ K')
    (V : Z.ProEtᵒᵖ) (y : K.obj.obj V) :
    ((lisseTowerFiniteSheafRealization g d j).map ψ).val.app V (fsrSection g d j K V y) =
      fsrSection g d j K' V (ψ.hom.app V y) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (lisseTowerFiniteScalarMap g d j)).unit.naturality
      ((ProEtale.finiteCoefficientModulePresheaf Z.ProEt (A ⧸ d.ideal ^ (j + 1))).map ψ.hom)
  have e := congrArg (fun φ ↦ (φ.app V) y) h
  exact e.symm

/- Fixed realization sections are natural. -/
private theorem fixedSection_naturality {X Z : Scheme.{u}} (g : Z ⟶ X) {A : Type (u + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)
    {K K' : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))}
    (φ : K ⟶ K') (V : Z.ProEtᵒᵖ) (y : K.obj.obj V) :
    ((lisseTowerFixedSheafRealization g d j).map φ).val.app V (fixedSection g d j K V y) =
      fixedSection g d j K' V (φ.hom.app V y) :=
  fsrSection_naturality g d j ((sheafCompose (ProEt.topology Z)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal j))).map φ)
      V _

/- The constant compositor is compatible with the fixed realization sections. -/
private theorem constantCommuteCompose_fixedSection {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (M : ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) (x : M) :
    ((lisseTowerFixedSheafRealization g d (n + 1)).map
      ((constantCommuteCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (lisseTowerEtaleQuotient d n))).inv.app M)).val.app _
      (fixedSection g d (n + 1) _ _ (constSection g _ _ (moduleRestrictElem _ M x))) =
    fixedSection g d (n + 1) _ _ (sheafRestrictElem (lisseTowerEtaleQuotient d n) _ _
      (constSection g _ M x)) := by
  rw [fixedSection_naturality]
  congr 1
  have h := constantSheafAdj_unit_app_comp_constantCommuteCompose_inv (ProEt.topology Z)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))
    ((terminalIsTerminal : IsTerminal (⊤_ X.ProEt)).isTerminalObj (proEtaleBaseChange g) _) M
  exact congrArg (fun φ ↦ φ x) h

/- Evaluation of a composite on elements. -/
private theorem comp_elem_eq {Z : Scheme.{u}} {X₀ G₁ G₀ : Sheaf (ProEt.topology Z)
    AddCommGrpCat.{u + 1}}
    {V : Z.ProEtᵒᵖ} (F₁ : X₀ ⟶ G₁) (t : G₁ ⟶ G₀) (a : X₀.obj.obj V) (b :
        G₁.obj.obj V)
    (c : G₀.obj.obj V) (hF : F₁.hom.app V a = b) (ht : t.hom.app V b = c) :
    t.hom.app V (F₁.hom.app V a) = c := by
  rw [hF, ht]

/- The fixed restriction forgetful comparison is the identity on sections. -/
private theorem fixedRestrictForgetIso_sheafRestrictElem {Z : Scheme.{u}}
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    (K : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} S)) (V : Z.ProEtᵒᵖ) (y : K.obj.obj V) :
    ((lisseTowerFixedRestrictForgetIso (ProEt.topology Z) q).hom.app K).hom.app V
      (sheafRestrictElem q K V y) = y :=
  rfl

/- The normalized scalar square sends fixed realization sections to fixed realization
sections. -/
private theorem normalizedScalarSquare_fixedSection {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (V : Z.ProEtᵒᵖ) (y : K.obj.obj V) :
    ((lisseTowerNormalizedScalarSquare g d n).hom.app K).val.app V
      (fixedSection g d (n + 1) ((sheafCompose (ProEt.topology Z)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))).obj K) V
        (sheafRestrictElem (lisseTowerEtaleQuotient d n) K V y)) =
    restrictElem ((adicLisseForget Z).map ((adicTowerInverseImage g).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
      ((lisseTowerFixedSheafRealization g d n).obj K) V (fixedSection g d n K V y) := by
  have hFF : ∀ (j : ℕ) (K' : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d
      j)))
      (y' : K'.obj.obj V), ((lisseTowerFixedForgetIso g d j).hom.app K').hom.app V
        (fixedSection g d j K' V y') = y' := fun j K' y' ↦ fixedForgetIso_fsrSection g d j K' V y'
  have hn := lisseTowerNormalizedScalarSquare_sections g d n
  unfold LisseTowerScalarSquareSections lisseTowerScalarSquareNormalized at hn
  have e := congrArg (fun z ↦ z.app K) hn
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at e
  refine restrictElem_of_normalized
    ((adicLisseForget Z).map ((adicTowerInverseImage g).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
    ((lisseTowerNormalizedScalarSquare g d n).hom.app K)
    ((lisseTowerFixedForgetIso g d (n + 1)).hom.app ((sheafCompose (ProEt.topology Z)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))).obj K))
    ((lisseTowerFixedForgetIso g d n).hom.app K)
    ((lisseTowerRestrictForgetIso ((adicTowerInverseImage g).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).hom.app
        ((lisseTowerFixedSheafRealization g d n).obj K))
    ((lisseTowerFixedRestrictForgetIso (ProEt.topology Z) (lisseTowerEtaleQuotient d n)).hom.app K)
    e V ?_ (fun z ↦ rfl) _ _ y ?_ (hFF n K y)
  · have : IsIso (((sheafToPresheaf _ _).map
        ((lisseTowerFixedForgetIso g d n).hom.app K)).app V) := inferInstance
    exact (ConcreteCategory.bijective_of_isIso _).1
  · exact comp_elem_eq _ _ _ _ _ (hFF (n + 1) ((sheafCompose (ProEt.topology Z)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))).obj K)
      (sheafRestrictElem (lisseTowerEtaleQuotient d n) K V y))
      (fixedRestrictForgetIso_sheafRestrictElem (lisseTowerEtaleQuotient d n) K V y)

/- The restriction compositor is the identity on sections. -/
private theorem pbcRestrictComp_restrictElem {X : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (ψ : S ⟶ B)
    (χ : R ⟶ B) (h : φ ≫ ψ = χ) (M : pbcModules X B) (V : X.ProEtᵒᵖ) (y : M.val.obj V) :
    ((pbcRestrictComp φ ψ χ h).hom.app M).val.app V
      (restrictElem _ _ V (restrictElem _ M V y)) = restrictElem _ M V y :=
  (pbcRestrictComp_exists φ ψ χ h).exists.choose_spec M V y

/- The ordinary constant model sends constant sections to pulled-back constant sections. -/
private theorem canonicalOrdinaryConstantModel_section {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)
    (N : ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) (z : N) :
    ((canonicalOrdinaryConstantModel g d j).hom.app N).val.app _
      (fixedSection g d j _ _ (constSection g _ N z)) = qSection g d j N z := by
  unfold canonicalOrdinaryConstantModel
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  let qN := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal
      j)).obj N
  let P := proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op j))
    ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op j))) (Iso.refl _)
  let k := canonicalPresentationPullIso g ((pbcAdicRings X d).obj (op j)) (sourceScalarMap X d j)
    (lisseTowerFiniteScalarMap g d j) (sourceScalarMap_pull g d j)
  have e1 : ((lisseTowerFiniteSheafRealization g d j).map ((constantCommuteCompose
      (ProEt.topology Z) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (constantAdicQuotientMap d.ideal j))).hom.app N)).val.app
        (op ((proEtaleBaseChange g).obj (⊤_ X.ProEt)))
      (fixedSection g d j ((constantSheaf (ProEt.topology Z)
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))).obj N) _ (constSection g _ N z)) =
      fsrSection g d j ((constantSheaf (ProEt.topology Z)
        (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1)))).obj qN) _
        (constSection g _ qN (moduleRestrictElem _ N z)) := (fsrSection_naturality g d j
            ((constantCommuteCompose (ProEt.topology Z)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal j))).hom.app
        N)
    _ _).trans (congrArg (fsrSection g d j _ _)
      (constantCommuteCompose_hom_constSection g (constantAdicQuotientMap d.ideal j) N z))
  have e2 := fixedConstantIso_inv_section g d j qN (moduleRestrictElem _ N z)
  have e3 := canonicalPresentationPullIso_inv_section g d j qN (moduleRestrictElem _ N z)
  have e4 := (congrArg (fun φ ↦ φ.val.app (op (⊤_ X.ProEt)) (alphaSection X d j qN
    (moduleRestrictElem _ N z)))
    ((proEtaleRingModuleAdjunction g ((pbcAdicRings X d).obj (op j))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op j))) (Iso.refl _)).unit.naturality
        ((canonicalSourcePresentationIso X d j).hom.app qN))).symm.trans
    (congrArg (fun w ↦ ((proEtaleRingModuleAdjunction g ((pbcAdicRings X d).obj (op j))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op j))) (Iso.refl _)).unit.app
        ((constantAdicQuotientModules X d j).obj N)).val.app (op (⊤_ X.ProEt)) w)
      (canonicalSourcePresentationIso_section X d j qN (moduleRestrictElem _ N z)))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app]
  exact chain4_eq e1 e2 e3 e4

/- The right square sends pulled-back constant sections to pulled-back constant sections. -/
private theorem constantAdicOrdinaryQuotientRightIso_section {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)
    (N : ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) (z : N) :
    ((constantAdicOrdinaryQuotientRightIso g d j).inv.app N).val.app _
      (restrictElem _ _ _ (qSection g d j N z)) =
    pulledConstantSection g (AdicCompletion d.ideal A) _ (moduleRestrictElem _ N z) := by
  have := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).1
  have := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).2
  simp only [constantAdicOrdinaryQuotientRightIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, asIso_inv]
  let K := (constantAdicQuotientModules X d j).obj N
  let c : K.val.obj (op (⊤_ X.ProEt)) :=
    restrictElem ((adicLisseForget X).map (pbcLevelConstantComparison X d j).inv)
    ((adicLisseConstantModules X (A ⧸ d.ideal ^ (j + 1))).obj
    ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal j)).obj N))
      (op (⊤_ X.ProEt)) (constantAdicModuleSection X (A ⧸ d.ideal ^ (j + 1))
        ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal j)).obj
            N)
        (op (⊤_ X.ProEt)) (moduleRestrictElem _ N z))
  have h1 := pullbackInv_unit g (adicLisseConstantRing X (AdicCompletion d.ideal A))
    ((pbcAdicRings X d).obj (op j))
    ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
    ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op j)))
    ((constantAdicFiniteCone X d).π.app (op j))
    (constantAdicFiniteProjection g d j) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm) K (op (⊤_ X.ProEt)) c
  have h2 := congrArg (fun w ↦ (CategoryTheory.inv ((proEtaleRingRestrictionPullbackInv g
    (adicLisseConstantRing X (AdicCompletion d.ideal A))
    ((pbcAdicRings X d).obj (op j))
    ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
    ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op j)))
    ((constantAdicFiniteCone X d).π.app (op j))
    (constantAdicFiniteProjection g d j) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)).app K)).val.app _ w) h1
  have h3 := h2.symm.trans (by
    change ((proEtaleRingRestrictionPullbackInv g
      (adicLisseConstantRing X (AdicCompletion d.ideal A))
      ((pbcAdicRings X d).obj (op j))
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op j)))
      ((constantAdicFiniteCone X d).π.app (op j))
      (constantAdicFiniteProjection g d j) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)).app K ≫ CategoryTheory.inv
          _).val.app
        _ _ = _
    rw [IsIso.hom_inv_id])
  let k := constantAdicQuotientComparison X d j
  have hspec := (constantAdicQuotientScalarComparison X d j).exists.choose_spec.1 N
    (op (⊤_ X.ProEt)) z
  have hk : (k.inv.app N).val.app (op (⊤_ X.ProEt))
      (restrictElem ((adicLisseForget X).map ((constantAdicFiniteCone X d).π.app (op j))) K
        (op (⊤_ X.ProEt)) c) =
      constantAdicModuleSection X (AdicCompletion d.ideal A)
        ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.mk
          ((d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (j + 1)))).obj N)
        (op (⊤_ X.ProEt)) (moduleRestrictElem _ N z) := by
    have e := congrArg (fun w ↦ (k.inv.app N).val.app (op (⊤_ X.ProEt)) w) hspec
    refine e.symm.trans ?_
    change (k.hom.app N ≫ k.inv.app N).val.app _ _ = _
    rw [Iso.hom_inv_id_app]
    rfl
  have hn := (proEtaleRingModuleAdjunction g (adicLisseConstantRing X (AdicCompletion d.ideal A))
    ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
    (Iso.refl _)).unit.naturality (k.inv.app N)
  have hn' := congrArg (fun φ ↦ φ.val.app (op (⊤_ X.ProEt))
    (restrictElem ((adicLisseForget X).map ((constantAdicFiniteCone X d).π.app (op j))) K
      (op (⊤_ X.ProEt)) c)) hn
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    NatIso.isIso_inv_app]
  refine (congrArg (fun w ↦ ((proEtaleRingModulePullback g
    (adicLisseConstantRing X (AdicCompletion d.ideal A))
    ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
    (Iso.refl _)).map (k.inv.app N)).val.app _ w) h3).trans ?_
  refine hn'.symm.trans ?_
  exact congrArg (fun w ↦ ((proEtaleRingModuleAdjunction g
    (adicLisseConstantRing X (AdicCompletion d.ideal A))
    ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
    (Iso.refl _)).unit.app _).val.app (op (⊤_ X.ProEt)) w) hk

/- Restriction of scalars along consecutive quotients is the identity on sections. -/
private theorem algebraRestrictIso_section {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (M : ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) (x : M) :
    ((adicLisseConstantModules X (AdicCompletion d.ideal A) ⋙
      proEtaleRingModulePullback g (adicLisseConstantRing X (AdicCompletion d.ideal A))
        ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
        (Iso.refl _)).map ((lisseTowerOrdinaryAlgebraRestrictIso d n).hom.app M)).val.app _
      (pulledConstantSection g (AdicCompletion d.ideal A) _
        (moduleRestrictElem _ _ (moduleRestrictElem (lisseTowerEtaleQuotient d n) M x))) =
    pulledConstantSection g (AdicCompletion d.ideal A) _ (moduleRestrictElem _ M x) :=
  pulledConstantSection_naturality g _ _ _


end Realization

section Coherence

variable {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

attribute [local instance] CompletedConstantReduction.constant_additive

/- The realization layer of the coherence: the constant realization comparisons at levels
`n` and `n + 1` are compatible with the normalized scalar square, the restriction
compositors and the constant quotient comparisons. -/
private theorem constantRealization_coherence (M : ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) :
    (pbcRestrict (constantAdicFiniteProjection g d (n + 1))).map
        ((lisseTowerFixedSheafRealization g d (n + 1)).map
          ((constantCommuteCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{u + 1, u + 1,
            u + 1} (lisseTowerEtaleQuotient d n))).inv.app M)) ≫
      (pbcRestrict (constantAdicFiniteProjection g d (n + 1))).map
        ((lisseTowerNormalizedScalarSquare g d n).hom.app
          ((constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))).obj
            M)) ≫
      (pbcRestrictComp (constantAdicFiniteProjection g d (n + 1))
          ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
          (constantAdicFiniteProjection g d n)
          (constantAdicFiniteProjection_comp g d (n + 1) n (Nat.le_succ n))).hom.app
        ((lisseTowerFixedSheafRealization g d n).obj
          ((constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))).obj
            M)) ≫
      (pbcRestrict (constantAdicFiniteProjection g d n)).map
        ((canonicalOrdinaryConstantModel g d n).hom.app M) ≫
      (constantAdicOrdinaryQuotientRightIso g d n).inv.app M =
    (pbcRestrict (constantAdicFiniteProjection g d (n + 1))).map
        ((canonicalOrdinaryConstantModel g d (n + 1)).hom.app
          ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)).obj M))
              ≫
      (constantAdicOrdinaryQuotientRightIso g d (n + 1)).inv.app
        ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)).obj M) ≫
      (adicLisseConstantModules X (AdicCompletion d.ideal A) ⋙
        proEtaleRingModulePullback g (adicLisseConstantRing X (AdicCompletion d.ideal A))
          ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
          (Iso.refl _)).map ((lisseTowerOrdinaryAlgebraRestrictIso d n).hom.app M) := by
  let V := op ((proEtaleBaseChange g).obj (⊤_ X.ProEt))
  let q := lisseTowerEtaleQuotient d n
  let RM := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q).obj M
  exact realizationLayer_paste
    ((adicLisseForget Z).map (constantAdicFiniteProjection g d (n + 1)))
    ((adicLisseForget Z).map (constantAdicFiniteProjection g d n))
    ((adicLisseForget Z).map ((adicTowerInverseImage g).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
    (I := M) V _ _ _ _ _ _ _ _
    (fun x ↦ fixedSection g d (n + 1)
      ((constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))).obj
          RM)
      V (constSection g _ RM (moduleRestrictElem q M x)))
    (fun x ↦ fixedSection g d (n + 1)
      ((sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).obj
        ((constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))).obj M))
      V (sheafRestrictElem q _ V (constSection g _ M x)))
    (fun x ↦ fixedSection g d n
      ((constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))).obj M)
      V (constSection g _ M x))
    (fun x ↦ qSection g d n M x)
    (fun x ↦ qSection g d (n + 1) RM (moduleRestrictElem q M x))
    (fun x ↦ pulledConstantSection g (AdicCompletion d.ideal A) _
      (moduleRestrictElem _ _ (moduleRestrictElem q M x)))
    (fun x ↦ pulledConstantSection g (AdicCompletion d.ideal A) _ (moduleRestrictElem _ M x))
    (fun x ↦ constantCommuteCompose_fixedSection g d n M x)
    (fun x ↦ normalizedScalarSquare_fixedSection g d n _ V _)
    (fun y ↦ pbcRestrictComp_restrictElem _ _ _ _ _ V y)
    (fun x ↦ canonicalOrdinaryConstantModel_section g d n M x)
    (fun x ↦ constantAdicOrdinaryQuotientRightIso_section g d n M x)
    (fun x ↦ canonicalOrdinaryConstantModel_section g d (n + 1) RM _)
    (fun x ↦ constantAdicOrdinaryQuotientRightIso_section g d (n + 1) RM _)
    (fun x ↦ algebraRestrictIso_section g d n M x)
    (fun φ ψ h ↦ pulledConstant_ext g (AdicCompletion d.ideal A) _ φ ψ h)

/-- The ordinary constant comparisons are compatible with the coefficient restriction
from level `n + 1` to level `n`: both composites send every constant section to itself. -/
theorem lisseTowerOrdinaryConstant_coherence :
    (lisseTowerOrdinaryConstantScalarIso g a b d n ≪≫
        lisseTowerOrdinaryConstantModelIso g a b d n).hom =
      (Functor.isoWhiskerLeft
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))
          (lisseTowerOrdinaryConstantModelIso g a b d (n + 1)) ≪≫
        Functor.isoWhiskerRight (lisseTowerOrdinaryAlgebraRestrictIso d n)
          (adicLisseConstantModules X (AdicCompletion d.ideal A) ⋙
            proEtaleRingModulePullback g (adicLisseConstantRing X (AdicCompletion d.ideal A))
              ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
              (Iso.refl _))).hom := by
  apply constantComparisons_paste
  · intro M
    have h := congr_app (comparisonConstantIso_restrictScalars S (lisseTowerEtaleQuotient d n)) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at h
    exact h
  · intro M
    have h := congr_app (fixedProEtaleConstantIso_restrictScalars a (lisseTowerEtaleQuotient d n)) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at h
    exact h
  · intro M
    have h := congr_app (fixedProEtaleConstantIso_restrictScalars b (lisseTowerEtaleQuotient d n)) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at h
    exact h
  · intro M
    exact constantRealization_coherence g d n M

/-- The derived constant comparisons built from the natural constant model satisfy the
coefficient identity on every represented complex. -/
theorem lisseTowerConstantModel_coherence
    (K : CochainComplex (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) ℤ) :
    ((lisseTowerConstantScalarIso g a b d n) ≪≫
        lisseTowerConstantModelIso g a b d n (lisseTowerConstantModel g a b d n)).hom.app
          (DerivedCategory.Q.obj K) =
      (Functor.isoWhiskerLeft (normalizationModuleRestrict (lisseTowerEtaleQuotient d n))
          (lisseTowerConstantModelIso g a b d (n + 1) (lisseTowerConstantModel g a b d (n + 1)))
              ≪≫
        Functor.isoWhiskerRight (lisseTowerAlgebraRestrictIso d n)
          (constantAdicFiniteRealization g d)).hom.app (DerivedCategory.Q.obj K) := by
  have hL := (lisseTowerConstantScalarIso_represents g a b d n).comp
    (lisseTowerConstantModelIso_represents g a b d n)
  have hR := (((lisseTowerConstantModelIso_represents g a b d (n + 1)).whiskerLeft
    (DerivedPresentation.ofMap (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (lisseTowerEtaleQuotient d n)))).comp (derivedRepresents_associator_inv _ _ _)).comp
    ((lisseTowerAlgebraRestrictIso_represents d n).whiskerRight
      (constantAdicFiniteRealizationPresentation g d))
  have hR' := hR.congr (τ₀' := (lisseTowerOrdinaryConstantScalarIso g a b d n).hom ≫
      (lisseTowerOrdinaryConstantModelIso g a b d n).hom) rfl (by
    rw [← Iso.trans_hom, lisseTowerOrdinaryConstant_coherence]
    refine NatTrans.ext (funext fun M ↦ ?_)
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.comp_id])
  rw [Iso.trans_hom, DerivedRepresents.app_eq_app hL hR']
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.comp_id]

end Coherence

end AlgebraicGeometry.Scheme
