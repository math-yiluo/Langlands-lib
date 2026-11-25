/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionExtendNaturality
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSemilinearHomology

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Homology data extended by zero retain their cycles and homology objects. -/
noncomputable def tensorResolutionExtendLeftHomologyData
    {C : Type*} [Category C] [HasZeroObject C] [HasZeroMorphisms C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (E : HomologicalComplex C c)
    {i : ι} {i' : ι'} (hi : e.f i = i') (hE : (E.sc i).LeftHomologyData) :
    ((E.extend e).sc i').LeftHomologyData :=
  HomologicalComplex.extend.leftHomologyData E e hi rfl rfl rfl rfl hE

/-- Extension by zero preserves a specified semilinear map on homology data. -/
noncomputable def tensorResolutionExtendHomologyMapData
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c')
    (E : HomologicalComplex (ModuleCat.{u} A) c)
    (F : HomologicalComplex (ModuleCat.{u} B) c)
    (a : E ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex c).obj F)
    {i : ι} {i' : ι'} (hi : e.f i = i')
    (hE : (E.sc i).LeftHomologyData) (hF : (F.sc i).LeftHomologyData)
    (γ : ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) c i).map a)
      hE (hF.map (ModuleCat.restrictScalars φ))) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) c' i').map
        (tensorResolutionExtendSemilinear φ e E F a))
      (tensorResolutionExtendLeftHomologyData e E hi hE)
      ((tensorResolutionExtendLeftHomologyData e F hi hF).map
        (ModuleCat.restrictScalars φ)) := by
  let U : ModuleCat.{u} B ⥤ ModuleCat.{u} A := ModuleCat.restrictScalars φ
  let h₁ := tensorResolutionExtendLeftHomologyData e E hi hE
  let h₂ := (tensorResolutionExtendLeftHomologyData e F hi hF).map U
  let a' := tensorResolutionExtendSemilinear φ e E F a
  let f := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) c' i').map a'
  have hc : γ.φK ≫ h₂.i = h₁.i ≫ f.τ₂ := by
    change γ.φK ≫ U.map (hF.i ≫ (F.extendXIso e hi).inv) =
      (hE.i ≫ (E.extendXIso e hi).inv) ≫ a'.f i'
    dsimp only [a']
    rw [tensorResolutionExtendSemilinear_f φ e E F a hi]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
    exact γ.commi_assoc _
  refine { φK := γ.φK, φH := γ.φH, commi := hc, commf' := ?_, commπ := ?_ }
  · apply (cancel_mono h₂.i).1
    rw [Category.assoc, hc, ← Category.assoc,
      ShortComplex.LeftHomologyData.f'_i, Category.assoc,
      ShortComplex.LeftHomologyData.f'_i]
    exact f.comm₁₂.symm
  · exact γ.commπ

end AlgebraicGeometry
