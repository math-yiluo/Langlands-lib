/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionExtendHomology

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact sheafification of extended ordinary homology respects semilinear chain maps. -/
theorem tensorResolutionExtendedHomology_naturality {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c')
    (E : HomologicalComplex (ModuleCat.{u} A) c)
    (F : HomologicalComplex (ModuleCat.{u} B) c)
    (a : E ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex c).obj F)
    {i : ι} {i' : ι'} (hi : e.f i = i') :
    let TA := tilde.functor A
    let TB := tilde.functor B
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    letI : TA.PreservesHomology := tilde_preservesHomology A
    letI : TB.PreservesHomology := tilde_preservesHomology B
    let hE := tensorResolutionExtendLeftHomologyData e E hi (E.sc i).homologyData.left
    let hF := tensorResolutionExtendLeftHomologyData e F hi (F.sc i).homologyData.left
    R.map (hE.map TA).homologyIso.inv ≫
        (((((TA.mapHomologicalComplex c').obj (E.extend e))).sc i').mapHomologyIso R).inv ≫
        HomologicalComplex.homologyMap
          (tensorResolutionSemilinearComplexMap φ c' (E.extend e) (F.extend e)
            (tensorResolutionExtendSemilinear φ.hom e E F a)) i' =
      tensorResolutionSemilinearMap φ
        (HomologicalComplex.homologyMap a i ≫
          ((F.sc i).mapHomologyIso (ModuleCat.restrictScalars φ.hom)).hom) ≫
          (hF.map TB).homologyIso.inv := by
  dsimp only
  let U : ModuleCat.{u} B ⥤ ModuleCat.{u} A := ModuleCat.restrictScalars φ.hom
  let hE := (E.sc i).homologyData.left
  let hF := (F.sc i).homologyData.left
  let γ : ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) c i).map a)
      hE (hF.map U) := default
  have hg : γ.φH = HomologicalComplex.homologyMap a i ≫
      ((F.sc i).mapHomologyIso U).hom := by
    change γ.φH = ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) c i).map a) ≫
        (hF.map U).homologyIso.hom
    simpa only [hE, tensorResolution_chosenHomologyIso, Iso.refl_hom,
      Category.id_comp] using γ.homologyMap_comm.symm
  let γ' := tensorResolutionExtendHomologyMapData φ.hom e E F a hi hE hF γ
  have hh := tensorResolutionSemilinearMap_homologyData φ c' (E.extend e) (F.extend e)
    (tensorResolutionExtendSemilinear φ.hom e E F a) i'
    (tensorResolutionExtendLeftHomologyData e E hi hE)
    (tensorResolutionExtendLeftHomologyData e F hi hF) γ'
  change _ = tensorResolutionSemilinearMap φ γ.φH ≫ _ at hh
  rw [hg] at hh
  exact hh

end AlgebraicGeometry
