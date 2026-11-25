/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSemilinear

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The chosen homology data compute the chosen homology by the identity. -/
theorem tensorResolution_chosenHomologyIso {C : Type*} [Category C]
    [HasZeroMorphisms C] (S : ShortComplex C) [S.HasHomology] :
    S.homologyData.left.homologyIso = Iso.refl _ := by
  change S.leftHomologyIso.symm ≪≫ S.leftHomologyIso = Iso.refl _
  simp

/-- The affine adjunction carries semilinear maps on ordinary homology to the
homology map of their associated-sheaf maps. -/
theorem tensorResolutionSemilinearMap_homologyData {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]
    {ι : Type*} (c : ComplexShape ι)
    (E : HomologicalComplex (ModuleCat.{u} A) c)
    (F : HomologicalComplex (ModuleCat.{u} B) c)
    (a : E ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex c).obj F)
    (i : ι) (hE : (E.sc i).LeftHomologyData) (hF : (F.sc i).LeftHomologyData)
    (γ : ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) c i).map a)
      hE (hF.map (ModuleCat.restrictScalars φ.hom))) :
    let TA := tilde.functor A
    let TB := tilde.functor B
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    letI : TA.PreservesHomology := tilde_preservesHomology A
    letI : TB.PreservesHomology := tilde_preservesHomology B
    R.map (hE.map TA).homologyIso.inv ≫
        ((((TA.mapHomologicalComplex c).obj E).sc i).mapHomologyIso R).inv ≫
        HomologicalComplex.homologyMap (tensorResolutionSemilinearComplexMap φ c E F a) i =
      tensorResolutionSemilinearMap φ γ.φH ≫ (hF.map TB).homologyIso.inv := by
  dsimp only
  let TA := tilde.functor A
  let TB := tilde.functor B
  let R := Scheme.Modules.restrictFunctor (Spec.map φ)
  let U : ModuleCat.{u} B ⥤ ModuleCat.{u} A := ModuleCat.restrictScalars φ.hom
  have : TA.PreservesHomology := tilde_preservesHomology A
  have : TB.PreservesHomology := tilde_preservesHomology B
  let δ : ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (Spec B).Modules c i).map
        (tensorResolutionSemilinearComplexMap φ c E F a))
      ((hE.map TA).map R) (hF.map TB) :=
    { φK := tensorResolutionSemilinearMap φ γ.φK
      φH := tensorResolutionSemilinearMap φ γ.φH
      commi := by
        change tensorResolutionSemilinearMap φ γ.φK ≫ tilde.map hF.i =
          R.map (tilde.map hE.i) ≫ tensorResolutionSemilinearMap φ (a.f i)
        rw [tensorResolutionSemilinearMap_postcomp, tensorResolutionSemilinearMap_precomp]
        congr 1
        exact γ.commi
      commf' := by
        symm
        simp only [ShortComplex.LeftHomologyData.map_f']
        change tensorResolutionSemilinearMap φ (a.f (c.prev i)) ≫ tilde.map hF.f' =
          R.map (tilde.map hE.f') ≫ tensorResolutionSemilinearMap φ γ.φK
        rw [tensorResolutionSemilinearMap_postcomp, tensorResolutionSemilinearMap_precomp]
        congr 1
        simpa only [ShortComplex.LeftHomologyData.map_f', HomologicalComplex.shortComplexFunctor,
          HomologicalComplex.shortComplexFunctor'] using γ.commf'.symm
      commπ := by
        symm
        change tensorResolutionSemilinearMap φ γ.φK ≫ tilde.map hF.π =
          R.map (tilde.map hE.π) ≫ tensorResolutionSemilinearMap φ γ.φH
        rw [tensorResolutionSemilinearMap_postcomp, tensorResolutionSemilinearMap_precomp]
        congr 1
        exact γ.commπ.symm }
  change R.map (hE.map TA).homologyIso.inv ≫
      (((E.sc i).map TA).mapHomologyIso R).inv ≫
      ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (Spec B).Modules c i).map
          (tensorResolutionSemilinearComplexMap φ c E F a)) = _
  rw [δ.homologyMap_eq, (hE.map TA).mapHomologyIso_eq R]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc]
  change R.map ((hE.map TA).homologyIso).inv ≫
      R.map ((hE.map TA).homologyIso).hom ≫
      ((hE.map TA).map R).homologyIso.inv ≫
      ((hE.map TA).map R).homologyIso.hom ≫
      tensorResolutionSemilinearMap φ γ.φH ≫ (hF.map TB).homologyIso.inv = _
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc]
  rfl

/-- The affine adjunction carries semilinear maps on ordinary homology to the
homology map of their associated-sheaf maps. -/
theorem tensorResolutionSemilinearMap_homology {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]
    {ι : Type*} (c : ComplexShape ι)
    (E : HomologicalComplex (ModuleCat.{u} A) c)
    (F : HomologicalComplex (ModuleCat.{u} B) c)
    (a : E ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex c).obj F)
    (i : ι) :
    let TA := tilde.functor A
    let TB := tilde.functor B
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    letI : TA.PreservesHomology := tilde_preservesHomology A
    letI : TB.PreservesHomology := tilde_preservesHomology B
    R.map ((E.sc i).mapHomologyIso TA).inv ≫
        ((((TA.mapHomologicalComplex c).obj E).sc i).mapHomologyIso R).inv ≫
        HomologicalComplex.homologyMap (tensorResolutionSemilinearComplexMap φ c E F a) i =
      tensorResolutionSemilinearMap φ
          (HomologicalComplex.homologyMap a i ≫
            ((F.sc i).mapHomologyIso (ModuleCat.restrictScalars φ.hom)).hom) ≫
        ((F.sc i).mapHomologyIso TB).inv := by
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
  have hh := tensorResolutionSemilinearMap_homologyData φ c E F a i hE hF γ
  rw [hg] at hh
  exact hh

end AlgebraicGeometry
