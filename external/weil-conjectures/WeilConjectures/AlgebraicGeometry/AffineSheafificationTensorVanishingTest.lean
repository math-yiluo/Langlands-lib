/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatRestriction
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.OpenRestrictionKFlatModel
import WeilConjectures.AlgebraicGeometry.OpenRestrictionTotalTensor

/-! # A global test sheaf for affine tensor cohomology

Source: Stacks Project, Tags 08CG and 08DX; exact restriction to an open subscheme.
(blueprint: lem-pc-affine-sheafification-tensor-vanishing-test).
-/

@[expose] public section

universe u w wX

open CategoryTheory

namespace AlgebraicGeometry.Scheme

-- Transport the pullback tensor structure to restriction and totalize its tensorators.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Limits MonoidalCategory in
private theorem restriction_totalTensor_iso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j]
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := SheafOfModules.monoidalCategory Y.sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Y.sheaf
    Nonempty (((Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor P N
        (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))) ≅
        CochainComplex.mapBifunctor
          (((Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj P)
          (((Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj N)
          (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Y.sheaf
  let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) := Modules.restrictFunctor j
  have : R.Additive := by
    change (Modules.restrictFunctor j).Additive
    exact Functor.additive_of_iso (Modules.restrictFunctorIsoPullback j).symm
  have : PreservesColimitsOfSize.{0, 0} R := by
    change PreservesColimitsOfSize.{0, 0} (Modules.restrictFunctor j)
    infer_instance
  let K := (((curriedTensor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).obj P).obj N
  have : R.PreservesTotalComplex K (.up ℤ) := fun _ => inferInstance
  let e₁ := (HomologicalComplex₂.mapTotalIso R K (.up ℤ)).symm
  let : (Modules.pullback j).Monoidal := Modules.pullbackMonoidal j
  let : R.Monoidal := Functor.Monoidal.transport
    (Modules.restrictFunctorIsoPullback j).symm
  let e (F G : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (Functor.Monoidal.μIso R F G).symm
  have he (F F' G G' : SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (f : F ⟶ F') (g : G ⟶ G') :
      R.map (f ⊗ₘ g) ≫ (e F' G').hom =
        (e F G).hom ≫ (R.map f ⊗ₘ R.map g) :=
    (Functor.OplaxMonoidal.δ_natural R f g).symm
  let e₂ :
      (((R.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj K) ≅
        (((curriedTensor (SheafOfModules.{u}
          (moduleRings Y.toRingedSpace))).mapBifunctorHomologicalComplex
            (.up ℤ) (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj P)).obj
              ((R.mapHomologicalComplex (.up ℤ)).obj N) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents (fun q ↦ e (P.X p) (N.X q))
        (by
          intro q q' hq
          change (e (P.X p) (N.X q)).hom ≫ R.obj (P.X p) ◁ R.map (N.d q q') =
            R.map (P.X p ◁ N.d q q') ≫ (e (P.X p) (N.X q')).hom
          simpa [R] using (he (P.X p) (P.X p) (N.X q) (N.X q') (𝟙 _) (N.d q q')).symm))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (e (P.X p) (N.X q)).hom ≫ R.map (P.d p p') ▷ R.obj (N.X q) =
          R.map (P.d p p' ▷ N.X q) ≫ (e (P.X p') (N.X q)).hom
        simpa [R] using (he (P.X p) (P.X p') (N.X q) (N.X q) (P.d p p') (𝟙 _)).symm)
  exact ⟨e₁ ≪≫ HomologicalComplex₂.total.mapIso e₂ (.up ℤ)⟩



set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Vanishing against the direct image of a spectrum module sheaf implies vanishing
against that sheaf after affine sheafification. This concerns one test sheaf and one
cohomological degree; it assumes neither Tor bounds nor boundedness of the complex.
Source: Stacks Project, Tags 08CG and 08DX, using exact open restriction and its
counit on direct images.
(blueprint: lem-pc-affine-sheafification-tensor-vanishing-test).

Proof: Put R = Gamma(S,U) and j = isoSpec.inv followed by U.ι. This is an open
immersion Spec R -> S. Take the actual test sheaf F = j_* G appearing in the statement.
Unpack the hypothesis as a K-flat representative C of K, its representing isomorphism,
and vanishing of H^i(C tensor F[0]). Exact restriction j^* preserves that vanishing,
commutes with total tensor, and preserves K-flatness. The open-immersion counit
j^* j_* G -> G is an isomorphism. Thus j^* C tensor G[0] has zero degree-i cohomology.
Transport the representing isomorphism hP through overEquiv and restriction by
isoSpec.inv. The restriction-composition isomorphisms, isoSpec's inverse identities,
and the counit of overEquiv identify Q(j^* C) with Q(tilde P). These exact transport
functors induce derived equivalences compatible with Q even when the localization
universes differ. Consequently j^* C, its transported representing isomorphism,
and the computed zero cohomology give the K-flat witness required by the conclusion.
For an empty affine open the same restriction and counit isomorphisms exist; its
module sheaves are zero. Zero rings, zero complexes and unbounded complexes require
no additional hypothesis. -/
theorem affine_sheafification_tensor_vanishing_test (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ V : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over V))]
    (U : S.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (S.presheaf.obj (.op U))).toRingedSpace))]
    (K : schemeDerivedCategory S)
    (P : CochainComplex (ModuleCat.{u} (S.presheaf.obj (.op U))) ℤ)
    (hP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj P)))
    (G : SheafOfModules.{u}
      (moduleRings (Spec (S.presheaf.obj (.op U))).toRingedSpace)) (i : ℤ)
    (h : schemeDerivedTensorCohomologyVanishes S K
      ((Modules.pushforward (hU.isoSpec.inv ≫ U.ι)).obj G) i) :
    schemeDerivedTensorCohomologyVanishes (Spec (S.presheaf.obj (.op U)))
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (S.presheaf.obj (.op U)))
          (SheafOfModules.{u}
            (moduleRings (Spec (S.presheaf.obj (.op U))).toRingedSpace)) _ _ _ _
          (tilde.functor (S.presheaf.obj (.op U)))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj P)) G i := by
  classical
  let X := Spec (S.presheaf.obj (.op U))
  let j : X ⟶ S := hU.isoSpec.inv ≫ U.ι
  let R : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := Modules.restrictFunctor j
  have : R.Additive := by
    change (Modules.restrictFunctor j).Additive
    exact Functor.additive_of_iso (Modules.restrictFunctorIsoPullback j).symm
  let RC := R.mapHomologicalComplex (.up ℤ)
  let := SheafOfModules.monoidalCategory S.sheaf
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor S.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj S.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  obtain ⟨C, hC, ⟨eC⟩, hz⟩ := h
  refine ⟨RC.obj C, isKFlat_restrict j C hC, ?_, ?_⟩
  · let O := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
    let E : SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U) ≌
        SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Modules.overEquiv U
    let V : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
      Modules.restrictFunctor hU.isoSpec.hom
    let W : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      Modules.restrictFunctor hU.isoSpec.inv
    have : V.Additive := by
      change (Modules.restrictFunctor hU.isoSpec.hom).Additive
      exact Functor.additive_of_iso (Modules.restrictFunctorIsoPullback _).symm
    have : W.Additive := by
      change (Modules.restrictFunctor hU.isoSpec.inv).Additive
      exact Functor.additive_of_iso (Modules.restrictFunctorIsoPullback _).symm
    have : CategoryTheory.Limits.PreservesFiniteLimits W := by
      change CategoryTheory.Limits.PreservesFiniteLimits (Modules.restrictFunctor hU.isoSpec.inv)
      infer_instance
    have : CategoryTheory.Limits.PreservesFiniteColimits W := by
      change CategoryTheory.Limits.PreservesFiniteColimits (Modules.restrictFunctor hU.isoSpec.inv)
      infer_instance
    have : CategoryTheory.Limits.HasBinaryBiproducts
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) :=
      CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts
    have : CategoryTheory.Limits.PreservesBinaryBiproducts E.functor :=
      CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts _
    have : E.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
    have : CategoryTheory.Limits.PreservesBinaryBiproducts E.inverse :=
      CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts _
    have : E.inverse.Additive := Functor.additive_of_preservesBinaryBiproducts _
    let H := E.functor ⋙ W
    have : CategoryTheory.Limits.PreservesFiniteLimits H :=
      CategoryTheory.Limits.comp_preservesFiniteLimits E.functor W
    have : CategoryTheory.Limits.PreservesFiniteColimits H :=
      CategoryTheory.Limits.comp_preservesFiniteColimits E.functor W
    let A := affinePerfectSheafification S U hU
    let T : ModuleCat.{u} (S.presheaf.obj (.op U)) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      tilde.functor (S.presheaf.obj (.op U))
    have : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
    have : T.Additive := inferInstanceAs (tilde.functor _).Additive
    have : A.Additive := by
      dsimp [A, affinePerfectSheafification]
      infer_instance
    let a : O ⋙ H ≅ R := (Functor.associator O E.functor W).symm ≪≫
      Functor.isoWhiskerRight (Modules.overFunctorEquiv U) W ≪≫
        (Modules.restrictFunctorComp hU.isoSpec.inv U.ι).symm
    let c : V ⋙ W ≅ 𝟭 _ :=
      (Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom).symm ≪≫
        Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId
    let b : A ⋙ H ≅ T :=
      (Functor.associator (T ⋙ V ⋙ E.inverse) E.functor W).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.associator (T ⋙ V) E.inverse E.functor ≪≫
            Functor.isoWhiskerLeft (T ⋙ V) E.counitIso ≪≫
              Functor.rightUnitor (T ⋙ V)) W ≪≫
        Functor.associator T V W ≪≫
        Functor.isoWhiskerLeft T c ≪≫ Functor.rightUnitor T
    obtain ⟨eP⟩ := hP
    let d : DerivedCategory.Q.obj ((O.mapHomologicalComplex (.up ℤ)).obj C) ≅
        DerivedCategory.Q.obj ((A.mapHomologicalComplex (.up ℤ)).obj P) :=
      (O.mapDerivedCategoryFactors.app C).symm ≪≫
        O.mapDerivedCategory.mapIso eC ≪≫ eP
    exact ⟨DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso a (.up ℤ)).app C).symm ≪≫
      (H.mapDerivedCategoryFactors.{w, wX}.app _).symm ≪≫
      H.mapDerivedCategory.{w, wX}.mapIso d ≪≫ H.mapDerivedCategoryFactors.{w, wX}.app _ ≪≫
      DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso b (.up ℤ)).app P)⟩
  · let N := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((Modules.pushforward j).obj G)
    let L := CochainComplex.mapBifunctor C N (MonoidalCategory.curriedTensor _)
    have : CategoryTheory.Limits.PreservesFiniteLimits R := by
      change CategoryTheory.Limits.PreservesFiniteLimits (Modules.restrictFunctor j)
      infer_instance
    have : CategoryTheory.Limits.PreservesFiniteColimits R := by
      change CategoryTheory.Limits.PreservesFiniteColimits (Modules.restrictFunctor j)
      infer_instance
    have hzR : CategoryTheory.Limits.IsZero ((RC.obj L).homology i) := by
      exact (R.map_isZero hz).of_iso ((L.sc i).mapHomologyIso R)
    obtain ⟨t⟩ := restriction_totalTensor_iso j C N
    let n : RC.obj N ≅ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G :=
      (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app _ ≪≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
          ((Modules.restrictFunctorAdjCounitIso j).app G)
    let B := ((MonoidalCategory.curriedTensor (SheafOfModules.{u}
      (moduleRings X.toRingedSpace))).map₂CochainComplex).obj (RC.obj C)
    exact hzR.of_iso (HomologicalComplex.homologyMapIso (t ≪≫ B.mapIso n).symm i)


end AlgebraicGeometry.Scheme
