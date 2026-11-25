/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseSingleMapComposition
import WeilConjectures.AlgebraicGeometry.Single.SingleComplexQcqsHomologyMono
import WeilConjectures.AlgebraicGeometry.CounitStalkConditionFromLocalizedComparison
import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorFlat
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.FlatBaseDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Injectivity of relatively flat single base change

Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor.
(blueprint: lem-pc-standard-flat-single-base-change-mono).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem complex_qcoh (X : Scheme.{u})
    [HasDerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hG : ∀ i : ℤ, (G.X i).IsQuasicoherent) :
    schemeDerivedQCohProperty X (DerivedCategory.Q.obj G) := by
  intro n
  let S := G.sc n
  have : S.X₁.IsQuasicoherent := hG _
  have : S.X₂.IsQuasicoherent := hG _
  have : S.X₃.IsQuasicoherent := hG _
  have : (kernel S.g).IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel S.g
  have : (cokernel (kernel.lift S.g S.f S.zero)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_cokernel _
  let e : S.homology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
    S.leftHomologyIso.symm ≪≫ S.leftHomologyIsoCokernelLift
  exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    (((DerivedCategory.homologyFunctorFactors _ n).app G) ≪≫ e).symm inferInstance

private theorem single_qcoh_terms (X : Scheme.{u}) (M : X.Modules) [M.IsQuasicoherent]
    (i : ℤ) :
    (((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M).X i).IsQuasicoherent := by
  by_cases hi : i = 0
  · subst i
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).symm inferInstance
  · have h := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi
    have : (kernel (𝟙 M)).IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel (𝟙 M)
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      (h.iso (isZero_kernel_of_mono (𝟙 M))).symm inferInstance

-- The stalk and pinned counit comparisons unfold several shared module carriers.
/-- The canonical single-module base-change comparison is injective on cohomology.

Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor, specialized to
E = O_Y[0] and G = M[0], and Tag 0DJ9, lemma-single-complex-base-change.
(blueprint: lem-pc-standard-flat-single-base-change-mono).

Proof: Work locally on the new base and the original base, so both bases are
affine. On an affine source chart, relative flatness of M makes its module of
sections flat over the original base ring. The affine derived direct image is
therefore a flat module in degree zero; derived scalar extension computes it by
ordinary tensor product. The affine tensor-pullback section formula identifies
that tensor product with the sections of the pulled-back module. The canonical
mate followed by the left-derived counit is precisely this section comparison:
its component in degree zero is the tensor identification, and all other
cohomology objects are zero. In particular its degree-n map is injective.
For a general qcqs source, use the single-complex source-open induction of
Tag 0DJ9: compare the two Mayer--Vietoris triangles for U, V, their intersection
and union. The affine comparisons identify the local tensor-cohomology maps;
relative flatness makes them valid at every stalk, including on the
intersection. The long exact cohomology sequences and the five lemma propagate
the comparison along the quasi-compact-open induction. Take the injectivity half
of that degree-n conclusion. Finally exact open restriction detects monomorphisms
and gives the asserted global monomorphism. This argument includes zero M,
empty schemes, and negative n, and assumes neither flatness of g nor intrinsic
flatness of M over O_Y. -/
theorem standard_flat_single_baseChange_homology_mono
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (n : ℤ) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    Mono ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings A.toRingedSpace)) n).map
        (standardSingleBaseChangeMap p M g)) := by
  change SheafOfModules.{u} (moduleRings Y.toRingedSpace) at M
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let q := pullback.fst p g
  let r := pullback.snd p g
  let sq : IsPullback q r p g := IsPullback.of_hasPullback p g
  let G := (CochainComplex.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
  let E := (Scheme.Modules.tensorPullback q).mapHomologicalComplex (.up ℤ)
  have hG : schemeDerivedQCohProperty Y (DerivedCategory.Q.obj G) :=
    complex_qcoh Y G (single_qcoh_terms Y M)
  have hEG : schemeDerivedQCohProperty (pullback p g) (DerivedCategory.Q.obj (E.obj G)) := by
    apply complex_qcoh
    intro i
    have : (G.X i).IsQuasicoherent := single_qcoh_terms Y M i
    let e := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction q)
    exact (SheafOfModules.isQuasicoherent (moduleRings (pullback p g).toRingedSpace)).prop_of_iso
      (e.app (G.X i)).symm (Scheme.Modules.isQuasicoherent_pullback q (G.X i))
  have hstalk := SingleComplexBaseChange.counit_stalkCondition_of_localizedComparison
    p r g q sq G (by
      intro z
      let := SingleComplexBaseChange.leftAlgebra p q z
      let := SingleComplexBaseChange.rightAlgebra p r g q sq z
      let := (SingleComplexBaseChange.tensorMap p r g q sq z).toAlgebra
      let := HasDerivedCategory.standard
        (ModuleCat.{u} (SingleComplexBaseChange.R p q z))
      let := HasDerivedCategory.standard
        (ModuleCat.{u} (SingleComplexBaseChange.B r z))
      apply ModuleCat.localizedComparison_isIso_of_kFlat_flat
      · let F := RingedSpace.moduleStalkFunctor Y.toRingedSpace (q z) ⋙
          ModuleCat.restrictScalars (algebraMap (SingleComplexBaseChange.R p q z)
            (SingleComplexBaseChange.A q z))
        let P := (F.mapHomologicalComplex (.up ℤ)).obj G
        apply CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat
        · refine ⟨0, fun i hi ↦ ?_⟩
          exact F.map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i
            (by omega))
        · intro i
          by_cases hi : i = 0
          · subst i
            have : Module.Flat (SingleComplexBaseChange.R p q z) (F.obj M) :=
              relative_flat_module_stalk p M hM (q z) rfl
            exact Module.Flat.of_linearEquiv
              (F.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M)).toLinearEquiv
          · have hz : IsZero (P.X i) :=
              F.map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
            let := ModuleCat.subsingleton_of_isZero hz
            change Module.Flat (SingleComplexBaseChange.R p q z) (P.X i)
            exact Module.Flat.of_retract
              (0 : P.X i →ₗ[SingleComplexBaseChange.R p q z] SingleComplexBaseChange.R p q z)
              (0 : SingleComplexBaseChange.R p q z →ₗ[SingleComplexBaseChange.R p q z] P.X i)
              (by ext; exact Subsingleton.elim _ _)
      · exact pullback_stalk_tensor_flat g p z rfl rfl
          (Classical.choose_spec
            (SingleComplexBaseChange.exists_tensorMap p r g q sq z)).1
          (Classical.choose_spec
            (SingleComplexBaseChange.exists_tensorMap p r g q sq z)).2)
  have hc := singleComplexBaseChange_homology_mono p r g q sq _ hG _ hEG _ hstalk n
  simp only [cast_eq] at hc
  let s : E.obj G ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback q).obj M) :=
    (HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.tensorPullback q) (.up ℤ) 0).hom.app M
  have hnorm : Scheme.picardTermwiseSingleMap q M =
      (SingleComplexBaseChange.counit q).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj G) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) (.up ℤ)).map s) := by
    exact Scheme.single_map_normalize q M
  change Mono ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings A.toRingedSpace)) n).map
      (schemeDerivedBaseChangeMap p r g q sq.w (DerivedCategory.Q.obj G) ≫
        (schemeDerivedDirectImage r).map (Scheme.picardTermwiseSingleMap q M)))
  rw [hnorm, (schemeDerivedDirectImage r).map_comp, ← Category.assoc, Functor.map_comp]
  have hr : IsIso ((schemeDerivedDirectImage r).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) (.up ℤ)).map s))) := by
    dsimp [s]
    infer_instance
  infer_instance

end AlgebraicGeometry
