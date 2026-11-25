/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.GlobalTensorPullbackMatesIsIso
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.LocalizedOpenKFlatTensorRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Comparison with prescribed local strictly perfect tensor models

Source: Stacks Project, Cohomology of Sheaves, Tags 09J5 and 06YH; Schemes,
Tag 08DX (blueprint: lem-sc-strict-perfect-tensor-local-comparison).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance sptc_globalTensorZero (X : Scheme.{u}) :
    (@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf

local instance sptc_globalTensorObjZero (X : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    ((@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

local instance sptc_localTensorZero (X : Scheme.{u}) (U : X.Opens) :
    (@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor (X.sheaf.over U)

local instance sptc_localTensorObjZero (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
    ((@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (X.sheaf.over U) M

attribute [local instance] Scheme.Modules.globalPullbackMatesColimits

local instance sptc_localColimits (X : Scheme.{u}) (U : X.Opens) :
    CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) := inferInstance

local instance sptc_globalTotal (X : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    HomologicalComplex.HasMapBifunctor P N
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)) (.up ℤ) :=
  fun _ ↦ inferInstance

local instance sptc_localTotal (X : Scheme.{u}) (U : X.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor A B
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U))) (.up ℤ) :=
  fun _ ↦ inferInstance

/-- Strictly perfect complexes are K-flat on the localized ringed space.
Source: Stacks Project, Tag 06YD, bounded-above flat complexes are K-flat.
(blueprint: lem-sc-strict-perfect-tensor-local-comparison).
-/
private theorem strictPerfect_isKFlat_local (X : Scheme.{u}) (U : X.Opens)
    (A : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hA : Scheme.IsStrictlyPerfect X U A) :
    CochainComplex.IsKFlatTensor (R := X.sheaf.over U) A := by
  classical
  let C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let : MonoidalCategory C := SheafOfModules.monoidalCategory (X.sheaf.over U)
  let : SymmetricCategory C := SheafOfModules.symmetricCategory (X.sheaf.over U)
  have : MonoidalPreadditive C :=
    Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1
  let : MonoidalClosed C :=
    Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).2.1
  have : IsGrothendieckAbelian.{u} C :=
    SheafOfModules.isGrothendieckAbelian ((moduleRings X.toRingedSpace).over U)
  obtain ⟨⟨a, b, hb⟩, hf⟩ := hA
  have : A.IsStrictlyGE a := (A.isStrictlyGE_iff a).2 (fun i hi ↦ hb i (Or.inl hi))
  have : A.IsStrictlyLE b := (A.isStrictlyLE_iff b).2 (fun i hi ↦ hb i (Or.inr hi))
  have hflat (i : ℤ) : ObjectProperty.flat (A.X i) := by
    obtain ⟨m, ι, π, hι⟩ := hf i
    exact ObjectProperty.flat_of_retract ⟨ι, π, hι⟩
      (ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _))
  have hk := CochainComplex.kFlat_of_bounded_of_flat A a b hflat
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic] at hk
  intro F hF
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
    (hk ((HomotopyCategory.quotient C (.up ℤ)).obj F)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hF)).2

private theorem local_kFlat_tensor_invariance (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (P N A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hN : CochainComplex.IsKFlatTensor (R := X.sheaf.over U) N)
    (hA : CochainComplex.IsKFlatTensor (R := X.sheaf.over U) A)
    (eA : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj A)
    (eB : DerivedCategory.Q.obj N ≅ DerivedCategory.Q.obj B) :
    Nonempty (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U)))) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor A B
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U))))) := by
  let C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  -- Mapping cones and homology use these same structures at every step.
  let : Abelian C := inferInstance
  let : CategoryTheory.Limits.HasBinaryBiproducts C := inferInstance
  let : MonoidalCategory C := SheafOfModules.monoidalCategory (X.sheaf.over U)
  let : SymmetricCategory C := SheafOfModules.symmetricCategory (X.sheaf.over U)
  have : MonoidalPreadditive C :=
    Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1
  let T := curriedTensor C
  let symmetry (K L : CochainComplex C ℤ) :
      CochainComplex.mapBifunctor K L T ≅ CochainComplex.mapBifunctor L K T := by
    let e : (((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L) ≅
        (((T.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L) :=
      HomologicalComplex.Hom.isoOfComponents
        (fun p ↦ HomologicalComplex.Hom.isoOfComponents
          (fun q ↦ β_ (K.X p) (L.X q)) (by
            intro q q' hq
            exact (BraidedCategory.braiding_naturality_right (K.X p) (L.d q q')).symm))
        (by
          intro p p' hp
          ext q : 1
          exact (BraidedCategory.braiding_naturality_left (K.d p p') (L.X q)).symm)
    exact HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso L K T (.up ℤ)
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  let F := T.map₂CochainComplex.flip.obj N ⋙ DerivedCategory.Q (C := C)
  let G := T.map₂CochainComplex.obj A ⋙ DerivedCategory.Q (C := C)
  have hF : W.IsInvertedBy F := by
    intro K L f hf
    have : QuasiIso f := hf
    have ht := hN (CochainComplex.mappingCone f)
      ((CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf)
    have : QuasiIso ((T.map₂CochainComplex.flip.obj N).map f) := by
      apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
      intro i
      exact (ht i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso f N T)
    change IsIso (DerivedCategory.Q.map ((T.map₂CochainComplex.flip.obj N).map f))
    infer_instance
  have hG : W.IsInvertedBy G := by
    intro K L f hf
    have : QuasiIso f := hf
    have ht := hA (CochainComplex.mappingCone f)
      ((CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf)
    have ht' : (CochainComplex.mapBifunctor A (CochainComplex.mappingCone f) T).Acyclic :=
      HomologicalComplex.Acyclic.of_iso ht (symmetry (CochainComplex.mappingCone f) A)
    have : QuasiIso ((T.map₂CochainComplex.obj A).map f) := by
      apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
      intro i
      exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso A f T)
    change IsIso (DerivedCategory.Q.map ((T.map₂CochainComplex.obj A).map f))
    infer_instance
  let DF := Localization.lift F hF DerivedCategory.Q
  let DG := Localization.lift G hG DerivedCategory.Q
  let cF := Localization.fac F hF DerivedCategory.Q
  let cG := Localization.fac G hG DerivedCategory.Q
  exact ⟨(cF.app P).symm ≪≫ DF.mapIso eA ≪≫ cF.app A ≪≫
    (cG.app N).symm ≪≫ DG.mapIso eB ≪≫ cG.app B⟩

set_option linter.unusedVariables false in
-- The unchanged interface assumes B strictly perfect; K-flatness of A already suffices.
-- Localized-site tensor comparisons require additional elaboration steps.
/-- On a fixed open, prescribed strictly perfect models compute the restriction of the
ordinary tensor of global K-flat representatives. No perfectness hypothesis or choice of
neighbourhood is involved.
Source: Stacks Project, Cohomology of Sheaves, Lemma 09J5, local reduction and K-flat
computation; Tag 06YH, independence of K-flat representatives; Tag 08DX, open restriction.
(blueprint: lem-sc-strict-perfect-tensor-local-comparison).

Proof: Let R be exact restriction to the localized site over U. The comparison between
termwise and derived restriction identifies R(Q(P)) with Q(R(P)), and similarly for N.
Restriction preserves K-flatness, since it is restriction to an open. Restriction also
commutes with sheaf tensor and arbitrary direct sums, so Q(R(Tot(P tensor N))) identifies
with Q(Tot(R(P) tensor R(N))). Each term of A and B is a retract of a finite free sheaf,
hence flat; their upper degree bounds make them K-flat. The K-flat derived tensor
comparison identifies the latter object with Q(R(P)) tensor-derived Q(R(N)). Tensor the
two prescribed derived-category isomorphisms, obtaining Q(A) tensor-derived Q(B).
The same K-flat comparison for A and B identifies this with Q(Tot(A tensor B)). Compose
these isomorphisms. All constructions are on the localized site; no quasi-coherence or
affineness assumption is needed. On the empty open every category object is zero, and
rank-zero free summands and zero complexes obey the same comparison. -/
theorem strictPerfect_tensor_localComparison (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (hN : CochainComplex.IsKFlatTensor (R := X.sheaf) N)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hA : Scheme.IsStrictlyPerfect X U A) (hB : Scheme.IsStrictlyPerfect X U B)
    (eA : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj (DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj A))
    (eB : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj (DerivedCategory.Q.obj N) ≅
        DerivedCategory.Q.obj B)) :
    Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N
          (@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)))) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor A B
        (@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))))) := by
  classical
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let P' := (R.mapHomologicalComplex (.up ℤ)).obj P
  let N' := (R.mapHomologicalComplex (.up ℤ)).obj N
  obtain ⟨_hP', hN', ⟨e⟩⟩ := localizedOpen_kFlat_tensor_restriction X U P N hP hN
  obtain ⟨e'⟩ := local_kFlat_tensor_invariance X U P' N' A B hN'
    (strictPerfect_isKFlat_local X U A hA)
    ((R.mapDerivedCategoryFactors.app P).symm ≪≫ eA.some)
    ((R.mapDerivedCategoryFactors.app N).symm ≪≫ eB.some)
  exact ⟨e ≪≫ e'⟩

end AlgebraicGeometry
