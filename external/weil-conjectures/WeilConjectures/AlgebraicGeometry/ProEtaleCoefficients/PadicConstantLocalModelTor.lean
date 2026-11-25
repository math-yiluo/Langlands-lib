/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.AlgebraicGeometry.PadicConstantLocalModelTor

import all WeilConjectures.AlgebraicGeometry.LocalModelTorBoundDescent
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Tor intervals for finite constant p-adic scalar models -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj ZeroObject TensorProduct
open Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] constantScalarSheaf_laxBraided

attribute [local irreducible] CondensedRing.upperStar Functor.mapDerivedCategory
  Functor.mapDerivedCategoryHomologyFunctorIso Functor.mapDerivedCategorySingleFunctor
  _root_.DerivedCategory.instMonoidalCategory

private theorem tor_of_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (K : _root_.DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (a b : ℤ)
    (hK : ∀ i, _root_.DerivedCategory.torAmplitudeIn _ a b
      ((CondensedRing.upperStar Λ (U.f i)).mapDerivedCategory.obj K)) :
    _root_.DerivedCategory.torAmplitudeIn _ a b K := by
  intro M
  let T := K ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj M
  have hz (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj T) := by
    apply coverHomologyZero (Mon.mk Λ) X U T q
    intro i
    let F := CondensedRing.upperStar Λ (U.f i)
    let e := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (U.f i)
    let t := ((CondensedRing.leftDerivedUpperStarTensorIso Λ (U.f i)).app K).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj M)
    let d := transportTensorIso F.mapDerivedCategory _ e K
      ((_root_.DerivedCategory.singleFunctor _ 0).obj M)
      (F.mapDerivedCategory.obj K) ((_root_.DerivedCategory.singleFunctor _ 0).obj (F.obj M))
      (Iso.refl _) ((F.mapDerivedCategorySingleFunctor 0).app M) t
    have ht := (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      d.symm (hK i (F.obj M))
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff _ a).mp ht.1 q hq
    · exact (_root_.DerivedCategory.isLE_iff _ b).mp ht.2 q hq
  exact ⟨(_root_.DerivedCategory.isGE_iff T a).mpr (fun q hq ↦ hz q (Or.inl hq)),
    (_root_.DerivedCategory.isLE_iff T b).mpr (fun q hq ↦ hz q (Or.inr hq))⟩

private noncomputable def ringFreeCoordinates
    {K : Type (u + 1)} [CommRing K]
    {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
    (R : D) (F : D ⥤ ModuleCat.{u + 1} K) [F.Additive]
    (e : F.obj R ≃ₗ[K] K) (n : ℕ) :
    F.obj (⨁ fun _ : Fin n ↦ R) ≃ₗ[K] (Fin n → K) :=
  ((F.mapBiproduct (fun _ : Fin n ↦ R)).toLinearEquiv.trans
    (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ F.obj R)).toLinearEquiv).trans
      (LinearEquiv.piCongrRight fun _ ↦ e)

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_field_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (K : Type (u + 1)) [Field K]
    (φ : AddCommGrpCat.of K ⟶ scalarRingObj Λ) [IsMonHom φ] [IsIso φ]
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Λ) P) :
    Mod.IsFree (scalarRingObj Λ) P := by
  classical
  let R := scalarRingObj Λ
  let Q := Mod.comap φ ⋙ internalToModule K
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : Q.IsEquivalence := by dsimp only [Q]; infer_instance
  have : Q.Additive := by
    have : (internalToModule K).Additive := ⟨by intros; rfl⟩
    dsimp only [Q]
    infer_instance
  let r : (Mod.comap φ).obj (Mod.regular R) ≅ Mod.regular (AddCommGrpCat.of K) :=
    (Mod.comapCongr (by simp : inv (inv φ) = φ)).symm.app _ ≪≫
      Mod.regularIsoOfIsIso (inv φ)
  let b : Q.obj (Mod.regular R) ≃ₗ[K] K :=
    ((internalToModule K).mapIso r).toLinearEquiv.trans (internalRegularCoordinates K)
  let e (n : ℕ) := ringFreeCoordinates (Mod.regular R) Q b n
  obtain ⟨n, m, f, ⟨i⟩⟩ := hP
  let iQ : Q.obj P ≅ cokernel (Q.map f) := Q.mapIso i ≪≫ PreservesCokernel.iso Q f
  have : Module.Finite K (Q.obj (Mod.finiteFree R n)) :=
    Module.Finite.of_injective (e n).toLinearMap (e n).injective
  have : Module.Finite K (cokernel (Q.map f) : ModuleCat K) :=
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient (Q.map f)).toLinearEquiv.symm
  have : Module.Finite K (Q.obj P) := Module.Finite.equiv iQ.toLinearEquiv.symm
  let B := Module.finBasis K (Q.obj P)
  exact ⟨Module.finrank K (Q.obj P), ⟨Q.preimageIso
    ((B.equivFun.trans (e _).symm).toModuleIso)⟩⟩

private theorem tor_of_scalar_field
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (K : Type (u + 1)) [Field K]
    (φ : AddCommGrpCat.of K ⟶ scalarRingObj Λ) [IsMonHom φ] [IsIso φ]
    (X : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hN : HasFiniteConstantLocalModel Λ X N) :
    _root_.DerivedCategory.torAmplitudeIn _ 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj N) := by
  obtain ⟨U, hU⟩ := (finiteConstantLocalModel_iff_exists_cover Λ N).mp hN
  apply tor_of_cover Λ X U
  intro i
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  obtain ⟨n, ⟨en⟩⟩ := scalar_field_free Λ K φ P hP
  let e := eP ≪≫ (finiteConstantScalarExtension Λ (U.X i)).mapIso en ≪≫
    scalarFreeIso Λ (U.X i) n
  let d := ((CondensedRing.upperStar Λ (U.f i)).mapDerivedCategorySingleFunctor 0).app N
  apply (_root_.DerivedCategory.torAmplitudeIn _ 0 0).prop_of_iso
    (d ≪≫ (_root_.DerivedCategory.singleFunctor _ 0).mapIso e).symm
  exact _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
    (CategoryTheory.isDualizable_biproduct_unit
      (C := Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
        (condensedRingObj Λ (U.X i))) n).flat

private noncomputable def continuousScalarEquiv
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    ULift.{u + 1} A ≃+* ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, A) where
  toFun a := ULift.up (ContinuousMap.const _ a.down)
  invFun f := ULift.up (f.down PUnit.unit)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    ext x
    exact congrArg f.down (Subsingleton.elim PUnit.unit x)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private noncomputable def continuousScalarHom
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    AddCommGrpCat.of (ULift.{u + 1} A) ⟶
      scalarRingObj (Profinite.continuousMapRingObj A) :=
  (continuousScalarEquiv A).toAddEquiv.toAddCommGrpIso.hom

private instance continuousScalarHom_iso
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsIso (continuousScalarHom.{u} A) := by
  unfold continuousScalarHom
  infer_instance

private instance continuousScalarHom_mon
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsMonHom (continuousScalarHom.{u} A) := by
  have hm : (scalarSections.{u}).monObjObj (Profinite.continuousMapRingObj A) =
      AddCommGrpCat.ringMonObj
        (ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, A)) := by
    rw [scalarSections_monoidal_eq]
    apply MonObj.ext
    let R := Profinite.continuousMapRingSheaf.{u} A
    let : MonObj (Profinite.continuousMapRingObj.{u} A).obj := R.obj.monObjCompForget₂
    exact congr_app (Sheaf.μ_comp_map_mul (Profinite.continuousMapRingObj A))
      (Opposite.op (Profinite.of PUnit.{u + 1}))
  change @IsMonHom _ _ _ _ _ _ ((scalarSections.{u}).monObjObj _) _
  rw [hm]
  exact AddCommGrpCat.isMonHom_ofHom_ringHom (continuousScalarEquiv A).toRingHom

private theorem tor_of_continuous_field
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (A : Type) [Field A] [TopologicalSpace A] [IsTopologicalRing A]
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))
    (X : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hN : HasFiniteConstantLocalModel Λ X N) :
    _root_.DerivedCategory.torAmplitudeIn _ 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj N) := by
  let j := scalarSections.mapMon.mapIso e
  exact tor_of_scalar_field Λ (ULift.{u + 1} A)
    (continuousScalarHom A ≫ j.inv.hom) X N hN

private noncomputable def qbarPointEval (ℓ : ℕ) [Fact ℓ.Prime] :
    PadicAlgCl.finiteIntermediateFieldValued ℓ (Profinite.of PUnit.{u + 1}) →+*
      PadicAlgCl ℓ where
  toFun f := f.1 PUnit.unit
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem qbarPointEval_bijective (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Bijective (qbarPointEval.{u} ℓ) := by
  constructor
  · intro a b h
    apply Subtype.ext
    ext x
    exact (congrArg a.1 (Subsingleton.elim x PUnit.unit)).trans
      (h.trans (congrArg b.1 (Subsingleton.elim PUnit.unit x)))
  · intro a
    have ha : _root_.IsIntegral ℚ_[ℓ] a := Algebra.IsIntegral.isIntegral a
    refine ⟨⟨ContinuousMap.const _ a,
      ⟨IntermediateField.adjoin ℚ_[ℓ] {a}, IntermediateField.adjoin.finiteDimensional ha,
        fun _ ↦ IntermediateField.subset_adjoin ℚ_[ℓ] _ (Set.mem_singleton a)⟩⟩, rfl⟩

private noncomputable def qbarScalarEquiv (ℓ : ℕ) [Fact ℓ.Prime] :
    ULift.{u + 1} (PadicAlgCl ℓ) ≃+*
      ULift.{u + 1}
        (PadicAlgCl.finiteIntermediateFieldValued ℓ (Profinite.of PUnit.{u + 1})) :=
  ULift.ringEquiv.trans
    ((RingEquiv.ofBijective (qbarPointEval ℓ) (qbarPointEval_bijective ℓ)).symm.trans
      ULift.ringEquiv.symm)

private noncomputable def qbarScalarHom (ℓ : ℕ) [Fact ℓ.Prime] :
    AddCommGrpCat.of (ULift.{u + 1} (PadicAlgCl ℓ)) ⟶
      scalarRingObj (Profinite.padicAlgClRingObj ℓ) :=
  (qbarScalarEquiv ℓ).toAddEquiv.toAddCommGrpIso.hom

private instance qbarScalarHom_iso (ℓ : ℕ) [Fact ℓ.Prime] :
    IsIso (qbarScalarHom.{u} ℓ) := by
  unfold qbarScalarHom
  infer_instance

private instance qbarScalarHom_mon (ℓ : ℕ) [Fact ℓ.Prime] :
    IsMonHom (qbarScalarHom.{u} ℓ) := by
  have hm : (scalarSections.{u}).monObjObj (Profinite.padicAlgClRingObj ℓ) =
      AddCommGrpCat.ringMonObj (ULift.{u + 1}
        (PadicAlgCl.finiteIntermediateFieldValued ℓ (Profinite.of PUnit.{u + 1}))) := by
    rw [scalarSections_monoidal_eq]
    apply MonObj.ext
    let R := Profinite.padicAlgClCondensedRing.{u} ℓ
    let : MonObj (Profinite.padicAlgClRingObj.{u} ℓ).obj := R.obj.monObjCompForget₂
    exact congr_app (Sheaf.μ_comp_map_mul (Profinite.padicAlgClRingObj ℓ))
      (Opposite.op (Profinite.of PUnit.{u + 1}))
  change @IsMonHom _ _ _ _ _ _ ((scalarSections.{u}).monObjObj _) _
  rw [hm]
  exact AddCommGrpCat.isMonHom_ofHom_ringHom (qbarScalarEquiv ℓ).toRingHom

private noncomputable abbrev scalarCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (scalarRingObj Λ) ⟶ Λ :=
  (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit).counit.app Λ

private instance scalarCounit_mon
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
    IsMonHom (scalarCounit Λ) := by
  let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let G := scalarSections.{u}
  let adj : C ⊣ G := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  exact adj.isMonHom_counitAlgHom Λ

private instance counitSource_comm
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
    IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (scalarRingObj Λ)) := Functor.isCommMonObj_obj

attribute [local irreducible] Mod.extendScalars Mod.extendScalarsComp
  Mod.extendScalarsIsoOfEq Mod.extendScalarsIsoComapInv
  Mod.extendRestrictAdjunction Mod.regularExtensionIso
  scalarCoefficientHom finiteConstantScalarExtension

private noncomputable def pointExtensionMapIso
    (X : Scheme.{u})
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    (upperStarFromPoint X).mapMod R ⋙
        Mod.extendScalars ((upperStarFromPoint X).map f) ≅
      Mod.extendScalars f ⋙ (upperStarFromPoint X).mapMod S := by
  let F := upperStarFromPoint X
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  exact Adjunction.pullIsoOfComapIso
    (Mod.extendRestrictAdjunction (F.map f)) (Mod.extendRestrictAdjunction f)
    (adj.mapModAdjunction R) (adj.mapModAdjunction S)
    (Mod.comapMapModComapIso _ (F.map f) f
      (adj.unitAlgHom R) (adj.unitAlgHom S) (adj.unit.naturality f))

private noncomputable def compositionExtensionIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [HasCoequalizers E] [HasEqualizers E] [BraidedCategory E] [MonoidalClosed E]
    [∀ Z : E, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : E, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (τ : F ⋙ G ≅ H) [NatTrans.IsMonoidal τ.hom]
    (R : C) [MonObj R]
    [IsCommMonObj (G.obj (F.obj R))] [IsCommMonObj (H.obj R)]
    (S : E) [MonObj S]
    (f : G.obj (F.obj R) ⟶ S) [IsMonHom f]
    (φ : H.obj R ⟶ S) [IsMonHom φ]
    (he : inv (Functor.compAlgHom F G τ.hom R) ≫ f = φ) :
    H.mapMod R ⋙ Mod.extendScalars φ ≅
      (F.mapMod R ⋙ G.mapMod (F.obj R)) ⋙ Mod.extendScalars f := by
  let α := Functor.compAlgHom F G τ.hom R
  let i : Mod.comap α ≅ Mod.extendScalars (inv α) :=
    (Mod.comapCongr (IsIso.inv_inv (f := α))).symm ≪≫
      (Mod.extendScalarsIsoComapInv (inv α)).symm
  let j : Mod.comap α ⋙ Mod.extendScalars f ≅ Mod.extendScalars φ :=
    Functor.isoWhiskerRight i (Mod.extendScalars f) ≪≫
      (Mod.extendScalarsComp (inv α) f).symm ≪≫ Mod.extendScalarsIsoOfEq he
  exact Functor.isoWhiskerLeft (H.mapMod R) j.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapModCompIso F G τ.hom R).symm
      (Mod.extendScalars f)

private noncomputable def constantExtensionCompIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    finiteConstantScalarExtension Λ X ≅
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod (scalarRingObj Λ) ⋙
        Mod.extendScalars (scalarCounit Λ) ⋙ (upperStarFromPoint X).mapMod Λ := by
  let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let F := upperStarFromPoint X
  let R := scalarRingObj Λ
  let ε := scalarCounit Λ
  let τ : C ⋙ F ≅ scalarConstant X := Iso.refl _
  have hτ : NatTrans.IsMonoidal τ.hom := by
    constructor
    · simp only [τ, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
      rfl
    · intro A B
      simp only [τ, Iso.refl_hom, NatTrans.id_app, tensorHom_id,
        id_whiskerRight, Category.id_comp, Category.comp_id]
      rfl
  let α := Functor.compAlgHom C F τ.hom R
  have he : inv α ≫ F.map ε = scalarCoefficientHom Λ X := by
    apply (cancel_epi α).mp
    rw [IsIso.hom_inv_id_assoc]
    change F.map ε = 𝟙 _ ≫ scalarCoefficientHom Λ X
    rw [Category.id_comp]
    unfold scalarCoefficientHom
    rfl
  unfold finiteConstantScalarExtension
  exact compositionExtensionIso C F (scalarConstant X) τ R _
      (F.map ε) (scalarCoefficientHom Λ X) he ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (C.mapMod R) (pointExtensionMapIso X _ _ ε) ≪≫
    (Functor.associator _ _ _).symm

attribute [local irreducible] scalarConstant pointExtensionMapIso constantExtensionCompIso

private theorem scalarExtension_leftExact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (h : PreservesFiniteLimits (Mod.extendScalars
      (scalarCounit Λ))) (X : Scheme.{u}) :
    PreservesFiniteLimits (finiteConstantScalarExtension Λ X) := by
  let : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : PreservesFiniteLimits
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
    unfold constantSheaf
    infer_instance
  have : PreservesFiniteLimits (Mod.extendScalars (scalarCounit Λ)) := h
  have : PreservesFiniteLimits
      ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
        (scalarRingObj Λ)) := inferInstance
  have : PreservesFiniteLimits ((upperStarFromPoint X).mapMod Λ) := inferInstance
  exact preservesFiniteLimits_of_natIso (constantExtensionCompIso Λ X).symm

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_pid_kernel_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (K : Type (u + 1)) [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
    (φ : AddCommGrpCat.of K ⟶ scalarRingObj Λ) [IsMonHom φ] [IsIso φ]
    (n : ℕ) (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (g : Mod.finiteFree (scalarRingObj Λ) n ⟶ P) :
    Mod.IsFree (scalarRingObj Λ) (kernel g) := by
  classical
  let R := scalarRingObj Λ
  let Q := Mod.comap φ ⋙ internalToModule K
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : Q.IsEquivalence := by dsimp only [Q]; infer_instance
  have : Q.Additive := by
    have : (internalToModule K).Additive := ⟨by intros; rfl⟩
    dsimp only [Q]
    infer_instance
  let r : (Mod.comap φ).obj (Mod.regular R) ≅ Mod.regular (AddCommGrpCat.of K) :=
    (Mod.comapCongr (by simp : inv (inv φ) = φ)).symm.app _ ≪≫
      Mod.regularIsoOfIsIso (inv φ)
  let b : Q.obj (Mod.regular R) ≃ₗ[K] K :=
    ((internalToModule K).mapIso r).toLinearEquiv.trans (internalRegularCoordinates K)
  let e (m : ℕ) := ringFreeCoordinates (Mod.regular R) Q b m
  let kg : Q.obj (kernel g) ≅ ModuleCat.of K (LinearMap.ker (Q.map g).hom) :=
    PreservesKernel.iso Q g ≪≫ ModuleCat.kernelIsoKer (Q.map g)
  have : Module.Finite K (Q.obj (Mod.finiteFree R n)) :=
    Module.Finite.of_injective (e n).toLinearMap (e n).injective
  have : Module.Free K (Q.obj (Mod.finiteFree R n)) := Module.Free.of_equiv (e n).symm
  have : Module.Finite K (Q.obj (kernel g)) :=
    Module.Finite.equiv kg.toLinearEquiv.symm
  have : Module.Free K (Q.obj (kernel g)) := Module.Free.of_equiv kg.toLinearEquiv.symm
  let B := Module.Free.chooseBasis K (Q.obj (kernel g))
  let d := Fintype.card (Module.Free.ChooseBasisIndex K (Q.obj (kernel g)))
  let B' := B.reindex (Fintype.equivFin _)
  exact ⟨d, ⟨Q.preimageIso ((B'.equivFun.trans (e d).symm).toModuleIso)⟩⟩

private theorem tor_of_free_shortExact
    {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (h₁ : IsDualizable S.X₁) (h₂ : IsDualizable S.X₂) :
    _root_.DerivedCategory.torAmplitudeIn C (-1) 0
      ((_root_.DerivedCategory.singleFunctor C 0).obj S.X₃) := by
  let S' := S.map (HomologicalComplex.single C (.up ℤ) 0)
  have hS' : S'.ShortExact := hS.map_of_exact _
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  have : (CochainComplex.mappingCone S'.f).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  have : (CochainComplex.mappingCone S'.f).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  exact (_root_.DerivedCategory.torAmplitudeIn C (-1) 0).prop_of_iso
    (asIso (_root_.DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S')) ≪≫
      ((_root_.DerivedCategory.singleFunctorIsoCompQ C 0).app S.X₃).symm)
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ (-1) 0 (fun n ↦
      (_root_.DerivedCategory.isDualizable_mappingCone_single_X h₁ h₂ S'.f n).flat))

private theorem scalar_pid_model_tor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (K : Type (u + 1)) [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
    (φ : AddCommGrpCat.of K ⟶ scalarRingObj Λ) [IsMonHom φ] [IsIso φ]
    (X : Scheme.{u}) [PreservesFiniteLimits (finiteConstantScalarExtension Λ X)]
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Λ) P) :
    _root_.DerivedCategory.torAmplitudeIn _ (-1) 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((finiteConstantScalarExtension Λ X).obj P)) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hP
  let g := cokernel.π f ≫ e.inv
  have : Epi g := by dsimp only [g]; infer_instance
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hs : S.ShortExact := ⟨ShortComplex.exact_kernel g⟩
  let F := finiteConstantScalarExtension Λ X
  obtain ⟨a, ⟨ea⟩⟩ := scalar_pid_kernel_free Λ K φ n P g
  have h₁ : IsDualizable (F.obj S.X₁) :=
    (CategoryTheory.isDualizable_biproduct_unit a).of_iso
      (F.mapIso ea ≪≫ scalarFreeIso Λ X a).symm
  have h₂ : IsDualizable (F.obj S.X₂) :=
    (CategoryTheory.isDualizable_biproduct_unit n).of_iso (scalarFreeIso Λ X n).symm
  exact tor_of_free_shortExact (S.map F) (hs.map_of_exact F) h₁ h₂

-- The Type-0 coefficient version of constantToContinuous_preservesFiniteLimits.
-- Its sectionwise proof does not require the scalar carrier to have the site's universe.
set_option backward.isDefEq.respectTransparency false in
private theorem continuousScalarExtension_leftExact
    (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    [IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))]
    (φ : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ Profinite.continuousMapRingObj A)
    [IsMonHom φ]
    (hφ : ∀ (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} A),
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ _ φ).app S) a = ULift.up (ContinuousMap.const S.unop a.down)) :
    PreservesFiniteLimits (Mod.extendScalars φ) := by
  let J := coherentTopology Profinite.{u}
  let P := (Functor.const Profinite.{u}ᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{u + 1} A))
  let R := (constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} A))
  let : MonObj P := (Functor.const Profinite.{u}ᵒᵖ).monObjObj
    (AddCommGrpCat.of (ULift.{u + 1} A))
  let : MonObj R.obj := (sheafToPresheaf J Ab.{u + 1}).monObjObj R
  let η : P ⟶ R.obj := toSheafify J P
  have hη : IsMonHom η := by
    have h := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
    have he : (inferInstance : MonObj R) =
        (presheafToSheaf J Ab.{u + 1}).monObjObj P :=
      Functor.monObjObj_comp (Functor.const Profinite.{u}ᵒᵖ)
        (presheafToSheaf J Ab.{u + 1}) (AddCommGrpCat.of (ULift.{u + 1} A))
    have he' := congrArg (fun m : MonObj R ↦
      @Functor.monObjObj _ _ _ _ _ _ (sheafToPresheaf J Ab.{u + 1}) _ R m) he
    exact @IsMonHom.of_eq _ _ _ _ _ _ _ _ _ _ rfl he'.symm h
  let RR := InternalAbelianSheafModule.sectionRingSheaf J R
  let ι (S : Profinite.{u}ᵒᵖ) : A →+* RR.obj.obj S :=
    { ((η.app S).hom.comp
        (ULift.moduleEquiv.symm : A ≃ₗ[A] ULift.{u + 1} A).toAddMonoidHom) with
      map_one' := by
        have h := congr_app (IsMonHom.one_hom (f := η)) S
        change (η.app S) (ULift.up (1 : A)) = _
        have he := ConcreteCategory.congr_hom h (ULift.up (1 : ℤ))
        change (η.app S) (ULift.up ((1 : ℤ) : A)) = (1 : RR.obj.obj S) at he
        simpa using he
      map_mul' := fun a b ↦ ConcreteCategory.congr_hom
        (congr_app (IsMonHom.mul_hom (f := η)) S) (ULift.up a ⊗ₜ[ℤ] ULift.up b) }
  let N := (Mod.comap φ).obj (Mod.regular (Profinite.continuousMapRingObj A))
  let M := (InternalAbelianSheafModule.sectionModuleFunctor J R).obj N
  have hsmul (S : Profinite.{u}ᵒᵖ) (a : A) (s : M.val.obj S) :
      ι S a • s = a • (show ULift.{u + 1} C(S.unop, A) from s) := by
    have he := hφ S (ULift.up a)
    change (φ.hom.app S) ((η.app S) (ULift.up a)) = _ at he
    change ((φ.hom.app S) ((η.app S) (ULift.up a))) = _ at he
    let : MonObj (Profinite.continuousMapRingObj A).obj := inferInstanceAs
      (MonObj (Profinite.continuousMapRingPresheaf A ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}))
    have hm := Sheaf.μ_comp_map_mul (Profinite.continuousMapRingObj A)
    let F := sheafToPresheaf J Ab.{u + 1}
    change ((Functor.LaxMonoidal.μ F R (Profinite.continuousMapRingObj A) ≫
      F.map (φ ▷ (Profinite.continuousMapRingObj A) ≫ MonObj.mul)).app S).hom
        (((η.app S) (ULift.up a)) ⊗ₜ[ℤ]
          (show ULift.{u + 1} C(S.unop, A) from s)) = _
    rw [F.map_comp, ← Functor.LaxMonoidal.μ_natural_left_assoc, hm]
    change (show ULift.{u + 1} C(S.unop, A) from
      (φ.hom.app S) ((η.app S) (ULift.up a))) *
        (show ULift.{u + 1} C(S.unop, A) from s) = _
    rw [he]
    rfl
  have hflat (S : Profinite.{u}ᵒᵖ) : Module.Flat A (ULift.{u + 1} C(S.unop, A)) := by
    have : Module.IsTorsionFree A (ULift.{u + 1} C(S.unop, A)) := by
      apply Module.IsTorsionFree.of_smul_eq_zero
      intro a f h
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        have hx : a * f.down x = 0 := congrArg (fun g ↦ g.down x) h
        exact (mul_eq_zero.mp hx).resolve_left ha
    infer_instance
  have hlifts (U : Profinite.{u}) (n : ℕ) (a : Fin n → RR.obj.obj (op U)) :
      ∃ S : Sieve U, S ∈ J U ∧ ∀ V (f : V ⟶ U), S f →
        ∃ c : Fin n → A, ∀ i, ι (op V) (c i) = RR.obj.map f.op (a i) := by
    induction n with
    | zero =>
      refine ⟨⊤, J.top_mem U, ?_⟩
      intro V f hf
      exact ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
    | succ n ih =>
      obtain ⟨S, hS, hs⟩ := ih (fun i ↦ a i.succ)
      refine ⟨Presheaf.imageSieve η (a 0) ⊓ S,
        J.intersection_covering (Presheaf.imageSieve_mem J η (a 0)) hS, ?_⟩
      intro V f hf
      obtain ⟨c, hc⟩ := hs V f hf.2
      obtain ⟨c₀, hc₀⟩ := hf.1
      refine ⟨Fin.cons c₀.down c, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j ↦ hc j) i
      exact hc₀
  have hN : ObjectProperty.flat N := by
    apply (InternalAbelianSheafModule.flat_iff_sectionModule J R N).mpr
    apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
      RR M).mpr
    intro U n a s hs
    obtain ⟨S, hS, hl⟩ := hlifts U n a
    refine ⟨S, hS, ?_⟩
    intro V f hf
    obtain ⟨c, hc⟩ := hl V f hf
    let s' : Fin n → ULift.{u + 1} C(V, A) := fun i ↦ M.val.map f.op (s i)
    have he : ∑ i, c i • s' i = 0 := by
      have h := congrArg (fun z ↦ M.val.map f.op z) hs
      simp only [map_sum, M.val.map_smul, map_zero] at h
      change (∑ i, RR.obj.map f.op (a i) • M.val.restrictₛₗ f.op (s i)) = 0 at h
      simpa only [← hc, hsmul, PresheafOfModules.restrictₛₗ_apply, s'] using! h
    have := hflat (op V)
    obtain ⟨l, b, t, hst, hcb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero he
    refine ⟨l, (fun i j ↦ ι (op V) (b i j)), t, ?_, ?_⟩
    · intro i
      simpa only [hsmul] using hst i
    · intro j
      simpa only [hc, map_sum, map_mul, map_zero] using
        congrArg (ι (op V)) (hcb j)
  have ht : PreservesFiniteLimits (tensorLeft N) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits N).mp hN
  have : PreservesFiniteLimits (Mod.extendScalars φ ⋙ Mod.forget _) :=
    preservesFiniteLimits_of_natIso (Mod.extendForgetTensorIso φ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (Mod.extendScalars φ) (Mod.forget _)

private theorem extension_equivalence
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R]
    (f : R ⟶ S) [IsMonHom f] [IsIso f] :
    (Mod.extendScalars f).IsEquivalence := by
  have : (Mod.comap (asIso f).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (asIso f).inv).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv f).symm

private theorem counitExtension_leftExact
    (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    PreservesFiniteLimits (Mod.extendScalars
      (scalarCounit.{u} (Profinite.continuousMapRingObj.{u} A))) := by
  let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  let R := Profinite.continuousMapRingObj.{u} A
  let h := continuousScalarHom.{u} A
  let f := C.map h
  let ε := scalarCounit R
  have : IsCommMonObj (C.obj (AddCommGrpCat.of (ULift.{u + 1} A))) :=
    Functor.isCommMonObj_obj (F := C)
  have hf : IsMonHom f := Functor.map.instIsMonHom (F := C) _ _ h
  have hφ : ∀ (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} A),
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ _ (f ≫ ε)).app S) a = ULift.up (ContinuousMap.const S.unop a.down) := by
    let p : (Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
        R.obj :=
      { app S := AddCommGrpCat.ofHom
          { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
            map_zero' := rfl
            map_add' _ _ := rfl }
        naturality _ _ _ := rfl }
    have he : f ≫ ε =
        ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
          _ R).symm p := by
      change (adj.homEquiv _ _).symm h = _
      apply (adj.homEquiv _ _).injective
      rw [Equiv.apply_symm_apply]
      dsimp only [adj, constantSheafAdj]
      rw [Adjunction.comp_homEquiv]
      erw [Equiv.trans_apply, Equiv.apply_symm_apply]
      change h = 𝟙 _ ≫ p.app (op (Profinite.of PUnit.{u + 1}))
      rw [Category.id_comp]
      rfl
    rw [he, Equiv.apply_symm_apply]
    intros
    rfl
  have : PreservesFiniteLimits (Mod.extendScalars (f ≫ ε)) :=
    continuousScalarExtension_leftExact A (f ≫ ε) hφ
  have : (Mod.extendScalars f).IsEquivalence := extension_equivalence f
  have he : inv f ≫ (f ≫ ε) = ε := by simp
  let i : Mod.extendScalars ε ≅
      Mod.extendScalars (inv f) ⋙ Mod.extendScalars (f ≫ ε) :=
    Mod.extendScalarsIsoOfEq he.symm ≪≫ Mod.extendScalarsComp _ _
  have : (Mod.extendScalars (inv f)).IsEquivalence := extension_equivalence (inv f)
  exact preservesFiniteLimits_of_natIso i.symm

private theorem counitExtension_transport
    (Λ B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [MonObj B] [IsCommMonObj Λ] [IsCommMonObj B]
    (e : Mon.mk Λ ≅ Mon.mk B)
    (hB : PreservesFiniteLimits (Mod.extendScalars
      (scalarCounit B))) :
    PreservesFiniteLimits (Mod.extendScalars
      (scalarCounit Λ)) := by
  let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  let j := scalarSections.mapMon.mapIso e
  have : IsCommMonObj (scalarSections.mapMon.obj (Mon.mk Λ)).X := scalarRingObj_comm Λ
  have : IsCommMonObj (scalarSections.mapMon.obj (Mon.mk B)).X := scalarRingObj_comm B
  let a : C.obj (scalarRingObj Λ) ⟶ C.obj (scalarRingObj B) := C.map j.hom.hom
  let b := e.hom.hom
  let f := scalarCounit Λ
  let g := scalarCounit B
  have : IsMonHom a := Functor.map.instIsMonHom (F := C) _ _ j.hom.hom
  have : IsMonHom f := scalarCounit_mon Λ
  have : IsMonHom g := scalarCounit_mon B
  have : PreservesFiniteLimits (Mod.extendScalars g) := hB
  have : (Mod.extendScalars a).IsEquivalence := extension_equivalence a
  have : (Mod.extendScalars b).IsEquivalence := extension_equivalence b
  have sq : a ≫ g = f ≫ b := adj.counit.naturality b
  let i : Mod.extendScalars f ⋙ Mod.extendScalars b ≅
      Mod.extendScalars a ⋙ Mod.extendScalars g :=
    (Mod.extendScalarsComp f b).symm ≪≫
      Mod.extendScalarsIsoOfEq sq.symm ≪≫ Mod.extendScalarsComp a g
  have : PreservesFiniteLimits (Mod.extendScalars f ⋙ Mod.extendScalars b) :=
    preservesFiniteLimits_of_natIso i.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Mod.extendScalars b)

private theorem tor_of_continuous_pid
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))
    (X : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hN : HasFiniteConstantLocalModel Λ X N) :
    _root_.DerivedCategory.torAmplitudeIn _ (-1) 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj N) := by
  obtain ⟨U, hU⟩ := (finiteConstantLocalModel_iff_exists_cover Λ N).mp hN
  have hε := counitExtension_transport Λ _ e (counitExtension_leftExact A)
  apply tor_of_cover Λ X U
  intro i
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  have := scalarExtension_leftExact Λ hε (U.X i)
  let j := scalarSections.mapMon.mapIso e
  have : IsDomain (ULift.{u + 1} A) :=
    MulEquiv.isDomain A (ULift.ringEquiv (R := A)).toMulEquiv
  have : IsPrincipalIdealRing (ULift.{u + 1} A) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := A)).symm.toRingHom
      (ULift.ringEquiv (R := A)).symm.surjective
  let d := ((CondensedRing.upperStar Λ (U.f i)).mapDerivedCategorySingleFunctor 0).app N
  exact (_root_.DerivedCategory.torAmplitudeIn _ (-1) 0).prop_of_iso
    (d ≪≫ (_root_.DerivedCategory.singleFunctor _ 0).mapIso eP).symm
    (scalar_pid_model_tor Λ (ULift.{u + 1} A)
      (continuousScalarHom A ≫ j.inv.hom) (U.X i) P hP)

/-- Finite constant local models have a uniform scalar Tor interval, on every scheme. -/
theorem padic_constant_local_model_tor
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (c : ℤ)
    (hΛ :
      (c = -1 ∧ (Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
        ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)))) ∨
      (c = 0 ∧ (Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
        (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))))
    (S : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hN : HasFiniteConstantLocalModel Λ S N) :
    _root_.DerivedCategory.torAmplitudeIn _ c 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj N) := by
  rcases hΛ with h | h
  · rcases h with ⟨hc, h⟩
    subst c
    rcases h with h | ⟨E, h⟩
    · obtain ⟨e⟩ := h
      exact tor_of_continuous_pid Λ ℤ_[ℓ] e S N hN
    · obtain ⟨e⟩ := h
      let := PadicAlgCl.normedFieldOfAlgebra ℓ E
      let : IsTopologicalRing (PadicAlgCl.integers ℓ E) :=
        PadicAlgCl.isTopologicalRing_integers ℓ E
      exact tor_of_continuous_pid Λ (PadicAlgCl.integers ℓ E) e S N hN
  · rcases h with ⟨hc, h⟩
    subst c
    rcases h with h | h
    · obtain ⟨e⟩ := h
      exact tor_of_continuous_field Λ ℚ_[ℓ] e S N hN
    · rcases h with ⟨E, h⟩ | h
      · obtain ⟨e⟩ := h
        exact tor_of_continuous_field Λ E e S N hN
      · obtain ⟨e⟩ := h
        let j := scalarSections.mapMon.mapIso e
        exact tor_of_scalar_field Λ (ULift.{u + 1} (PadicAlgCl ℓ))
          (qbarScalarHom ℓ ≫ j.inv.hom) S N hN

end AlgebraicGeometry.ProEtale
