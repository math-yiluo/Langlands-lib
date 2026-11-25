/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import all Mathlib.Algebra.Module.FinitePresentation
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.ConstantToContinuousScalarFlat
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Finite presentations of scalar-complex cohomology
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
open FiniteConstantModel ContinuousScalarPresentation

private theorem continuousScalar_exact
    (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    PreservesFiniteLimits (continuousScalarFunctor A) := by
  have : PreservesFiniteLimits (scalarModules A) := scalarModules_preservesFiniteLimits A
  have : PreservesFiniteLimits
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
    unfold constantSheaf
    infer_instance
  have : PreservesFiniteLimits (Mod.extendScalars (scalarToContinuous A)) := by
    apply constantToContinuous_preservesFiniteLimits A
    intro S a
    simp only [scalarToContinuous, Equiv.apply_symm_apply]
    rfl
  unfold continuousScalarFunctor
  infer_instance

private theorem continuous_kernel_free
    (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    {M N : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (Profinite.continuousCoefficientRingObj A)}
    (f : M ⟶ N) (hM : Mod.IsFree _ M) (hN : Mod.IsFree _ N) :
    Mod.IsFree (Profinite.continuousCoefficientRingObj A) (kernel f) := by
  classical
  obtain ⟨m, ⟨em⟩⟩ := hM
  obtain ⟨n, ⟨en⟩⟩ := hN
  let f' := em.inv ≫ f ≫ en.hom
  obtain ⟨g, hg⟩ := continuous_free_map_surjective A m n f'
  let F := continuousScalarFunctor.{u} A
  have : PreservesFiniteLimits F := continuousScalar_exact A
  have : PreservesFiniteColimits F := continuous_colimits A
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  let e₁ : kernel (F.map g) ≅ kernel f' :=
    kernel.mapIso (F.map g) f' (continuousFreeIso A m) (continuousFreeIso A n) (by
      rw [← hg]
      simp only [Iso.hom_inv_id_assoc]
      rfl)
  let e : kernel (F.map g) ≅ kernel f := e₁ ≪≫
    kernel.mapIso f' f em.symm en.symm (by
      simp only [f', Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  have : Module.Finite A (freeScalars A m) := by
    have : Module.Finite A (ULift.{u + 1} A) :=
      Module.Finite.equiv (ULift.moduleEquiv : ULift.{u + 1} A ≃ₗ[A] A).symm
    exact inferInstanceAs (Module.Finite A (Fin m → ULift.{u + 1} A))
  have : Module.Free A (freeScalars A m) := by
    have : Module.Free A (ULift.{u + 1} A) :=
      Module.Free.of_equiv (ULift.moduleEquiv : ULift.{u + 1} A ≃ₗ[A] A).symm
    exact inferInstanceAs (Module.Free A (Fin m → ULift.{u + 1} A))
  let ek := ModuleCat.kernelIsoKer g
  have : Module.Finite A (kernel g : ModuleCat.{u + 1} A) :=
    Module.Finite.equiv ek.toLinearEquiv.symm
  have : Module.Free A (kernel g : ModuleCat.{u + 1} A) :=
    Module.Free.of_equiv ek.toLinearEquiv.symm
  let B := Module.Free.chooseBasis A (kernel g : ModuleCat.{u + 1} A)
  let d := Fintype.card (Module.Free.ChooseBasisIndex A (kernel g : ModuleCat.{u + 1} A))
  let B' := B.reindex (Fintype.equivFin _)
  let ed : (kernel g : ModuleCat.{u + 1} A) ≅ freeScalars A d :=
    (B'.equivFun.trans (LinearEquiv.piCongrRight fun _ ↦
      (ULift.moduleEquiv : ULift.{u + 1} A ≃ₗ[A] A).symm)).toModuleIso
  exact ⟨d, ⟨e.symm ≪≫ (PreservesKernel.iso F g).symm ≪≫
    F.mapIso ed ≪≫ continuousFreeIso A d⟩⟩

/-- A complex of finite free continuous modules over a scalar PID has finitely
presented cohomology. This includes torsion cohomology and rank-zero terms. -/
theorem integral_scalar_complex_homology
    (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (P : CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousCoefficientRingObj A)) ℤ)
    (hf : ∀ q, Mod.IsFree (Profinite.continuousCoefficientRingObj A) (P.X q)) (q : ℤ) :
    Mod.IsFinitelyPresented (Profinite.continuousCoefficientRingObj A) (P.homology q) := by
  let S := P.sc q
  have hk : Mod.IsFree (Profinite.continuousCoefficientRingObj A) (kernel S.g) :=
    continuous_kernel_free A S.g (hf _) (hf _)
  obtain ⟨m, ⟨em⟩⟩ := hf ((ComplexShape.up ℤ).prev q)
  obtain ⟨n, ⟨en⟩⟩ := hk
  let g := kernel.lift S.g S.f S.zero
  exact ⟨n, m, em.inv ≫ g ≫ en.hom,
    ⟨S.homologyIsoCokernelLift ≪≫
      cokernel.mapIso g _ em en (by simp only [Iso.hom_inv_id_assoc])⟩⟩

end AlgebraicGeometry.ProEtale
