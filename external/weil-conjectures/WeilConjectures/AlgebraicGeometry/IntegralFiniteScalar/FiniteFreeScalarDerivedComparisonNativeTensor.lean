/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions

/-! Native derived tensor consequence for the finite-free scalar model.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

set_option linter.unusedVariables false in
/-- K-flatness gives the native derived tensor comparison isomorphism.

Resolve the two factors by the K-flat complex;
the normalized total-tensor comparison is an isomorphism and localization preserves
it, yielding the displayed `DerivedCategory.Q` multiplication map.
-/
theorem finiteFreeScalarDerivedComparison_nativeTensor
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hS : S.ShortExact) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (Z : Scheme.{u})
    (hK : CochainComplex.IsKFlatIndependentCoefficients
      (((ModuleRingedComparison.equivalence Λ.X Z).functor.mapHomologicalComplex
        (.up ℤ)).obj (complex Λ S Z))) :
    ∀ C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ,
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Z) C) := by
  have h := InternalAbelianSheafModule.internal_section_tensor_comparison
    (Scheme.ProEt.topology Z) (condensedRingObj Λ.X Z)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hk⟩ := h.2
  have htest := (hk (complex Λ S Z)).mpr hK
  have hflat :
      (HomotopyCategory.quasiIso (ModuleRingedComparison.internalModules Λ.X Z)
        (.up ℤ)).kFlat ((HomotopyCategory.quotient _ _).obj (complex Λ S Z)) := by
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro A hA
    obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hA
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor A (complex Λ S Z) (curriedTensor _))).2 (htest A hA)
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩
  intro C
  have (M : ModuleRingedComparison.internalModules Λ.X Z) :
      PreservesColimitsOfShape ℤ
        ((curriedTensor (ModuleRingedComparison.internalModules Λ.X Z)).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have := isLeftDerivabilityStructure_localizerMorphismKFlat Λ.X Z
  have hm : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ _).obj (complex Λ S Z))
      ((HomotopyCategory.quotient _ _).obj C)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ hflat
  change IsIso ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
    DerivedCategory.Qh.map _) ≫ _)
  infer_instance

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
