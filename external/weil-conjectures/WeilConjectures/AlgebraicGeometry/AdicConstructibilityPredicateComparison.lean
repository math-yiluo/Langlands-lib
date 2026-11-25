/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import WeilConjectures.Algebra.Homology.RingedSiteBoundedDualComponents
import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwists
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoConstructible
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
import all WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.NormalizedDVRKFlatTransition
import WeilConjectures.AlgebraicGeometry.PrincipalConeKoszulRoosComparison
import WeilConjectures.AlgebraicGeometry.PrincipalIdealLocalTestCriterion
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
import WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.CategoryTheory.SiteAlgebraicCompositionUnit
import WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact
import WeilConjectures.CategoryTheory.UnitPowerCompleteness
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.NumberTheory.Padics.IntegersFinite
import WeilConjectures.Topology.ProfiniteCondensedRing

set_option linter.privateModule false

/-!
# Adic constructibility predicates on Noetherian schemes

proof.md`, integral and rational cases, and
sec-proetale-coefficients/sk-def-sfb-constructible, clauses 1--2 and final paragraph
(auxiliary; not a blueprint node).

The comparison uses the specified condensed multiplication and the existing internal
module predicates. Under the section-action equivalence these are the same module sheaves.
Both bounded predicates live in the ordinary derived category; no completion is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem comparison_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ')
    (X : Scheme.{u})
    (h : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X),
      IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
        IsConstantModelConstructible Λ X M)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)) :
    IsConstructibleModuleObject (condensedRingObj Λ' X) M ↔
      IsConstantModelConstructible Λ' X M := by
  let φ := e.hom.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.hom.hom)
  let ψ := (upperStarFromPoint X).map φ
  let N := (Mod.comap ψ).obj M
  have er : (Mod.comap (inv ψ)).obj N ≅ M :=
    ((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
      Mod.comapId _).app M
  constructor
  · intro hM
    have hN := (h N).mp (_root_.constructible_comap ψ hM)
    have hback := constructible_comap (inv φ) X N hN
    apply constructible_iso _ hback
    exact ((Mod.comapComp ((upperStarFromPoint X).map (inv φ)) ψ).symm ≪≫
      Mod.comapCongr (by
        dsimp only [ψ]
        rw [← Functor.map_comp]
        simp) ≪≫ Mod.comapId _).app M
  · intro hM
    exact _root_.constructible_of_iso er
      (_root_.constructible_comap (inv ψ) ((h N).mpr (constructible_comap φ X M hM)))

private theorem integralCoefficientIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    Nonempty (Mon.mk (integralCondensedRing ℓ (ULift.{u} E)) ≅
      Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E := ⟨fun c x ↦ by
    change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
      ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
      PadicAlgCl.norm_extends]⟩
  let F := ULift.{u} E
  let : NormedField F :=
    { (inferInstance : Field F), (inferInstance : NormedCommRing F) with
      dist_eq x y := dist_eq_norm_neg_add x.down y.down
      norm_mul x y := norm_mul x.down y.down }
  let : NormedAlgebra ℚ_[ℓ] F := ⟨fun a x ↦ by
    change ‖a • x.down‖ ≤ ‖a‖ * ‖x.down‖
    exact norm_smul_le a x.down⟩
  let : FiniteDimensional ℚ_[ℓ] F :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
  let A := latticeCoefficientIntegers ℓ F
  let e : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F) ≃+* E :=
    (WithAbs.equiv _).trans ULift.ringEquiv
  have he (x : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F)) : ‖e x‖ = ‖x‖ := by
    change ‖(WithAbs.equiv _ x).down‖ = spectralNorm ℚ_[ℓ] F (WithAbs.equiv _ x)
    exact NormedAlgebra.norm_eq_spectralNorm ℚ_[ℓ] (L := F) (WithAbs.equiv _ x)
  have hmem (x : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F)) :
      x ∈ A ↔ e x ∈ PadicAlgCl.integers ℓ E := by
    change WithAbs.equiv _ x ∈ Padic.coefficientExtensionIntegers ℓ F ↔ _
    rw [Padic.mem_coefficientExtensionIntegers, PadicAlgCl.mem_integers_iff]
    change ‖x‖ ≤ 1 ↔ ‖e x‖₊ ≤ 1
    rw [← he, ← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm]
  let ei : A ≃+* PadicAlgCl.integers ℓ E :=
    { toFun := fun x ↦ ⟨e x, (hmem x).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x,
        (hmem _).mpr (by simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x y)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x y) }
  have hei : Isometry ei := by
    apply AddMonoidHomClass.isometry_of_norm ei
    intro x
    exact he x
  have heis : Isometry ei.symm := by
    intro x y
    simpa only [ei.apply_symm_apply] using (hei (ei.symm x) (ei.symm y)).symm
  let eR : Profinite.continuousMapRingSheafOfUniverse.{u,u} A ≅
      Profinite.padicIntegersCondensedRing.{u} ℓ E :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hei.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop
              heis.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  refine ⟨{ hom := Mon.ofHom eAb.hom
            inv := Mon.ofHom eAb.inv
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · apply Mon.Hom.ext
    exact eAb.hom_inv_id
  · apply Mon.Hom.ext
    exact eAb.inv_hom_id

end AlgebraicGeometry.ProEtale
