/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Internal.InternalPerfectReductionHomData
public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryReductions
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import WeilConjectures.AlgebraicGeometry.FiniteScalarCompletion.FiniteScalarLocalModelComplete
import WeilConjectures.AlgebraicGeometry.Derived.DerivedNakayamaFirstReduction
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteFreeApproximationHomology
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Completeness of the scalar model of a bounded finite free complex

For a bounded complex `P` of finite free `𝒪_E`-modules, the complex `𝒪_{E,W} ⊗_{𝒪_E} P`
is derived complete.

## Implementation details

Every term is isomorphic to a finite free module, whose completeness is
`finite_scalar_local_model_complete`. Complete objects are closed under isomorphisms,
shifts and cones (`derived_nakayama_first_reduction`), so the stupid filtration
(`CochainComplex.bounded_mem_of_single_terms`) shows the whole complex is complete.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Derived completeness is invariant under isomorphism. -/
theorem IsDerivedComplete.of_iso {W : Scheme.{u}}
    {K L : DerivedCategory (AdicCompletion.Modules l E W)} (e : K ≅ L)
    (hK : IsDerivedComplete l E W K) : IsDerivedComplete l E W L := by
  obtain ⟨P, hP, ⟨eP⟩, h⟩ := hK
  exact ⟨P, hP, ⟨eP ≪≫ e⟩, h⟩

/-- The scalar model `𝒪_{E,W} ⊗_{𝒪_E} P` of a bounded complex `P` of finite free
`𝒪_E`-modules is derived complete. -/
theorem isDerivedComplete_internalPerfectScalarModel (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) :
    IsDerivedComplete l E W (internalPerfectScalarModel l E W P) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionIntegers l E
  let C := AdicCompletion.Modules l E W
  obtain ⟨-, hcone, hshift, -⟩ := derived_nakayama_first_reduction l E W
  let S : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
    fun X ↦ IsDerivedComplete l E W (DerivedCategory.Qh.obj X)
  have hfree₀ : IsDerivedComplete l E W
      (DerivedCategory.Q.obj (FiniteScalarCompletion.freeComplex l E W 1)) :=
    ((FiniteScalarCompletion.finite_scalar_local_model_complete l E W).2.2 1).1
  have hzero : ∀ Z : DerivedCategory C, IsZero Z → IsDerivedComplete l E W Z := by
    intro Z hZ
    let K := DerivedCategory.Q.obj (FiniteScalarCompletion.freeComplex l E W 1)
    have h := hcone _ (contractible_distinguished K) hfree₀ hfree₀
    exact IsDerivedComplete.of_iso l E (Limits.isZero_zero _ |>.iso hZ) h
  have : S.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ IsDerivedComplete.of_iso l E (DerivedCategory.Qh.mapIso e) h⟩
  have : S.ContainsZero :=
    ⟨⟨0, Limits.isZero_zero _, hzero _ (DerivedCategory.Qh.map_isZero (Limits.isZero_zero _))⟩⟩
  have : S.IsTriangulatedClosed₂ := ⟨fun T hT h₁ h₃ ↦ by
    apply ObjectProperty.le_isoClosure
    have hT' := DerivedCategory.Qh.map_distinguished T hT
    exact hcone _ (inv_rot_of_distTriang _ hT') (hshift _ h₃ (-1)) h₁⟩
  have hsingle : ∀ (n : ℤ) (M : C) (r : ℕ), Nonempty (M ≅ Mod.finiteFree
      (AdicCompletion.ring l E W) r) →
      S ((HomotopyCategory.singleFunctor C n).obj M) := by
    rintro n M r ⟨e⟩
    have h₀ : IsDerivedComplete l E W ((DerivedCategory.singleFunctor C 0).obj M) :=
      IsDerivedComplete.of_iso l E ((DerivedCategory.singleFunctor C 0).mapIso e.symm)
        ((FiniteScalarCompletion.finite_scalar_local_model_complete l E W).2.2 r).1
    have h₁ := hshift _ h₀ (-n)
    refine IsDerivedComplete.of_iso l E ?_ h₁
    exact ((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by omega)).app M ≪≫
      (DerivedCategory.singleFunctorIsoCompQh C n).app M
  let K := internalPerfectIntegralComplex l E W P
  have : K.IsStrictlyGE a := by
    unfold K internalPerfectIntegralComplex
    infer_instance
  have : K.IsStrictlyLE b := by
    unfold K internalPerfectIntegralComplex
    infer_instance
  have hK : S ((HomotopyCategory.quotient C _).obj K) := by
    refine CochainComplex.bounded_mem_of_single_terms S K a b (fun i _ _ ↦ ?_)
    let : Module.Finite A (P.X i) := (hfree i).1
    let : Module.Free A (P.X i) := (hfree i).2
    let M := (ModuleCat.uliftFunctor.{u + 1, u} A).obj (P.X i)
    have : Module.Free A M := by
      change Module.Free A (ULift.{u + 1} (P.X i))
      infer_instance
    have : Module.Finite A M := by
      change Module.Finite A (ULift.{u + 1} (P.X i))
      infer_instance
    let r := Module.finrank A M
    let e : M ≅ FiniteConstantModel.freeScalars A r :=
      ((Module.finBasis A M).equivFun.trans
        (LinearEquiv.piCongrRight (fun _ : Fin r ↦ ULift.moduleEquiv.symm))).toModuleIso
    obtain ⟨c⟩ := FiniteConstantModel.modelFiniteFree A W r
    exact hsingle i _ r ⟨(FiniteConstantModel.modelFunctor A W).mapIso e ≪≫ c⟩
  exact IsDerivedComplete.of_iso l E ((DerivedCategory.quotientCompQhIso C).app K) hK

end AlgebraicGeometry.ProEtale
