/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectOrdinaryMatrixData
import WeilConjectures.CategoryTheory.FunctorFiniteMatrixCoordinates
public import WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBoundTorsion
import all WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBoundTorsion
import all WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelOrdinaryScalar

/-! # Scalar normalization of the fixed rank-one coordinates
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale.InternalPerfectMatrix

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- A constant residue section is the actual image of the integral scalar section. -/
theorem coefficientSection_integral (W : Scheme.{u}) (n : ℕ) (x : A l E) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    coefficientSection l E W n (LocallyConstant.const _
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x)) =
      ((MonObj.one : 𝟙_ (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) ⟶
        AdicCompletion.ring l E W) ≫
          (upperStarFromPoint W).map (torsionIntegerMultiply l E x).asHom) ≫
        AdicCompletion.quotient l E W n := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let U : W.ProEt := Scheme.ProEt.mk (𝟙 W)
  apply Sheaf.unitHomEval_injective (Scheme.ProEt.isTerminalMkId W)
    (AdicCompletion.finiteRing l E W n)
  erw [coefficientSection_const_eval]
  exact (constant_scalar_section l E W (n + 1) x (op U)).symm

/-- Integral multiplication has the prescribed multiplication matrix after ordinary
rank-one scalar extension. This uses the fixed, normalized integral regular comparison. -/
theorem quotientRegular_scalar (W : Scheme.{u}) (n : ℕ) (x : A l E) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let F := Mod.extendScalars (AdicCompletion.quotient l E W n)
    let e := F.mapIso (integralRegular l E W) ≪≫
      Mod.regularExtensionIso (AdicCompletion.quotient l E W n)
    F.map ((FiniteConstantModel.modelFunctor (A l E) W).map
        (ModuleCat.ofHom (LinearMap.lsmul (A l E) (ULift.{u + 1} (A l E)) x))) ≫ e.hom =
      e.hom ≫ (coefficientEndEquiv l E W n (LocallyConstant.const _
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x))).asHom := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let F := Mod.extendScalars (AdicCompletion.quotient l E W n)
  let s := MonObj.one ≫ (upperStarFromPoint W).map (torsionIntegerMultiply l E x).asHom
  have hi := F.congr_map (FiniteModelQuotient.integralRegular_scalar l E W x)
  have he := FiniteModelQuotient.extendRegular_lift
    (AdicCompletion.quotient l E W n) s
  change F.map _ ≫ (F.map (integralRegular l E W).hom ≫
      (Mod.regularExtensionIso (AdicCompletion.quotient l E W n)).hom) =
    (F.map (integralRegular l E W).hom ≫
      (Mod.regularExtensionIso (AdicCompletion.quotient l E W n)).hom) ≫
        Mod.regularLift (Mod.regular (AdicCompletion.finiteRing l E W n))
          (coefficientSection l E W n (LocallyConstant.const _
            (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x)))
  rw [coefficientSection_integral]
  simp only [Functor.map_comp] at hi
  erw [← Category.assoc, hi, Category.assoc, he, ← Category.assoc]

/-- Fixed free-coordinate comparisons intertwine every finite matrix of integral scalars
with its entrywise constant residue matrix. -/
theorem quotientFreeMatrix_scalar (W : Scheme.{u}) (n a b : ℕ)
    (v : Fin a → Fin b → A l E) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    letI : (FiniteConstantModel.modelFunctor (A l E) W).Additive :=
      (((AdmissibleScalarRealization.admissible_scalar_realization_exact l W).2.2.1 E).1.1).2.1
    let F := FiniteConstantModel.modelFunctor (A l E) W
    let G := Mod.extendScalars (AdicCompletion.quotient l E W n)
    let H := F ⋙ G
    let S := ModuleCat.of (A l E) (ULift.{u + 1} (A l E))
    let e := G.mapIso (integralRegular l E W) ≪≫
      Mod.regularExtensionIso (AdicCompletion.quotient l E W n)
    H.map (biproduct.matrix (fun i j ↦ ModuleCat.ofHom
        (LinearMap.lsmul (A l E) (ULift.{u + 1} (A l E)) (v i j)))) ≫
      ((H.mapBiproduct (fun _ : Fin b ↦ S)) ≪≫
        biproduct.mapIso (fun _ ↦ e)).hom =
    ((H.mapBiproduct (fun _ : Fin a ↦ S)) ≪≫
      biproduct.mapIso (fun _ ↦ e)).hom ≫
        biproduct.matrix (fun i j ↦ (coefficientEndEquiv l E W n
          (LocallyConstant.const _
            (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) (v i j)))).asHom) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let F := FiniteConstantModel.modelFunctor (A l E) W
  let : F.Additive :=
    (((AdmissibleScalarRealization.admissible_scalar_realization_exact l W).2.2.1 E).1.1).2.1
  let G := Mod.extendScalars (AdicCompletion.quotient l E W n)
  let H := F ⋙ G
  let S := ModuleCat.of (A l E) (ULift.{u + 1} (A l E))
  let e := G.mapIso (integralRegular l E W) ≪≫
    Mod.regularExtensionIso (AdicCompletion.quotient l E W n)
  change H.map _ ≫ ((H.mapBiproduct (fun _ : Fin b ↦ S)).hom ≫
      biproduct.map (fun _ ↦ e.hom)) =
    ((H.mapBiproduct (fun _ : Fin a ↦ S)).hom ≫
      biproduct.map (fun _ ↦ e.hom)) ≫ _
  rw [← Category.assoc, Functor.mapBiproduct_matrix, Category.assoc, Category.assoc]
  congr 1
  erw [biproduct.matrix_map, biproduct.map_matrix]
  congr 1
  funext i j
  exact quotientRegular_scalar l E W n (v i j)

end AlgebraicGeometry.ProEtale.InternalPerfectMatrix
