/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Comparing the two integral coefficient presentations
-/

@[expose] public section

set_option autoImplicit false
set_option linter.privateModule false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section

private theorem spectral_embedded_norm
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] (x : ULift.{u} E.val) :
    Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val) x =
      ‖(x.down : PadicAlgCl ℓ)‖ := by
  let f : ULift.{u} E.val →+* PadicAlgCl ℓ :=
    E.val.val.toRingHom.comp ULift.ringEquiv.toRingHom
  let a : AbsoluteValue (ULift.{u} E.val) ℝ :=
    { toFun := fun x ↦ ‖f x‖
      map_mul' := fun x y ↦ by rw [map_mul, norm_mul]
      nonneg' := fun x ↦ norm_nonneg _
      eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero_iff f f.injective]
      add_le' := fun x y ↦ by rw [map_add]; exact norm_add_le _ _ }
  have ha : ∀ y : ℚ_[ℓ], a (algebraMap ℚ_[ℓ] (ULift.{u} E.val) y) = ‖y‖ := by
    intro y
    change ‖algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) y‖ = ‖y‖
    exact PadicAlgCl.norm_extends ℓ y
  exact (spectralNorm_unique_field_norm_ext ha x).symm
open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
private theorem mem_lift_integers
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] (x : ULift.{u} E.val) :
    x ∈ Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val) ↔
      x.down ∈ PadicAlgCl.integers ℓ E.val := by
  change Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val) x ≤ 1 ↔ _
  rw [spectral_embedded_norm ℓ E x, PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe]
  rfl
private noncomputable def integerLiftEquiv
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] :
    PadicAlgCl.integers ℓ E.val ≃+*
      Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val) where
  toFun x := ⟨ULift.up x.val, (mem_lift_integers ℓ E _).2 x.property⟩
  invFun x := ⟨x.val.down, (mem_lift_integers ℓ E _).1 x.property⟩
  left_inv _x := rfl
  right_inv _x := rfl
  map_mul' _x _y := rfl
  map_add' _x _y := rfl
private noncomputable def integerLiftHomeo
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
    letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
    letI : TopologicalSpace (ULift.{u} E.val) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    PadicAlgCl.integers ℓ E.val ≃ₜ
      Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val) := by
  letI src := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  letI tgt := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
  letI : TopologicalSpace (ULift.{u} E.val) :=
    tgt.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e := integerLiftEquiv ℓ E
  let sm : MetricSpace (PadicAlgCl.integers ℓ E.val) :=
    @Subtype.metricSpace E.val _ src.toMetricSpace
  let tm : MetricSpace (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)) :=
    @Subtype.metricSpace (ULift.{u} E.val) _ tgt.toMetricSpace
  letI : PseudoEMetricSpace (PadicAlgCl.integers ℓ E.val) :=
    sm.toPseudoMetricSpace.toPseudoEMetricSpace
  letI : PseudoEMetricSpace
      (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)) :=
    tm.toPseudoMetricSpace.toPseudoEMetricSpace
  have hi : @Isometry _ _ sm.toPseudoMetricSpace.toPseudoEMetricSpace
      tm.toPseudoMetricSpace.toPseudoEMetricSpace e := by
    apply @Isometry.of_dist_eq _ _ sm.toPseudoMetricSpace tm.toPseudoMetricSpace
    intro x y
    change Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)
      (-ULift.up x.val + ULift.up y.val) = dist
        (algebraMap E.val (PadicAlgCl ℓ) x.val)
        (algebraMap E.val (PadicAlgCl ℓ) y.val)
    rw [spectral_embedded_norm ℓ E]
    change ‖-(x.val : PadicAlgCl ℓ) + (y.val : PadicAlgCl ℓ)‖ =
      dist (x.val : PadicAlgCl ℓ) (y.val : PadicAlgCl ℓ)
    exact (dist_eq_norm_neg_add _ _).symm
  exact { e.toEquiv with
    continuous_toFun := hi.continuous
    continuous_invFun := (hi.right_inv e.right_inv).continuous }

open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
private noncomputable def integerRingSheafIso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] :
    Profinite.padicIntegersCondensedRing.{u} ℓ E.val ≅
      DerivedNakayama.integerRingSheaf ℓ (ULift.{u} E.val) := by
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
  letI : Norm (ULift.{u} E.val) := nf.toNorm
  letI : MetricSpace (ULift.{u} E.val) := nf.toMetricSpace
  letI : TopologicalSpace (ULift.{u} E.val) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e := integerLiftEquiv ℓ E
  let h := integerLiftHomeo ℓ E
  let forward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E.val) →+*
        ULift.{u + 1} C(S.unop, Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.toRingHom.compLeftContinuous _ h.continuous_toFun).comp ULift.ringEquiv.toRingHom)
  let backward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)) →+*
        ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E.val) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.symm.toRingHom.compLeftContinuous _ h.continuous_invFun).comp
        ULift.ringEquiv.toRingHom)
  refine
    { hom := ⟨{ app := fun S ↦ RingCat.ofHom (forward S)
                naturality := by intros; ext x; rfl }⟩
      inv := ⟨{ app := fun S ↦ RingCat.ofHom (backward S)
                naturality := by intros; ext x; rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext S x
    apply ULift.ext
    ext t
    rfl
  · ext S x
    apply ULift.ext
    ext t
    rfl

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (e : Λ ≅ Λ') [IsMonHom e.hom]
omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
open CategoryTheory.Limits
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (e : Λ ≅ Λ') [IsMonHom e.hom]
end

end AlgebraicGeometry.ProEtale
