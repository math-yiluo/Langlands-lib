/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.TensorProduct.Finite

/-! # The explicit algebraic complex for a successive coefficient layer

Source: Stacks Project, sites-cohomology.tex, Tags 0942, 094H and 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- The actual ideal-power quotient, viewed over the residue coefficient ring.
Source: Stacks Project, Tags 0942 and 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
def finiteQuotientLayerModule {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :
    ModuleCat.{t} (A ⧸ I ^ (0 + 1)) :=
  ModuleCat.of _ ((I ^ (n + 1) : Ideal A) ⧸
    (I ^ (0 + 1) • ⊤ : Submodule A (I ^ (n + 1) : Ideal A)))

/-- The constructed residue module is the actual kernel of the quotient ring map.
Source: Stacks Project, Tag 094I, its ideal-layer identification.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
def finiteQuotientLayerKernelEquiv {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :
    finiteQuotientLayerModule I n ≃
      RingHom.ker (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
          I ^ (n + 1 + 1) ≤ I ^ (n + 1))) := by
  let e : finiteQuotientLayerModule I n ≃
      Ideal.map (Ideal.Quotient.mk (I ^ (n + 1 + 1))) (I ^ (n + 1)) := by
    simpa only [finiteQuotientLayerModule, Nat.reduceAdd, pow_one] using
      Ideal.powQuotPowSuccEquivMapMkPowSuccPow I (n + 1)
  exact e.trans (Set.equivOfEq (congrArg SetLike.coe
    (Ideal.Quotient.factor_ker
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
        I ^ (n + 1 + 1) ≤ I ^ (n + 1))).symm))

/-- Tensor with the ideal layer and retain the successor-ring action by restriction.
Source: Stacks Project, Tags 0942 and 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
def finiteQuotientLayerTensor {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :
    ModuleCat.{t} (A ⧸ I ^ (0 + 1)) ⥤ ModuleCat.{t} (A ⧸ I ^ (n + 1 + 1)) :=
  MonoidalCategory.tensorLeft (finiteQuotientLayerModule I n) ⋙
    ModuleCat.restrictScalars
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ n + 1 + 1)))

instance finiteQuotientLayerTensor_additive {A : Type t} [CommRing A]
    (I : Ideal A) (n : ℕ) : (finiteQuotientLayerTensor I n).Additive := by
  unfold finiteQuotientLayerTensor
  infer_instance

/-- Apply the layer tensor functor term by term, including to the differential.
Source: Stacks Project, Tags 0942, 094H and 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
def finiteQuotientLayerTensorComplex {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ I ^ (0 + 1))) ℤ) :
    CochainComplex (ModuleCat.{t} (A ⧸ I ^ (n + 1 + 1))) ℤ :=
  ((finiteQuotientLayerTensor I n).mapHomologicalComplex (.up ℤ)).obj P

/-- The ideal layer embeds in the finite successor quotient, hence is a finite type.
Source: Stacks Project, Tag 0942; Mathlib's ideal-power quotient equivalence.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
theorem finiteQuotientLayerModule_finite {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) : Finite (finiteQuotientLayerModule d.ideal n) := by
  have := d.quotientFinite (n + 1)
  exact Finite.of_equiv _ (finiteQuotientLayerKernelEquiv d.ideal n).symm

/-- Tensoring with the finite ideal layer has finite successor-coefficient terms.
Source: Stacks Project, Tags 0942 and 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
theorem finiteQuotientLayerTensorComplex_finite {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ)
    (hP : ∀ i : ℤ, Module.Finite (A ⧸ d.ideal ^ (0 + 1)) (P.X i)) (i : ℤ) :
    Module.Finite (A ⧸ d.ideal ^ (n + 1 + 1))
      ((finiteQuotientLayerTensorComplex d.ideal n P).X i) := by
  have := d.quotientFinite 0
  have := finiteQuotientLayerModule_finite d n
  have : Module.Finite (A ⧸ d.ideal ^ (0 + 1))
      (finiteQuotientLayerModule d.ideal n) := Module.Finite.of_finite
  have := hP i
  have : Finite ((finiteQuotientLayerModule d.ideal n) ⊗[A ⧸ d.ideal ^ (0 + 1)] P.X i) :=
    Module.finite_of_finite (A ⧸ d.ideal ^ (0 + 1))
  have : Finite ((finiteQuotientLayerTensorComplex d.ideal n P).X i) := by
    change Finite ((finiteQuotientLayerModule d.ideal n) ⊗[A ⧸ d.ideal ^ (0 + 1)] P.X i)
    infer_instance
  exact Module.Finite.of_finite

/-- A layer tensor complex retains the lower support bound, including for a zero layer.
Source: Stacks Project, Tag 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
theorem finiteQuotientLayerTensorComplex_ge {A : Type t} [CommRing A]
    (I : Ideal A) (n : ℕ)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ I ^ (0 + 1))) ℤ)
    (a : ℤ) (h : P.IsStrictlyGE a) :
    (finiteQuotientLayerTensorComplex I n P).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (finiteQuotientLayerTensor I n).map_isZero (P.isZero_of_isStrictlyGE a i hi)

/-- A layer tensor complex retains the upper support bound, even for an empty interval.
Source: Stacks Project, Tag 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
theorem finiteQuotientLayerTensorComplex_le {A : Type t} [CommRing A]
    (I : Ideal A) (n : ℕ)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ I ^ (0 + 1))) ℤ)
    (b : ℤ) (h : P.IsStrictlyLE b) :
    (finiteQuotientLayerTensorComplex I n P).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (finiteQuotientLayerTensor I n).map_isZero (P.isZero_of_isStrictlyLE b i hi)

end AlgebraicGeometry.Scheme
