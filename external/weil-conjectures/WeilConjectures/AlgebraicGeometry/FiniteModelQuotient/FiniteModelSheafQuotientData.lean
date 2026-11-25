/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Category.ModuleCat.Kernels
/-! # Finite reductions of integral scalar-model constructible sheaves

The coordinate definitions are shared by the chart comparison and descent.
(blueprint: def-sfb-finite-model-quotient-coordinates).

Source: blueprint main-20261015, localizing-closure ctf-equals-bc proof,
Local models, Locality and Strata paragraphs; Stacks Tags 093J, 093M, 06YQ, 06YY and 09AJ
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible).

The index n denotes the positive exponent n+1. All reductions use the existing actual
quotient map and take values in the derived category over the quotient coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteModelQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded integral scalar ring. Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev A := Padic.coefficientExtensionIntegers l E

/-- The recorded positive-level scalar quotient. Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev R (n : ℕ) := Padic.coefficientExtensionRing l E (n + 1)

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def quotientModules (n : ℕ) (T : Scheme.{u}) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.Internal (R l E n) T

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientModuleCategory (n : ℕ) (T : Scheme.{u}) :
    Category.{u + 1} (quotientModules l E n T) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  inferInstanceAs (Category (FiniteDiscreteOrdinary.Internal (R l E n) T))

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientModuleAbelian (n : ℕ) (T : Scheme.{u}) :
    @Abelian (quotientModules l E n T) (quotientModuleCategory l E n T) := by
  dsimp only [quotientModuleCategory, quotientModules]
  infer_instance

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientModuleDerived (n : ℕ) (T : Scheme.{u}) :
    @HasDerivedCategory.{u + 1} (quotientModules l E n T)
      (quotientModuleCategory l E n T) (quotientModuleAbelian l E n T) := by
  dsimp only [quotientModuleCategory, quotientModuleAbelian, quotientModules]
  infer_instance

attribute [instance] quotientModuleCategory quotientModuleAbelian quotientModuleDerived

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def quotientHomology (n : ℕ) (T : Scheme.{u}) (q : ℤ) :
    DerivedCategory (quotientModules l E n T) ⥤ quotientModules l E n T :=
  DerivedCategory.homologyFunctor _ q

/-- Ordinary quotient-module coordinates with the existing category structures.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def ordinaryHomology (n : ℕ) (T : Scheme.{u}) (q : ℤ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))) ⥤ Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) :=
  DerivedCategory.homologyFunctor _ q

/-- Exact quotient inverse image in the named module category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientUpperStar (n : ℕ) {V T : Scheme.{u}} (f : T ⟶ V) :
    quotientModules l E n V ⥤ quotientModules l E n T :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient (R l E n)) f

/-- Derived quotient inverse image in the named category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def quotientPullback (n : ℕ) {V T : Scheme.{u}} (f : T ⟶ V) :
    DerivedCategory (quotientModules l E n V) ⥤
      DerivedCategory (quotientModules l E n T) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  CondensedRing.moduleObjectDerivedPullback (FiniteDiscreteOrdinary.coefficient (R l E n)) f

/-- The normalized encoding with exactly the recorded quotient topology.
Source: blueprint finite-coefficient coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev Encoding (n : ℕ) (T : Scheme.{u}) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.Encoding (R l E n) T

/-- The specified ordinary encoding with its source written as the actual quotient
module category. Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def fixedEncoding (n : ℕ) (T : Scheme.{u}) (e : Encoding l E n T) :
    quotientModules l E n T ≌
      Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  e.ordinary.trans e.fixed

/-- The specified derived encoding with its source written as the actual quotient
module category. Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def derivedEncoding (n : ℕ) (T : Scheme.{u}) (e : Encoding l E n T) :
    DerivedCategory (quotientModules l E n T) ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  e.fixedDerived

/-- The recorded scalar-extension model, with the induced norm topology on A.
Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def model (T : Scheme.{u}) (P : ModuleCat.{u + 1} (A l E)) :
    AdicCompletion.Modules l E T :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  (FiniteConstantModel.modelFunctor (A l E) T).obj P

/-- Derived reduction of a sheaf in degree zero along the actual quotient homomorphism.
Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def reduction (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) (n : ℕ) :
    DerivedCategory (quotientModules l E n T) :=
  (AdicCompletion.derivedReduction l E T n).obj ((DerivedCategory.singleFunctor _ 0).obj M)

/-- Reduce every entry of the given scalar matrix by the actual quotient homomorphism.
The lift only puts the scalar coordinates in the site's coefficient universe.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def matrix (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    Matrix (Fin b) (Fin a) (ULift.{u + 1} (R l E n)) :=
  fun i j ↦ ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
    (v i j))

/-- The specified reduced scalar linear map, including ranks zero.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def differential (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    ModuleCat.of (ULift.{u + 1} (R l E n)) (Fin a → ULift.{u + 1} (R l E n)) ⟶
      ModuleCat.of (ULift.{u + 1} (R l E n)) (Fin b → ULift.{u + 1} (R l E n)) :=
  ModuleCat.ofHom (matrix l E n a b v).mulVecLin

/-- The literal complex of free quotient modules in degrees -1 and 0.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def scalarComplex (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) ℤ :=
  HomologicalComplex.double (differential l E n a b v)
    (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)

/-- Constant realization of that literal two-term scalar complex in ordinary coordinates.
Source: blueprint finite-coefficient coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def ordinaryComplex (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))) :=
  DerivedCategory.Q.obj
    (((constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (scalarComplex l E n a b v))

/-- The original integral scalar matrix in the lifted coordinates of the finite free modules.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def integralDifferential (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    ModuleCat.of (A l E) (Fin a → ULift.{u + 1} (A l E)) ⟶
      ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) :=
  ModuleCat.ofHom
    (((LinearEquiv.piCongrRight fun _ : Fin b ↦
        (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)).symm.toLinearMap).comp
      (v.mulVecLin.comp
        (LinearEquiv.piCongrRight fun _ : Fin a ↦
          (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)).toLinearMap))

/-- Internal coordinates for the literal two-term quotient complex, transported by
exactly the normalized finite coefficient equivalence (not an arbitrary equivalence).
Source: blueprint specified scalar resolution and ordinary coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def internalComplex (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) (e : Encoding l E n T) :
    DerivedCategory (quotientModules l E n T) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  (derivedEncoding l E n T e).inverse.obj (ordinaryComplex l E T n a b v)

/-- Properties of a specified quotient chart, kept as a record so projections do
not normalize the other derived cohomology types.
Source: blueprint Local models and Locality
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
structure ChartCalculation (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) (e : Encoding l E n T)
    (D : DerivedCategory (quotientModules l E n T)) : Prop where
  /-- The reduction is the specified two-term complex. -/
  complex : Nonempty (D ≅ internalComplex l E T n a b v e)
  /-- The degree -1 cohomology is the constant kernel. -/
  kernelModel :
    Nonempty ((ordinaryHomology l E n T (-1)).obj
      ((derivedEncoding l E n T e).functor.obj D) ≅
      (constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
          (kernel (differential l E n a b v)))
  /-- The degree zero cohomology is the constant cokernel. -/
  cokernelModel :
    Nonempty ((ordinaryHomology l E n T 0).obj
      ((derivedEncoding l E n T e).functor.obj D) ≅
      (constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
          (cokernel (differential l E n a b v)))
  /-- Finiteness of the scalar kernel. -/
  finiteKernel : Finite ↥(kernel (differential l E n a b v))
  /-- Finiteness of the scalar cokernel. -/
  finiteCokernel : Finite ↥(cokernel (differential l E n a b v))
  /-- Finite presentation of the scalar kernel. -/
  fpKernel : Module.FinitePresentation (ULift.{u + 1} (R l E n))
    ↥(kernel (differential l E n a b v))
  /-- Finite presentation of the scalar cokernel. -/
  fpCokernel : Module.FinitePresentation (ULift.{u + 1} (R l E n))
    ↥(cokernel (differential l E n a b v))

/-- The chart calculation for every specified scalar resolution on every member of
any chosen stratification and pro-etale covers. The two cohomology identifications
retain the quotient coefficient action. Source: blueprint Local models and Locality
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
structure LocalCalculationAt (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (enc : ∀ T : Scheme.{u}, Encoding l E n T)
    (K : DerivedCategory (quotientModules l E n V)) : Prop where
  /-- Every specified scalar chart has the required finite quotient calculation. -/
  chart :
    ∀ (S : Scheme.Stratification V)
      (C : ∀ i : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain i))
      (i : Fin S.n) (j : (C i).I₀) (P : ModuleCat.{u + 1} (A l E))
      (_hP : Module.FinitePresentation (A l E) P)
      (_eP : (CondensedRing.upperStar (DerivedNakayama.integerRing l E)
        ((C i).f j ≫ S.immersion i)).obj M ≅ model l E ((C i).X j) P)
      (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E))
      (w : ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) ⟶ P)
      (_hinj : Function.Injective (integralDifferential l E a b v).hom)
      (_hexact : Function.Exact (integralDifferential l E a b v).hom w.hom)
      (_hsurj : Function.Surjective w.hom),
      ChartCalculation l E ((C i).X j) n a b v (enc ((C i).X j))
        ((quotientPullback l E n
          ((C i).f j ≫ S.immersion i)).obj K)

/-- The universal chart calculation at the actual specified reduction.
Source: blueprint Local models and Locality
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
abbrev LocalCalculation (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (enc : ∀ T : Scheme.{u}, Encoding l E n T) : Prop :=
  LocalCalculationAt l E V M n enc (reduction l E V M n)

/-- Ordinary boundedness and intrinsic constructibility in the recorded finite-ring
encoding. The explicit finiteness witness installs only the finiteness just asserted
by the main theorem. Source: blueprint finite constructible cohomology clause
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def OrdinaryConclusion (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (hf : Finite (R l E n)) (e : Encoding l E n V) : Prop :=
  let := hf
  DerivedCategory.TStructure.t.bounded
    ((derivedEncoding l E n V e).functor.obj (reduction l E V M n)) ∧
    ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf V
      (ULift.{u + 1} (R l E n))
      ((ordinaryHomology l E n V q).obj
        ((derivedEncoding l E n V e).functor.obj (reduction l E V M n)))

end AlgebraicGeometry.ProEtale.FiniteModelQuotient
