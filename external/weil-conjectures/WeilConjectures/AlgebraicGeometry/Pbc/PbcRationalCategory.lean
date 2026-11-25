/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.CategoryTheory.Linear.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension

/-!
# Raw rationalization of the integral constructible category

The constant sections act on completed-coefficient modules. Scalar localization
retains the integral objects and tensors their Hom modules; no Karoubi envelope occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- The completed coefficient map from constant scalars, through its canonical limit
comparison. -/
def pbcCompletedScalar :=
  adicDatumScalar T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite } ≫ (pbcCompletedComparison T d).hom

/-- Constant scalar sections of the completed ring. -/
def pbcCompletedSection (U : T.ProEtᵒᵖ) :
    A →+* (pbcAdicCompletion T d).obj.obj U :=
  ((pbcCompletedScalar T d).hom.app U).hom.comp
    (((toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).app U).hom)

/-- Constant completed sections commute with every restriction. -/
theorem pbcCompletedSection_naturality (U V : T.ProEtᵒᵖ) (f : U ⟶ V) (a : A) :
    (pbcAdicCompletion T d).obj.map f (pbcCompletedSection T d U a) =
      pbcCompletedSection T d V a := by
  let s := toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫ (pbcCompletedScalar T d).hom
  change (s.app U ≫ (pbcAdicCompletion T d).obj.map f) a = s.app V a
  exact (ConcreteCategory.congr_hom (s.naturality f) a).symm

/-- The scalar action factors through the compatible global sections of the completed
ring. -/
def pbcCompletedScalarSections :
    A →+* RingCat.sectionsSubring
      ((pbcAdicCompletion T d).obj ⋙ forget₂ CommRingCat RingCat) where
  toFun a := ⟨fun U ↦ pbcCompletedSection T d U a,
    fun f ↦ pbcCompletedSection_naturality T d _ _ f a⟩
  map_one' := by ext U; exact (pbcCompletedSection T d U).map_one
  map_mul' a b := by ext U; exact (pbcCompletedSection T d U).map_mul a b
  map_zero' := by ext U; exact (pbcCompletedSection T d U).map_zero
  map_add' a b := by ext U; exact (pbcCompletedSection T d U).map_add a b

/-- Completed modules are A-linear by their actual constant-section action. -/
instance pbcCompletedModulesLinear : Linear A (pbcModules T (pbcAdicCompletion T d)) :=
  letI : Linear (RingCat.sectionsSubring
      ((pbcAdicCompletion T d).obj ⋙ forget₂ CommRingCat RingCat))
      (pbcModules T (pbcAdicCompletion T d)) :=
    SheafOfModules.homLinear (pbcAdicCompletion T d).obj
      (((adicLisseForget T).obj (pbcAdicCompletion T d)).property)
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) (pbcCompletedScalarSections T d)
    smul_comp := fun M N P a f g ↦
      Linear.smul_comp M N P (pbcCompletedScalarSections T d a) f g
    comp_smul := fun M N P f a g ↦
      Linear.comp_smul M N P f (pbcCompletedScalarSections T d a) g }

/-- The inherited A-linearity on the ambient derived category. -/
instance pbcCompletedDerivedLinear : Linear A (PbcCompletedDerived T d) := inferInstance

/-- The full integral subcategory inherits precisely the ambient scalar action. -/
instance pbcIntegralLinear : Linear A (PbcBoundedConstructibleComplete T d) := inferInstance

/-- Raw scalar localization at a uniformizer; the generic definition's Hom modules are
Localization.Away p tensor the integral Hom modules. For the finite p-adic integer
ring this localization is canonically E by integers_localization_uniformizer. -/
abbrev PbcRationalCategory (p : A) :=
  ScalarLocalization A (PbcBoundedConstructibleComplete T d) p

/-- Identity on integral objects and tensor with one on their morphisms. -/
abbrev pbcRationalization (p : A) :
    PbcBoundedConstructibleComplete T d ⥤ PbcRationalCategory T d p :=
  ScalarLocalization.localization A (PbcBoundedConstructibleComplete T d) p

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite-extension rational category on the base `T`. The hypotheses
restrict the scope of this notation; the category itself is the raw localization. -/
abbrev PbcRationalDerivedCategory (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :=
  PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)

end AlgebraicGeometry.Scheme
