/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Two-term scalar quotient resolutions after flat sheaf extension

Source: Stacks Project, Cohomology on Sites, Tags 06YQ and 06YU;
Modules on Sites, Tags 03EI and 03ER
(blueprint: lem-sfb-flat-scalar-cyclic-resolution).

The cone of scalar multiplication on the degree-zero ring complex is the displayed
complex in degrees -1 and 0. Its quotient is the sheaf cokernel, and the augmentation
is specified by its restriction to the degree-zero summand.
-/

@[expose] public section

universe u v r w

set_option autoImplicit false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (A : Type r) [CommRing A]
  [HasWeakSheafify J CommRingCat.{r}]

/-- The existing constant commutative ring sheaf.
Source: Stacks Tag 093I (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable abbrev scalarCyclicBase := (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A)

variable {J}

/-- Forget commutativity for the existing module-sheaf category.
Source: Stacks Tag 03CY (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable abbrev scalarCyclicRing (R : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

variable {A} (R : Sheaf J CommRingCat.{r})
  (α : scalarCyclicBase J A ⟶ R)

/-- The constant presheaf map adjoint to the given constant-sheaf algebra structure.
Source: Stacks Tags 03CY, 093I (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable def scalarCyclicPresheafMap :
    (Functor.const Cᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj :=
  (sheafificationAdjunction J CommRingCat.{r}).homEquiv _ _ α

/-- Multiplication by the constant scalar, constructed from its compatible sections.
Source: Stacks Tags 03CY, 03ER (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable def scalarCyclicMultiplication (a : A) :
    unit (scalarCyclicRing R) ⟶ unit (scalarCyclicRing R) :=
  (unit (scalarCyclicRing R)).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (scalarCyclicPresheafMap R α).app U a)
      (fun U V f ↦ by
        exact congrArg (fun g : CommRingCat.of A ⟶ R.obj.obj V ↦ g a)
          ((scalarCyclicPresheafMap R α).naturality f).symm))

private theorem scalar_cyclic_multiplication_apply (a : A) (U : Cᵒᵖ)
    (x : R.obj.obj U) :
    (scalarCyclicMultiplication R α a).val.app U x =
      (scalarCyclicPresheafMap R α).app U a * x := by
  change x * (scalarCyclicPresheafMap R α).app U a = _
  exact mul_comm _ _

omit [EssentiallySmall.{r} C] in
private theorem scalar_cyclic_presheaf_map_apply (a : A) (U : Cᵒᵖ) :
    (scalarCyclicPresheafMap R α).app U a =
      α.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a) := by
  rfl

omit [HasWeakSheafify J CommRingCat.{r}] in
private theorem constant_ring_locally_bijective :
    J.WEqualsLocallyBijective CommRingCat.{r} := by
  let : PreservesFilteredColimitsOfSize.{r, r} (CategoryTheory.forget CommRingCat.{r}) :=
    preservesFilteredColimitsOfSize_shrink _
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{r} C).inverse.op)
        CommRingCat.{r} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{r} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := CommRingCat.{r})

private theorem constant_scalar_mul_eq_zero [IsDomain A] (a : A) (ha : a ≠ 0)
    (U : Cᵒᵖ)
    (x : (sheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).obj U)
    (hx : (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a * x = 0) :
    x = 0 := by
  have := constant_ring_locally_bijective (J := J)
  let B := sheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  have hB : Presheaf.IsSheaf J B :=
    ((presheafToSheaf J CommRingCat.{r}).obj
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).property
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  apply hB.isSeparated _ _ (Presheaf.imageSieve_mem J η x)
  intro V f hf
  obtain ⟨b, hb⟩ := hf
  change A at b
  have hη (c : A) : B.map f.op (η.app U c) = η.app (Opposite.op V) c :=
    (NatTrans.naturality_apply η f.op c).symm
  have heq : η.app (Opposite.op V) (a * b) = η.app (Opposite.op V) 0 := by
    rw [map_mul, map_zero, hb, ← hη, ← map_mul, hx, map_zero]
  apply hB.isSeparated _ _ (Presheaf.equalizerSieve_mem J η (a * b) 0 heq)
  intro W g hg
  have hab : a * b = 0 := hg
  have hb0 : b = 0 := (mul_eq_zero.mp hab).resolve_left ha
  have hxV : B.map f.op x = 0 := by
    calc
      B.map f.op x = η.app (Opposite.op V) b := hb.symm
      _ = 0 := by rw [hb0]; exact map_zero (η.app (Opposite.op V)).hom
  change B.map g.op (B.map f.op x) = B.map g.op (B.map f.op 0)
  rw [hxV, map_zero (B.map f.op).hom]

private theorem flat_scalar_kernel [IsDomain A]
    (hflat : IsFlatOnSite (J := J) (R := scalarCyclicBase J A)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map α)).obj
        (unit (scalarCyclicRing R))))
    (a : A) (ha : a ≠ 0) (U : Cᵒᵖ) (x : R.obj.obj U)
    (hx : (scalarCyclicMultiplication R α a).val.app U x = 0) : x = 0 := by
  classical
  let B := scalarCyclicBase J A
  let F := (restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map α)).obj
      (unit (scalarCyclicRing R))
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  have hx' : η.app U a • (show F.val.obj U from x) = 0 := by
    change α.hom.app U (η.app U a) * x = 0
    rw [← scalar_cyclic_presheaf_map_apply R α a U,
      ← scalar_cyclic_multiplication_apply R α a U x]
    exact hx
  have hrel : (∑ _p : Fin 1, η.app U a • (show F.val.obj U from x)) = 0 := by
    simpa only [Fin.sum_univ_one] using hx'
  obtain ⟨S, hS, hf⟩ := local_equationalCriterion_of_isFlatOnSite.{u, v, r, r}
    B F hflat U.unop 1 (fun _ ↦ η.app U a) (fun _ ↦ x) hrel
  apply (unit (scalarCyclicRing R)).isSheaf.isSeparated _ S hS
  intro V f hmem
  obtain ⟨l, b, t, hb, hbt⟩ := hf V f hmem
  have hzero (q : Fin l) : b 0 q = 0 := by
    apply constant_scalar_mul_eq_zero a ha (Opposite.op V)
    have hη : B.obj.map f.op (η.app U a) = η.app (Opposite.op V) a :=
      (NatTrans.naturality_apply η f.op a).symm
    simpa only [Fin.sum_univ_one, hη] using hbt q
  have hz := hb 0
  simp only [hzero, zero_smul, Finset.sum_const_zero] at hz
  change R.obj.map f.op x = R.obj.map f.op 0
  exact hz.trans (map_zero (R.obj.map f.op).hom).symm

end SheafOfModules
