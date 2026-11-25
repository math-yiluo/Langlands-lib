/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-! # Canonical projective diagonal pullback comparisons
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients

/-- Bundle the existing tensor and its existing shift comparison. -/
structure TensorBundle (D : Type a) [Category.{v} D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] where
  monoidal : MonoidalCategory D
  comm : letI := monoidal; (curriedTensor D).CommShift₂Int

/-- The native K-flat tensor with its native two-variable shift structure. -/
@[irreducible]
def nativeTensorBundle (C : Type a) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] : TensorBundle (DerivedCategory C) :=
  ⟨inferInstance, inferInstance⟩

-- Keep the fixed site and derived-functor comparisons folded during elaboration.
/-- First projection of the actual self-product. -/
def firstProjection (Y : Scheme.{u}) : diagonalSurface Y ⟶ ProjectiveLine Y :=
  pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)

-- Keep the fixed site and derived-functor comparisons folded during elaboration.
/-- Second projection of the actual self-product. -/
def secondProjection (Y : Scheme.{u}) : diagonalSurface Y ⟶ ProjectiveLine Y :=
  pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Specialize the fixed native tensor bundle. -/
@[irreducible]
def internalTensorBundle (X : Scheme.{u}) :
    TensorBundle (DerivedCategory (Modules Λ X)) :=
  nativeTensorBundle (Modules Λ X)
/-- The same derived tensor through its fixed bundle field. -/
instance internalMonoidal (X : Scheme.{u}) :
    MonoidalCategory (DerivedCategory (Modules Λ X)) :=
  (internalTensorBundle Λ X).monoidal
/-- The same signed shift comparison through its fixed bundle field. -/
instance internalTensorCommShift (X : Scheme.{u}) :
    (curriedTensor (DerivedCategory (Modules Λ X))).CommShift₂Int :=
  (internalTensorBundle Λ X).comm

-- Keep the fixed site and derived-functor comparisons folded during elaboration.
/-- The canonical section comparison, with no arbitrary isomorphism. -/
@[no_expose]
def pullSectionIso (Y : Scheme.{u}) (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    CondensedRing.moduleObjectDerivedPullback Λ f ⋙
      CondensedRing.moduleObjectDerivedPullback Λ (diagonalImmersion Y) ≅
        𝟭 (DerivedCategory (Modules Λ (ProjectiveLine Y))) :=
  (CondensedRing.leftDerivedUpperStarComp Λ (diagonalImmersion Y) f).symm ≪≫
    eqToIso (congrArg (fun g ↦ CondensedRing.moduleObjectDerivedPullback Λ g) h) ≪≫
      CondensedRing.leftDerivedUpperStarId Λ (ProjectiveLine Y)

/-- The canonical section comparison is the pullback compositor followed by the
identity comparison. This equation keeps the construction available without unfolding
it during unrelated dependent interface checks. -/
theorem pullSectionIso_eq (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    pullSectionIso Λ Y f h =
      (CondensedRing.leftDerivedUpperStarComp Λ (diagonalImmersion Y) f).symm ≪≫
        eqToIso (congrArg (fun g ↦ CondensedRing.moduleObjectDerivedPullback Λ g) h) ≪≫
          CondensedRing.leftDerivedUpperStarId Λ (ProjectiveLine Y) := by
  unfold pullSectionIso
  rfl

/-- The canonical single/unit comparison in the bundled interface, uniquely fixed by the
comparison. -/
theorem singleUnit_existsUnique (X : Scheme.{u}) :
    ∃! e : unit Λ X ≅ 𝟙_ (DerivedCategory (Modules Λ X)),
      HEq e (DerivedCategory.singleFunctorObjUnitIso (Modules Λ X)) := by
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
  refine ⟨DerivedCategory.singleFunctorObjUnitIso (Modules Λ X), HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- The single/unit isomorphism in the shared tensor interface. -/
def singleUnitIso (X : Scheme.{u}) : unit Λ X ≅ 𝟙_ (DerivedCategory (Modules Λ X)) :=
  (singleUnit_existsUnique Λ X).exists.choose

end AlgebraicGeometry.ProEtale.RationalP1
