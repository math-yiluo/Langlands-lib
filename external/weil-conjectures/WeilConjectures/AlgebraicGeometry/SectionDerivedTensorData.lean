/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
public import WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
public import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
public import WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
public import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.AlgebraicGeometry.SectionCochainTensorComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquations
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors

/-! # Canonical derived section-module tensor data

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03EK, 03EL,
03D7, 03DI and 03DJ; Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(auxiliary; not a blueprint node).

## Main definitions

- `derivedEquivalence`: localization of the fixed termwise section equivalence.
- `derivedPullback`, `derivedPushforward`: the actual ringed derived operations.
- `tensor`, `tensorUnit`, `tensorComparison`: normalized conjugate K-flat tensor data.
- `totalTensor`: the signed direct-sum total of the ordinary relative tensor.
- `localizedTotalComparison`: the specified total comparison after localization.

-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

namespace ResolvingOplaxConstraints
namespace TensorFunctorTransport

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D]

/-- A transported tensor vertex, shared before projecting any functor data.
Source: Stacks 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
def tensorObject (e : C ≌ D) (X Y : D) : D :=
  e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y)

/-- A transported tensor morphism, with its shared tensor vertices in the signature.
Source: Stacks 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
def tensorMorphism (e : C ≌ D) {X Y X' Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorObject e X Y ⟶ tensorObject e X' Y' :=
  e.functor.map ((e.inverse.map f ▷ e.inverse.obj Y) ≫
    (e.inverse.obj X' ◁ e.inverse.map g))

/-- The conjugated uncurried tensor, shared by the functor and monoidal data.
Source: Stacks 07A4 and 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
def tensorFunctor (e : C ≌ D) : D × D ⥤ D :=
  let B := (e.inverse.prod e.inverse) ⋙ Functor.uncurry.obj (curriedTensor C) ⋙ e.functor
  { obj := fun XY ↦ tensorObject e XY.1 XY.2
    map := fun f ↦ tensorMorphism e f.1 f.2
    map_id := fun X ↦ B.map_id X
    map_comp := fun f g ↦ B.map_comp f g }

/-- The transported unit object, shared with the section unit definition.
Source: Stacks 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
def unitObject (e : C ≌ D) : D := e.functor.obj (𝟙_ C)

/-- The transported associator, with vertices expressed by the shared tensor functor.
Source: Stacks 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
def associator (e : C ≌ D) (X Y Z : D) :
    (tensorFunctor e).obj ((tensorFunctor e).obj (X, Y), Z) ≅
      (tensorFunctor e).obj (X, (tensorFunctor e).obj (Y, Z)) :=
  @MonoidalCategoryStruct.associator _ _ (Monoidal.transportStruct e) X Y Z

/-- The transported left unitor at the shared unit and tensor vertices.
Source: Stacks 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
def leftUnitor (e : C ≌ D) (X : D) :
    (tensorFunctor e).obj (unitObject e, X) ≅ X :=
  @MonoidalCategoryStruct.leftUnitor _ _ (Monoidal.transportStruct e) X

/-- The transported right unitor at the shared unit and tensor vertices.
Source: Stacks 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
def rightUnitor (e : C ≌ D) (X : D) :
    (tensorFunctor e).obj (X, unitObject e) ≅ X :=
  @MonoidalCategoryStruct.rightUnitor _ _ (Monoidal.transportStruct e) X

/-- The transported tensor, using the existing uncurried tensor map formula.
Source: Stacks 07A4 and 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
@[instance_reducible]
def struct (e : C ≌ D) : MonoidalCategoryStruct D :=
  { (Monoidal.transportStruct e) with
    tensorObj := fun X Y ↦ (tensorFunctor e).obj (X, Y)
    tensorUnit := unitObject e
    associator := associator e
    leftUnitor := leftUnitor e
    rightUnitor := rightUnitor e
    tensorHom := fun {_X₁ _Y₁ _X₂ _Y₂} f g ↦
      (tensorFunctor e).map (Prod.mkHom f g) }

/-- The functor map formula equals the canonical tensor, by tensorHom_def.
Source: Stacks 07A4 and 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
theorem struct_eq (e : C ≌ D) : struct e = Monoidal.transportStruct e := by
  dsimp only [struct, tensorFunctor, tensorObject, tensorMorphism, unitObject,
    associator, leftUnitor, rightUnitor,
    Monoidal.transportStruct, Functor.comp,
    Functor.prod, Functor.uncurry, curriedTensor]
  congr 1
  funext X₁ Y₁ X₂ Y₂ f g
  exact congrArg e.functor.map (MonoidalCategory.tensorHom_def _ _).symm

/-- The four laws involving tensorHom transfer through the proved equality of data.
Source: Stacks 07A4 and 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
theorem laws (e : C ≌ D) :
    letI := struct e
    (∀ {X₁ Y₁ X₂ Y₂ : D} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      f ⊗ₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g)) ∧
    (∀ X₁ X₂ : D, (𝟙 X₁ ⊗ₘ 𝟙 X₂) = 𝟙 (X₁ ⊗ X₂)) ∧
    (∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : D} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
      (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂)) ∧
    (∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : D} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom =
        (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃))) := by
  rw [struct_eq]
  let := Monoidal.transport e
  exact ⟨MonoidalCategory.tensorHom_def, MonoidalCategory.id_tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.associator_naturality⟩

/-- The canonical transported monoidal category with the functor map formula exposed.
Source: Stacks 07A4 and 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
@[instance_reducible]
def monoidal (e : C ≌ D) : MonoidalCategory D :=
  { (Monoidal.transport e) with
    toMonoidalCategoryStruct := struct e
    tensorHom_def := (laws e).1
    id_tensorHom_id := (laws e).2.1
    tensorHom_comp_tensorHom := (laws e).2.2.1
    associator_naturality := (laws e).2.2.2 }

/-- The tensor functor of the shared full structure is the shared conjugate functor.
Source: Stacks 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
private theorem monoidal_ext (m n : MonoidalCategory D)
    (h : m.toMonoidalCategoryStruct = n.toMonoidalCategoryStruct) : m = n := by
  cases m
  cases n
  cases h
  rfl

/-- The full structure equals the canonical transport; its law fields are proofs.
Source: Stacks 07A4 and 06YU, fixed equivalence transport
(auxiliary; not a blueprint node). -/
theorem monoidal_eq (e : C ≌ D) : monoidal e = Monoidal.transport e :=
  monoidal_ext _ _ (struct_eq e)

end TensorFunctorTransport
end ResolvingOplaxConstraints

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- Read the source functor of the specified comparison without re-inferring its
large derived-functor instance arguments. This returns the actual source itself.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
@[implicit_reducible]
def comparisonSource {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {F G : C ⥤ D} (_e : F ≅ G) : C ⥤ D := F

/-- Countable coproducts supply the internal graded tensor in every degree.
Source: Stacks 06YN (auxiliary; not a blueprint node).
Proof: the degree-n index consists of pairs of integers with sum n, hence is
countable. The internal Grothendieck module category has this coproduct. -/
@[instance] theorem internal_hasGradedTensor (X : Scheme.{u})
    (P Q : GradedObject ℤ (internalModules Λ X)) : GradedObject.HasTensor P Q := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Countable coproducts supply the section-module graded tensor in every degree.
Source: Stacks 06YN (auxiliary; not a blueprint node).
Proof: use the coproduct over integer pairs of fixed total degree, whose existence
transfers through the fixed section-module equivalence. -/
@[instance] theorem section_hasGradedTensor (X : Scheme.{u})
    (P Q : GradedObject ℤ (modules Λ X)) : GradedObject.HasTensor P Q := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Relative tensor commutes with the countable sums defining the internal graded tensor.
Source: Stacks 03EK and 06YN (auxiliary; not a blueprint node).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem internal_goodTensorLeft (X : Scheme.{u})
    (P Q S : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q S := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Relative tensor commutes with the countable sums defining the internal graded tensor.
Source: Stacks 03EK and 06YN (auxiliary; not a blueprint node).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem internal_goodTensorRight (X : Scheme.{u})
    (P Q S : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q S := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Relative tensor commutes with the countable sums defining the internal graded tensor.
Source: Stacks 03EK and 06YN (auxiliary; not a blueprint node).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem internal_quadrupleTensorExt (X : Scheme.{u})
    (P Q S T : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q S T := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Relative tensor commutes with the countable sums defining the section graded tensor.
Source: Stacks 03EK and 06YN (auxiliary; not a blueprint node).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem section_goodTensorLeft (X : Scheme.{u})
    (P Q S : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q S := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Relative tensor commutes with the countable sums defining the section graded tensor.
Source: Stacks 03EK and 06YN (auxiliary; not a blueprint node).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem section_goodTensorRight (X : Scheme.{u})
    (P Q S : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q S := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Relative tensor commutes with the countable sums defining the section graded tensor.
Source: Stacks 03EK and 06YN (auxiliary; not a blueprint node).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem section_quadrupleTensorExt (X : Scheme.{u})
    (P Q S T : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q S T := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- The existing internal total derived pullback, with its category arguments fixed.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
@[implicit_reducible]
def internalDerivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (internalModules Λ Y) ⥤ DerivedCategory (internalModules Λ X) :=
  comparisonSource (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f)

/-- The existing internal total derived pushforward, with its category arguments fixed.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
@[implicit_reducible]
def internalDerivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (internalModules Λ X) ⥤ DerivedCategory (internalModules Λ Y) :=
  comparisonSource (CondensedRing.rightDerivedLowerStarIso Λ f)

set_option linter.unusedSectionVars false in
/-- The fixed section equivalence functor is additive.
Source: Stacks 00YV (auxiliary; not a blueprint node).
Proof: an equivalence preserves binary products, hence is additive between preadditive
categories. -/
theorem sectionFunctorAdditive (X : Scheme.{u}) :
    (equivalence Λ X).functor.Additive :=
  Functor.additive_of_preserves_binary_products (equivalence Λ X).functor

/-- The localization of the fixed termwise sectionwise functor.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
@[implicit_reducible]
def derivedFunctor (X : Scheme.{u}) :
    DerivedCategory (internalModules Λ X) ⥤ DerivedCategory (modules Λ X) :=
  (equivalence Λ X).functor.mapDerivedCategory

/-- Localizing the termwise equivalence again gives an equivalence.
Source: Stacks 05RU (auxiliary; not a blueprint node).
Proof: an equivalence preserves and reflects quasi-isomorphisms; its localization
is an equivalence. -/
@[instance] theorem derivedFunctor_isEquivalence (X : Scheme.{u}) :
    (derivedFunctor Λ X).IsEquivalence := by
  change (equivalence Λ X).functor.mapDerivedCategory.IsEquivalence
  infer_instance

/-- The induced derived equivalence, with the fixed localization functor as forward functor.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
@[implicit_reducible]
def derivedEquivalence (X : Scheme.{u}) :
    DerivedCategory (internalModules Λ X) ≌ DerivedCategory (modules Λ X) :=
  (derivedFunctor Λ X).asEquivalence

/-- The forward functor of the derived equivalence is the fixed localization.
Source: Stacks 05RU (auxiliary; not a blueprint node).
Proof: this is the forward field of the localized equivalence. -/
theorem derivedEquivalence_functor (X : Scheme.{u}) :
    (derivedEquivalence Λ X).functor = (equivalence Λ X).functor.mapDerivedCategory := rfl

/-- Ringed-topos derived pullback, levelwise since these coefficients pull back exactly.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
@[implicit_reducible]
def derivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (modules Λ Y) ⥤ DerivedCategory (modules Λ X) :=
  (pullback Λ f).mapDerivedCategory

/-- K-injective resolutions transfer through the sectionwise exact equivalence.
Source: Stacks 070H (auxiliary; not a blueprint node).
Proof: a chain map from an acyclic complex is null-homotopic on one side exactly
when its underlying linear maps give that same null-homotopy on the other. Transfer
the functorial internal K-injective resolution through the equivalence. -/
@[instance] theorem section_hasKInjectiveResolutions (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (modules Λ X) := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Functorial flat resolutions transfer through the fixed exact tensor equivalence.
Source: Stacks 03EK and 06YU (auxiliary; not a blueprint node).
Proof: conjugate the existing internal functorial flat-resolution functor by the
section equivalence, and transfer its augmentation using the counit. The existing
internal_section_tensor_comparison preserves flat objects and exactness, hence
preserves the flatness and epimorphism requirements of this resolution. -/
@[instance] theorem section_hasFunctorialFlatResolutions (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (modules Λ X) := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  classical
  let E := equivalence Λ X
  let e := ordinaryTensorComparison Λ X
  have hn := ordinaryTensorComparison_natural Λ X
  have hflat (M : internalModules Λ X) (hM : ObjectProperty.flat M) :
      ObjectProperty.flat (E.functor.obj M) := by
    let i : E.functor ⋙ tensorRight (E.functor.obj M) ≅ tensorRight M ⋙ E.functor :=
      NatIso.ofComponents (fun N ↦ (e N M).symm) (by
        intro N N' f
        dsimp
        rw [← cancel_epi (e N M).hom, ← cancel_mono (e N' M).hom]
        simpa [e, E] using (hn N N' M M f (𝟙 M)).symm)
    let j : tensorRight (E.functor.obj M) ≅ E.inverse ⋙ tensorRight M ⋙ E.functor :=
      (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight E.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.inverse i
    have := hM.tensorRight.preservesFiniteLimits
    have := hM.tensorRight.preservesFiniteColimits
    have hright : exactFunctor _ _ (tensorRight (E.functor.obj M)) :=
      (exactFunctor _ _).prop_of_iso j.symm
        ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩)
    exact ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (E.functor.obj M)).symm hright, hright⟩
  obtain ⟨L⟩ := (inferInstance : Abelian.HasFunctorialFlatResolution (internalModules Λ X))
  let T := E.inverse ⋙ L.F ⋙ ObjectProperty.flat.ι ⋙ E.functor
  let π : T ⟶ 𝟭 (modules Λ X) :=
    Functor.whiskerLeft E.inverse (Functor.whiskerRight L.π E.functor) ≫ E.counitIso.hom
  refine ⟨{ F := ObjectProperty.lift _ T (fun M ↦ hflat _ (L.F.obj (E.inverse.obj M)).property)
            π := π
            epi_π_app := ?_ }⟩
  intro M
  dsimp [π]
  infer_instance

/-- Actual K-injective derived ringed-site direct image.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
@[implicit_reducible]
def derivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (modules Λ X) ⥤ DerivedCategory (modules Λ Y) :=
  (pushforward Λ f).rightDerivedFunctor

/-- The usual uncurried signed-total functor with its object field written directly.
Source: Stacks 06YN (auxiliary; not a blueprint node).
The maps and both functor laws are those of the existing uncurried construction.
This record is definitionally equal to it, while its objects avoid reducing through
both curried functor categories. -/
def cochainTotalFunctor
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    (T : C ⥤ C ⥤ C) [T.PreservesZeroMorphisms]
    [∀ M, (T.obj M).PreservesZeroMorphisms]
    [∀ P Q : CochainComplex C ℤ, P.HasMapBifunctor Q T] :
    CochainComplex C ℤ × CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := CochainComplex.mapBifunctor K.1 K.2 T
  map f := (Functor.uncurry.obj T.map₂CochainComplex).map f
  map_id K := (Functor.uncurry.obj T.map₂CochainComplex).map_id K
  map_comp f g := (Functor.uncurry.obj T.map₂CochainComplex).map_comp f g

set_option linter.overlappingInstances false in
/-- The native signed total tensor of internal cochain complexes.
Source: Stacks 06YN (auxiliary; not a blueprint node). -/
def internalTotalTensor [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]
    (X : Scheme.{u}) :
    CochainComplex (internalModules Λ X) ℤ × CochainComplex (internalModules Λ X) ℤ ⥤
      CochainComplex (internalModules Λ X) ℤ :=
  cochainTotalFunctor (curriedTensor (internalModules Λ X))

/-- The existing lax localization tensor map, with its two functors fixed.
Source: Stacks 06YU (auxiliary; not a blueprint node).
Naturality is the naturality axiom of the actual localization tensorator. -/
@[irreducible] def internalLocalizationTensorMap (X : Scheme.{u}) :
    ((DerivedCategory.Q (C := internalModules Λ X)).prod DerivedCategory.Q) ⋙
        Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⟶
      internalTotalTensor Λ X ⋙ DerivedCategory.Q := by
  change ((DerivedCategory.Q (C := internalModules Λ X)).prod DerivedCategory.Q) ⋙
      Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⟶
    Functor.uncurry.obj (curriedTensor (CochainComplex (internalModules Λ X) ℤ)) ⋙
      DerivedCategory.Q
  exact {
    app K := Functor.LaxMonoidal.μ DerivedCategory.Q K.1 K.2
    naturality K L f := by
      simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
        CondensedRing.derivedTensor, Functor.uncurry_obj_map,
        curriedTensor_obj_map, curriedTensor_map_app,
        ← MonoidalCategory.tensorHom_def] using
        Functor.LaxMonoidal.μ_natural DerivedCategory.Q f.1 f.2
  }

set_option linter.unusedSectionVars false in
/-- The cached map has exactly the existing native localization components.
Source: Stacks 06YU (auxiliary; not a blueprint node).
Proof: project the displayed transformation's component. -/
theorem internalLocalizationTensorMap_app (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    (internalLocalizationTensorMap Λ X).app (P, Q) =
      Functor.LaxMonoidal.μ (DerivedCategory.Q (C := internalModules Λ X)) P Q := by
  unfold internalLocalizationTensorMap
  rfl

/-- The fixed monoidal transport, shared by the tensor and its constraint diagrams.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
@[instance_reducible]
def transportedDerivedMonoidal (X : Scheme.{u}) :
    MonoidalCategory (DerivedCategory (modules Λ X)) :=
  ResolvingOplaxConstraints.TensorFunctorTransport.monoidal (derivedEquivalence Λ X)

/-- The canonical sectionwise derived tensor, constructed by exact equivalence transport.
Its K-flat representative characterization is stated below, so this construction uses
precisely the ordinary sectionwise derived tensor, with no arbitrary bifunctor choice.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
def tensor (X : Scheme.{u}) :
    DerivedCategory (modules Λ X) × DerivedCategory (modules Λ X) ⥤
      DerivedCategory (modules Λ X) :=
  ResolvingOplaxConstraints.TensorFunctorTransport.tensorFunctor (derivedEquivalence Λ X)

/-- The tensor unit in the transported K-flat tensor model.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
def tensorUnit (X : Scheme.{u}) : DerivedCategory (modules Λ X) :=
  ((derivedEquivalence Λ X).functor).obj
    ((DerivedCategory.singleFunctor (internalModules Λ X) 0).obj (𝟙_ (internalModules Λ X)))

/-- The tensor comparison is uniquely specified by the equivalence unit.
Source: Stacks 06YU (auxiliary; not a blueprint node).
Proof: apply the derived equivalence to the tensor of its unit isomorphisms.
Naturality is the tensor of the two unit naturality equations. -/
theorem tensorComparison_existsUnique (X : Scheme.{u}) :
    ∃! t : Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⋙ (derivedEquivalence Λ
      X).functor ≅
        (((derivedEquivalence Λ X).functor).prod ((derivedEquivalence Λ X).functor)) ⋙ tensor Λ X,
      ∀ M N : DerivedCategory (internalModules Λ X),
        t.hom.app (M, N) = ((derivedEquivalence Λ X).functor).map
          (((CondensedRing.derivedTensor Λ X).map
            ((derivedEquivalence Λ X).unitIso.hom.app M)).app N ≫
              ((CondensedRing.derivedTensor Λ X).obj
                ((derivedEquivalence Λ X).inverse.obj (((derivedEquivalence Λ X).functor).obj
      M))).map
                  ((derivedEquivalence Λ X).unitIso.hom.app N)) := by
  let E := derivedEquivalence Λ X
  let B := Functor.uncurry.obj (CondensedRing.derivedTensor Λ X)
  let t : B ⋙ E.functor ≅ E.functor.prod E.functor ⋙ tensor Λ X :=
    Functor.isoWhiskerRight (NatIso.prod E.unitIso E.unitIso) (B ⋙ E.functor)
  refine ⟨t, ?_, ?_⟩
  · intro M N
    rfl
  · intro s hs
    apply Iso.ext
    apply NatTrans.ext
    funext ⟨M, N⟩
    exact hs M N

/-- The tensor comparison selected by its unique equivalence-unit normalization.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
def tensorComparison (X : Scheme.{u}) :
    Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⋙ (derivedEquivalence Λ X).functor ≅
      ((derivedEquivalence Λ X).functor.prod (derivedEquivalence Λ X).functor) ⋙ tensor Λ X :=
  (tensorComparison_existsUnique Λ X).exists.choose

set_option linter.overlappingInstances false in
/-- The sectionwise tensor of cochain complexes is the signed direct-sum total.
Source: Stacks 06YN (auxiliary; not a blueprint node). -/
def totalTensor [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]
    (X : Scheme.{u}) :
    CochainComplex (modules Λ X) ℤ × CochainComplex (modules Λ X) ℤ ⥤
      CochainComplex (modules Λ X) ℤ :=
  cochainTotalFunctor (curriedTensor (modules Λ X))

set_option linter.unusedSectionVars false in
/-- Naturality of the fixed ordinary tensor comparison.
Source: Stacks 03EK (auxiliary; not a blueprint node).
Proof: use the existing pure-tensor naturality calculation. -/
theorem sectionOrdinaryTensorNaturality (X : Scheme.{u})
    (M M' N N' : internalModules Λ X) (f : M ⟶ M') (g : N ⟶ N') :
    (equivalence Λ X).functor.map (f ⊗ₘ g) ≫ (ordinaryTensorComparison Λ X M' N').hom =
      (ordinaryTensorComparison Λ X M N).hom ≫
        ((equivalence Λ X).functor.map f ⊗ₘ (equivalence Λ X).functor.map g) := by
  exact ordinaryTensorComparison_natural Λ X M M' N N' f g

/-- The actual ordinary tensor comparison as a curried natural transformation.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
@[irreducible] def sectionOrdinaryTensorMap (X : Scheme.{u}) :
    (Functor.postcompose₂.obj (equivalence Λ X).functor).obj
        (curriedTensor (internalModules Λ X)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (equivalence Λ X).functor).obj
        (equivalence Λ X).functor).obj (curriedTensor (modules Λ X)) :=
  { app M :=
      { app N := (ordinaryTensorComparison Λ X M N).hom
        naturality N N' g := by
          simpa using sectionOrdinaryTensorNaturality Λ X M M N N' (𝟙 M) g }
    naturality M M' f := by
      apply NatTrans.ext
      funext N
      simpa using sectionOrdinaryTensorNaturality Λ X M M' N N f (𝟙 N) }

/-- Each ordinary comparison component is invertible.
Source: Stacks 03EK (auxiliary; not a blueprint node).
Proof: each component is the hom of ordinaryTensorComparison. -/
theorem sectionOrdinaryTensorMap_isIso (X : Scheme.{u})
    (M N : internalModules Λ X) : IsIso (((sectionOrdinaryTensorMap Λ X).app M).app N) := by
  unfold sectionOrdinaryTensorMap
  infer_instance

/-- The curried comparison has the prescribed ordinary components.
Source: Stacks 03EK (auxiliary; not a blueprint node).
Proof: unfold the natural transformation and read its component. -/
theorem sectionOrdinaryTensorMap_app (X : Scheme.{u})
    (M N : internalModules Λ X) :
    ((sectionOrdinaryTensorMap Λ X).app M).app N =
      (ordinaryTensorComparison Λ X M N).hom := by
  unfold sectionOrdinaryTensorMap
  rfl

attribute [local instance] sectionFunctorAdditive sectionOrdinaryTensorMap_isIso

/-- The specified total comparison, with the actual total functors fixed.
Source: Stacks 06YN (auxiliary; not a blueprint node).
This is the canonical signed map induced by the ordinary natural comparison. -/
@[irreducible] def sectionTotalComparison (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    ((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor (internalModules Λ X))) ⟶
      CochainComplex.mapBifunctor
        (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P)
        (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj Q)
        (curriedTensor (modules Λ X)) :=
  HomologicalComplex.mapBifunctorComparison (sectionOrdinaryTensorMap Λ X) (.up ℤ) P Q

/-- The canonical total map equals the existing uniquely normalized comparison.
Source: Stacks 06YN (auxiliary; not a blueprint node).
Proof: the mapBifunctor comparison is invertible because its ordinary components are
isomorphisms and the equivalence preserves coproducts. Its summand formula is exactly
the defining normalization, so uniqueness identifies the two isomorphisms. -/
theorem sectionTotalComparison_eq (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    sectionTotalComparison Λ X P Q = (totalComparison Λ X P Q).hom := by
  let t := asIso
    (HomologicalComplex.mapBifunctorComparison (sectionOrdinaryTensorMap Λ X) (.up ℤ) P Q)
  have ht : ∀ (p q n : ℤ) (h : p + q = n),
      (equivalence Λ X).functor.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h) ≫ t.hom.f n =
        (ordinaryTensorComparison Λ X (P.X p) (Q.X q)).hom ≫
          CochainComplex.ιMapBifunctor
            (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P)
            (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj Q)
            (curriedTensor _) p q n h := by
    intro p q n h
    change _ ≫
      (HomologicalComplex.mapBifunctorComparison
        (sectionOrdinaryTensorMap Λ X) (.up ℤ) P Q).f n = _
    rw [HomologicalComplex.mapBifunctorComparison_f]
    simpa only [sectionOrdinaryTensorMap_app] using
      HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
        (sectionOrdinaryTensorMap Λ X) (.up ℤ) P Q p q n h
  unfold sectionTotalComparison totalComparison
  exact congrArg Iso.hom ((totalComparison_existsUnique Λ X P Q).unique ht
    (totalComparison_existsUnique Λ X P Q).exists.choose_spec)

/-- The specified exact-functor localization factor, before taking a component.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
def sectionLocalizationIso (X : Scheme.{u}) :
    DerivedCategory.Q ⋙ (derivedEquivalence Λ X).functor ≅
      (equivalence Λ X).functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (equivalence Λ X).functor.mapDerivedCategoryFactors

/-- The specified localization comparison of the fixed termwise section equivalence.
Source: Stacks 05RU and 06YU (auxiliary; not a blueprint node). -/
def sectionLocalizationComparison (X : Scheme.{u})
    (P : CochainComplex (internalModules Λ X) ℤ) :
    (derivedEquivalence Λ X).functor.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (equivalence Λ X).functor.mapDerivedCategoryFactors.app P

/-- The fixed ordinary total comparison localized after the section factor map.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
def localizedTotalComparison (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    (derivedEquivalence Λ X).functor.obj
        ((DerivedCategory.Q (C := internalModules Λ X)).obj
          ((internalTotalTensor Λ X).obj (P, Q))) ⟶
      (DerivedCategory.Q (C := modules Λ X)).obj
        ((totalTensor Λ X).obj
          ((((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
            (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q))) :=
  (sectionLocalizationComparison Λ X
      ((internalTotalTensor Λ X).obj (P, Q))).hom ≫
    (DerivedCategory.Q (C := modules Λ X)).map (sectionTotalComparison Λ X P Q)

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
