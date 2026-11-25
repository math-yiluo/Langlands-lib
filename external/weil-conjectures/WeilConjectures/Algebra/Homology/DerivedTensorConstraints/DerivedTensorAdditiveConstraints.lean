/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
public import Mathlib.CategoryTheory.Products.Associator
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Localization.Pi

/-!
# Normalized derived tensor constraints and additivity

Source: Stacks Project, sites-cohomology.tex, Tag 0FPT
(lemma-symmetric-monoidal-derived), lemma-tensor-product-K-flat and
 definition-derived-tor (blueprint: lem-pur-derived-tensor-additive-constraints).

The tensor and representative comparison are the published descent constructions.
The auxiliary definitions just specialize existing categories, tensor functors and
chain isomorphisms. The statements include the empty product and unbounded objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w i e z

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Functor

namespace SheafOfModules.DerivedTensorConstraints

attribute [local irreducible] SheafOfModules.monoidalCategory
  siteDerivedTensorIndependentCoefficients KFlatFixedTensor.representativeIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance 4000] SheafOfModules.monoidalCategory

-- Prefer the native complex tensor when elaborating chain-level formulas.
attribute [local instance 4000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.map f) ℤ]

end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.flip.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.flip.map f) ℤ]

end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.map f) ℤ]
  [∀ X, (T.flip.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.flip.map f) ℤ]

end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift B ℤ] [HasShift Z ℤ]

end

section
variable {A CC H Z : Type*} [Category* A] [Category* CC] [Category* H] [Category* Z]
  {q : CC ⥤ H} {Q : H ⥤ Z} {F : CC × CC ⥤ CC} {P : ObjectProperty H}

end

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

local instance (I : Type) :
    HasColimitsOfShape (Discrete I) (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
  PresheafOfModules.hasColimitsOfShape
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj (Discrete I)

/-- The existing ordinary module-sheaf category.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev Modules := KFlatFixedTensor.Modules R

/-- The existing category of integer-indexed, unbounded cochain complexes.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev Complex := CochainComplex (Modules R) ℤ

/-- The native complex monoidal dictionary, named once for the public tensor formulas.
Source: Mathlib.Algebra.Homology.Monoidal
(blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev complexMonoidal : MonoidalCategory (Complex R) :=
  HomologicalComplex.monoidalCategory (Modules R) (.up ℤ)

/-- The native complex tensor data, shared by the public formulas and their proofs.
Source: Mathlib.Algebra.Homology.Monoidal
(blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev complexMonoidalStruct : MonoidalCategoryStruct (Complex R) :=
  HomologicalComplex.monoidalCategoryStruct (Modules R) (.up ℤ)

attribute [local instance 4001] complexMonoidal complexMonoidalStruct

/-- The resolving property on complexes, using the recorded K-flatness and flatness.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def resolvingComplex : ObjectProperty (Complex R) := fun E ↦
  CochainComplex.IsKFlatIndependentCoefficients E ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (E.X n)

/-- The full subcategory of flat-term K-flat complex representatives.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev Model := (resolvingComplex R).FullSubcategory

/-- The same resolving property in the homotopy category.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def resolvingHomotopy : ObjectProperty (HomotopyCategory (Modules R) (.up ℤ)) :=
  fun E ↦ resolvingComplex R E.as

variable [HasDerivedCategory.{w} (Modules R)]

/-- The existing derived category, with independent localization universe.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev D := DerivedCategory (Modules R)

/-- The fixed tensor from site-derived-tensor descent; no new tensor is selected.
Source: Stacks 06YU and 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev tensor := siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R

/-- Localization restricted to the full resolving homotopy subcategory.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev localization := (resolvingHomotopy R).ι ⋙
  (DerivedCategory.Qh : HomotopyCategory (Modules R) (.up ℤ) ⥤ D R)

/-- Total tensor with its resolving proof supplied by the recorded model theorem.
Source: Stacks 07A2 and 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def totalModel (E F : Model R) : Model R :=
  ⟨E.obj ⊗ F.obj,
    (KFlatTotalTensorModel.kFlat_total_tensor_model R E.obj F.obj
      E.property.1 F.property.1 E.property.2 F.property.2).1,
    (KFlatTotalTensorModel.kFlat_total_tensor_model R E.obj F.obj
      E.property.1 F.property.1 E.property.2 F.property.2).2.1⟩

/-- Shift with the resolving proof supplied by the fixed-tensor theorem.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def shiftModel (E : Model R) (a : ℤ) : Model R :=
  ⟨E.obj⟦a⟧,
    ((KFlatFixedTensor.kFlat_fixed_tensor_triangulated R).choose_spec
      E.obj E.property.1 E.property.2).2.1 a⟩

/-- The actual published representative isomorphism, on bundled resolving models.
Source: Stacks 06YU and 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def representative (E F : Model R) :
    DerivedCategory.Q.obj (E.obj ⊗ F.obj) ≅
      (tensor R).obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) :=
  KFlatFixedTensor.representativeIso R E.obj F.obj
    E.property.1 F.property.1 E.property.2 F.property.2

/-- Extract the right shift first and the left shift second. The first map has
coefficient (-1)^(bp) in shifted first-factor degree p, and the second is unsigned.
Source: Stacks more-algebra.tex, sign rules, and sites-cohomology.tex, 0FPT
(blueprint: lem-pur-derived-tensor-additive-constraints). -/
def chainShift (E F : Complex R) (a b : ℤ) :
    (E⟦a⟧ ⊗ F⟦b⟧) ≅ (E ⊗ F)⟦a + b⟧ :=
  CochainComplex.mapBifunctorShift₂Iso (E⟦a⟧) F (KFlatFixedTensor.ordinaryTensor R) b ≪≫
    (shiftFunctor (Complex R) b).mapIso
      (CochainComplex.mapBifunctorShift₁Iso E F (KFlatFixedTensor.ordinaryTensor R) a) ≪≫
    ((shiftFunctorAdd (Complex R) a b).app (E ⊗ F)).symm

/-- The two-variable functor with shifts inside the fixed derived tensor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev shiftedSource (a b : ℤ) :=
  ((shiftFunctor (D R) a).prod (shiftFunctor (D R) b)) ⋙ tensor R

/-- The two-variable functor with the sum of the shifts outside tensor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev shiftedTarget (a b : ℤ) := tensor R ⋙ shiftFunctor (D R) (a + b)

/-- The left-parenthesized ternary derived tensor functor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev leftAssociated := ((tensor R).prod (𝟭 (D R))) ⋙ tensor R

/-- The right-parenthesized ternary derived tensor functor on the same domain.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev rightAssociated := CategoryTheory.prod.associator (D R) (D R) (D R) ⋙
  ((𝟭 (D R)).prod (tensor R)) ⋙ tensor R

/-- The swapped tensor functor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev swapped := CategoryTheory.Prod.swap (D R) (D R) ⋙ tensor R

/-- The normalized shift comparison on resolving pairs, with every comparison inserted.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def shiftRepresentative (E F : Model R) (a b : ℤ) :
    (shiftedSource R a b).obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) ≅
      (shiftedTarget R a b).obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) :=
  (tensor R).mapIso (Iso.prod ((DerivedCategory.Q.commShiftIso a).app E.obj).symm
      ((DerivedCategory.Q.commShiftIso b).app F.obj).symm) ≪≫
    (representative R (shiftModel R E a) (shiftModel R F b)).symm ≪≫
    DerivedCategory.Q.mapIso (chainShift R E.obj F.obj a b) ≪≫
    (DerivedCategory.Q.commShiftIso (a + b)).app (E.obj ⊗ F.obj) ≪≫
    (shiftFunctor (D R) (a + b)).mapIso (representative R E F)

/-- Comparison from the iterated total to the left-parenthesized derived tensor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def leftRepresentative (E F G : Model R) :
    DerivedCategory.Q.obj ((E.obj ⊗ F.obj) ⊗ G.obj) ≅
      (leftAssociated R).obj
        ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj), DerivedCategory.Q.obj G.obj) :=
  representative R (totalModel R E F) G ≪≫
    (tensor R).mapIso (Iso.prod (representative R E F) (Iso.refl _))

/-- Comparison from the other iterated total to the right-parenthesized derived tensor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def rightRepresentative (E F G : Model R) :
    DerivedCategory.Q.obj (E.obj ⊗ (F.obj ⊗ G.obj)) ≅
      (rightAssociated R).obj
        ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj), DerivedCategory.Q.obj G.obj) :=
  representative R E (totalModel R F G) ≪≫
    (tensor R).mapIso (Iso.prod (Iso.refl _) (representative R F G))

/-- The complete representative normalization of the shift, associator and symmetry.
The equalities compare natural isomorphisms through their actual components.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def IsNormalized
    (t : ∀ a b : ℤ, shiftedSource R a b ≅ shiftedTarget R a b)
    (α : leftAssociated R ≅ rightAssociated R) (σ : tensor R ≅ swapped R) : Prop :=
  (∀ (a b : ℤ) (E F : Model R),
    (t a b).app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) =
      shiftRepresentative R E F a b) ∧
  (∀ E F G : Model R,
    α.app ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
        DerivedCategory.Q.obj G.obj) =
      (leftRepresentative R E F G).symm ≪≫
        DerivedCategory.Q.mapIso (α_ E.obj F.obj G.obj) ≪≫ rightRepresentative R E F G) ∧
  (∀ E F : Model R,
    σ.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) =
      (representative R E F).symm ≪≫
        DerivedCategory.Q.mapIso (CochainComplex.Monoidal.braiding E.obj F.obj) ≪≫
        representative R F E)

section

end

section

-- Expose the tensor aliases before comparing their total-complex object formulas.
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance 2000] KFlatFixedTensor.tensorAdditive
  KFlatFixedTensor.tensorObjAdditive KFlatFixedTensor.tensorHasMapBifunctor

attribute [local instance 2000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory SheafOfModules.cochainModulesMonoidal

omit [HasDerivedCategory (Modules R)] in
omit [HasDerivedCategory (Modules R)] in
private theorem totalTensor_map {E E' F F' : Complex R}
    (f : E ⟶ E') (g : F ⟶ F') :
    (Functor.uncurry.obj (KFlatFixedTensor.totalTensor R)).map (Prod.mkHom f g) =
      f ⊗ₘ g := by
  rw [MonoidalCategory.tensorHom_def]
  rfl

omit [HasDerivedCategory (Modules R)] in
attribute [local irreducible] representative

end

end SheafOfModules.DerivedTensorConstraints
