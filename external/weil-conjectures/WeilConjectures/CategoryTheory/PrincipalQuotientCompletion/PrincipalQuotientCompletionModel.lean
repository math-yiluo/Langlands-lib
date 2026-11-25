/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism

/-! # Universal principal quotient completion with its strict unit

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT and 0941.
(blueprint: def-pur-principal-quotient-completion-model).

The ordinary functor uses the existing sheaf cokernel quotients and total tensor,
followed by the actual signed Roos cone. Its derived universal pair, computed on
K-flat complexes, presents quotient completion when countable products are exact.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.PrincipalQuotientCompletion

/-- Transpose a tower of complexes, using the existing degreewise construction.
Source: Stacks 0941 (blueprint: def-pur-principal-quotient-completion-model). -/
def transpose {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r}) :
    (ℕᵒᵖ ⥤ CochainComplex
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) ⥤
    CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ where
  obj := koszulTowerComplex R
  map := koszulTowerComplexMap R
  map_id X := by ext i n; rfl
  map_comp f g := by ext i n; rfl

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})

/-- The functor `P ↦ (R/t^(n+1)[0] ⊗ P)_n`, with the recorded strict quotient maps.
Source: Stacks 06YT and 0941
(blueprint: def-pur-principal-quotient-completion-model). -/
noncomputable def quotientTower
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) :
    CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ ⥤
    CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ := by
  let instPresheafCoproducts (I : Type r) : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  exact (curriedTensor (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))).map₂CochainComplex.flip ⋙
    (Functor.whiskeringLeft ℕᵒᵖ _ _).obj (principalReductionTower R t) ⋙ transpose R

/-- The actual signed Roos cone of the strict quotient tensor tower, functorially in `P`.
Source: Stacks 0941 (blueprint: def-pur-principal-quotient-completion-model). -/
noncomputable def quotientRoos
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) :=
  quotientTower R t ⋙ roosF

/-- The existing quotient map with its codomain expressed in the functorial tower.
Source: Stacks 06YT and 0941
(blueprint: def-pur-principal-quotient-completion-model). -/
noncomputable def quotientMap
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) (n : ℕ) :
    P ⟶ ((quotientTower R t).obj P).asFunctor.obj (op n) :=
  koszulRepresentativeQuotient R P t n

/-- The product of the canonical quotient maps into the functorial quotient tower.
Naming the map checks the concrete total-tensor identification once, before the model.
Source: Stacks 06YT and 0941
(blueprint: def-pur-principal-quotient-completion-model). -/
noncomputable def quotientProduct
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :
    P ⟶ roosP ((quotientTower R t).obj P) :=
  Pi.lift (quotientMap R t P)

variable [HasDerivedCategory.{w}
  (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]

/-- A universal derived principal quotient completion, including its canonical unit.
The counit and its K-flat computation fix the representative comparisons. The last two
fields specify the quotient augmentation on both product coordinates, on every complex.
Thus the data describe the canonical construction up to its unique compatible isomorphism.
Source: Stacks 06YS, 06YT and 0941
(blueprint: def-pur-principal-quotient-completion-model). -/
structure Model
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) where
  /-- Completion on the unbounded derived category. -/
  completion : DerivedCategory.{w} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ⥤
    DerivedCategory.{w} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
  /-- Universal comparison to the ordinary quotient Roos construction. -/
  counit : DerivedCategory.Q ⋙ completion ⟶ quotientRoos R t ⋙ DerivedCategory.Q
  /-- The total left-derived universal property at quasi-isomorphisms. -/
  universal : completion.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso _ (.up ℤ))
  /-- Computation on every K-flat representative, without boundedness. -/
  computes : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    IsIso (counit.app P)
  /-- The quotient-completion unit on the derived category. -/
  unit : 𝟭 _ ⟶ completion
  /-- The strict quotient augmentation before localization. -/
  augmentation : ∀ P, P ⟶ (quotientRoos R t).obj P
  /-- Product of quotient maps and zero shifted-product component. -/
  coordinates : ∀ P (p : ℤ),
    (augmentation P).f (p + 1) ≫ (roosχ ((quotientTower R t).obj P) p).hom =
      biprod.lift 0 ((quotientProduct R t P).f (p + 1))
  /-- Compatibility of the same unit with its universal representative comparison. -/
  unit_computes : ∀ P, unit.app (DerivedCategory.Q.obj P) ≫ counit.app P =
    DerivedCategory.Q.map (augmentation P)

end CategoryTheory.PrincipalQuotientCompletion
