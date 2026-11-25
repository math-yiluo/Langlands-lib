/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
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
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.Derived.DerivedCoefficientMapDescent
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import Mathlib.Algebra.Homology.Functor

/-! # Normalized derived pullback of strict reduction towers

Source: Stacks Project, Tags 06YS, 06YY, 07A4 and 03EL
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe a b c d w w' t t'
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace CategoryTheory.StrictReduction

variable {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]

/-- Tensor with the actual coefficient tower, retaining every transition.
Source: Stacks 06YY, applied to strict towers
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def reduction (Q : ℕᵒᵖ ⥤ A) : A ⥤ (ℕᵒᵖ ⥤ A) :=
  Functor.const ℕᵒᵖ ⋙ tensorRight Q

/-- The ordinary augmentation induced by the coefficient unit.
Source: Stacks 03CZ and 06YY
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def augmentation (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q) :
    Functor.const ℕᵒᵖ ⟶ reduction Q :=
  Functor.whiskerLeft (Functor.const ℕᵒᵖ)
    ((rightUnitorNatIso (ℕᵒᵖ ⥤ A)).inv ≫ (curriedTensor (ℕᵒᵖ ⥤ A)).flip.map e)

variable [MonoidalPreadditive A]

/-- Additivity of termwise tensor reduction.
Source: Stacks 03EK, bilinearity of tensor
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
instance reduction_additive (Q : ℕᵒᵖ ⥤ A) : (reduction Q).Additive where
  map_add {M N} f g := by
    ext n
    change (f + g) ▷ Q.obj n = f ▷ Q.obj n + g ▷ Q.obj n
    exact (tensorRight (Q.obj n)).map_add (f := f) (g := g)

/-- Exact termwise pullback on strict towers.
Source: Stacks 02MZ, limits and colimits in diagram categories
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
abbrev termwise {B : Type c} [Category.{d} B] (F : A ⥤ B) :=
  (Functor.whiskeringRight ℕᵒᵖ A B).obj F

variable {B : Type c} [Category.{d} B] [Abelian B]

/-- Termwise preservation of finite limits, using pointwise limits.
Source: Stacks 02MZ (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
instance termwise_limits (F : A ⥤ B) [PreservesFiniteLimits F] :
    PreservesFiniteLimits (termwise F) where
  preservesFiniteLimits L := preservesLimitsOfShape_of_evaluation _ L (fun n ↦
    inferInstanceAs (PreservesLimitsOfShape L ((evaluation ℕᵒᵖ A).obj n ⋙ F)))

/-- Termwise preservation of finite colimits, using pointwise colimits.
Source: Stacks 02MZ (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
instance termwise_colimits (F : A ⥤ B) [PreservesFiniteColimits F] :
    PreservesFiniteColimits (termwise F) where
  preservesFiniteColimits L := preservesColimitsOfShape_of_evaluation _ L (fun n ↦
    inferInstanceAs (PreservesColimitsOfShape L ((evaluation ℕᵒᵖ A).obj n ⋙ F)))

/-- Constant towers commute with actual termwise pullback.
Source: Stacks 06YY (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def constantSquare (F : A ⥤ B) :
    Functor.const ℕᵒᵖ ⋙ termwise F ≅ F ⋙ Functor.const ℕᵒᵖ :=
  NatIso.ofComponents (fun M ↦ Functor.constComp ℕᵒᵖ M F)

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ℕᵒᵖ ⥤ A)]

/-- The universal derived reduction and its augmentation. The counit is part of the
left-derived universal property, and is required to compute every good representative.
Source: Stacks 06YY and 06XN (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
structure Model (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (good : CochainComplex A ℤ → Prop) where
  B : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A)
  counit : DerivedCategory.Q ⋙ B ⟶
    (reduction Q).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : B.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso A (.up ℤ))
  computes : ∀ P, good P → IsIso (counit.app P)
  i : (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory ⟶ B
  augmentation_eq : ∀ P, good P →
    i.app (DerivedCategory.Q.obj P) ≫ counit.app P =
      (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (augmentation Q e) (.up ℤ)).app P)

variable [MonoidalCategory B]

/-- The pulled-back coefficient unit, using the normalized pullback unit isomorphism.
Source: Stacks 03EL (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def pulledUnit (F : A ⥤ B) (j : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q) :
    (Functor.const ℕᵒᵖ).obj (𝟙_ B) ⟶ Q ⋙ F :=
  (Functor.const ℕᵒᵖ).map j.inv ≫ (Functor.constComp ℕᵒᵖ (𝟙_ A) F).inv ≫
    Functor.whiskerRight e F

/-- The ordinary comparison as one isomorphism of strict towers, natural in the input.
Source: Stacks 03EL (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def ordinaryComparison (F : A ⥤ B)
    (mu : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hmu : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (mu M' N').hom =
        (mu M N).hom ≫ (F.map f ⊗ₘ F.map g)) (Q : ℕᵒᵖ ⥤ A) :
    reduction Q ⋙ termwise F ≅ F ⋙ reduction (Q ⋙ F) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun n ↦ mu M (Q.obj n))
    (fun {m n} g ↦ by
      change F.map (𝟙 M ⊗ₘ Q.map g) ≫ (mu M (Q.obj n)).hom =
        (mu M (Q.obj m)).hom ≫ (𝟙 (F.obj M) ⊗ₘ F.map (Q.map g))
      simpa only [F.map_id] using hmu (𝟙 M) (Q.map g)))
    (fun {M N} f ↦ by
      ext n
      change F.map (f ▷ Q.obj n) ≫ (mu N (Q.obj n)).hom =
        (mu M (Q.obj n)).hom ≫ (F.map f ▷ F.obj (Q.obj n))
      simpa only [F.map_id, tensorHom_id] using hmu f (𝟙 (Q.obj n)))

variable [HasDerivedCategory.{w'} B] [HasDerivedCategory.{t'} (ℕᵒᵖ ⥤ B)]

/-- The canonical localization of the constant-tower square.
Source: Stacks 06YY (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def constantDerivedSquare (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory ⋙ (termwise F).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory :=
  letI : PreservesFiniteLimits (Functor.const ℕᵒᵖ ⋙ termwise F) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (Functor.const ℕᵒᵖ ⋙ termwise F) :=
    comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits (F ⋙ Functor.const ℕᵒᵖ) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (F ⋙ Functor.const ℕᵒᵖ) :=
    comp_preservesFiniteColimits _ _
  Functor.mapDerivedCategoryCompIso (Functor.const ℕᵒᵖ) (termwise F) ≪≫
    Functor.mapDerivedCategoryNatIso (constantSquare F) ≪≫
      (Functor.mapDerivedCategoryCompIso F (Functor.const ℕᵒᵖ)).symm

variable [MonoidalPreadditive B]

/-- Normalization by the universal reduction counits on every good representative.
The equation is the conjugation formula, with both exact-localization factors explicit.
Source: Stacks 06YY and 07A4
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def IsNormalized (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (j : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (goodA : CochainComplex A ℤ → Prop) (goodB : CochainComplex B ℤ → Prop)
    (MY : Model Q e goodA) (MX : Model (Q ⋙ F) (pulledUnit F j Q e) goodB)
    (mu : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hmu : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (mu M' N').hom =
        (mu M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (tau : MY.B ⋙ (termwise F).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ MX.B) : Prop :=
  ∀ P, goodA P →
    (termwise F).mapDerivedCategory.map (MY.counit.app P) ≫
        (termwise F).mapDerivedCategoryFactors.hom.app
          (((reduction Q).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryComparison F mu hmu Q) (.up ℤ)).hom.app P) =
      tau.hom.app (DerivedCategory.Q.obj P) ≫
        MX.B.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        MX.counit.app ((F.mapHomologicalComplex (.up ℤ)).obj P)

end CategoryTheory.StrictReduction

private noncomputable def cochainRepresentativeWhiskering
    {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{w} A]
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), good L ∧ QuasiIso p)
    (E : Type c) [Category.{d} E] :
    ((Functor.whiskeringLeft _ _ E).obj
      (ObjectProperty.ι good ⋙ DerivedCategory.Q)).FullyFaithful := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let P : ObjectProperty (CochainComplex A ℤ) := good
  let S : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ good X.as
  let f := S.lift (P.ι ⋙ q) (fun X ↦ X.property)
  have : f.Full := ⟨by
    intro X Y g
    obtain ⟨a, ha⟩ := q.map_surjective g.hom
    refine ⟨ObjectProperty.homMk a, ?_⟩
    exact ObjectProperty.hom_ext _ ha⟩
  have : f.EssSurj := ⟨by
    intro X
    obtain ⟨Y, hy⟩ := HomotopyCategory.quotient_obj_surjective X.obj
    refine ⟨⟨Y, ?_⟩, ⟨ObjectProperty.isoMk S (eqToIso hy)⟩⟩
    change S (q.obj Y)
    rw [hy]
    exact X.property⟩
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : S.FullSubcategory) (s : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨L, p, hL, hp⟩ := res X.as
    exact ⟨⟨q.obj L, hL⟩, q.map p,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩
  have : (S.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage S.ι) :=
    CategoryTheory.restriction_localization _ _ S hres
  let ff := (Localization.fullyFaithfulWhiskeringLeft (S.ι ⋙ DerivedCategory.Qh)
    ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage S.ι) E).comp
      (CategoryTheory.fullyFaithfulWhiskeringOfFullEssSurj f E)
  exact ff.ofIso ((Functor.whiskeringLeft _ _ E).mapIso
    (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A)))

namespace CategoryTheory.StrictReduction

end CategoryTheory.StrictReduction

namespace CategoryTheory.StrictReduction

open CochainPullback

universe uC vC uD vD r dR dS dTY dTX

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}

/-- Exactly the flat-term K-flat representatives in the statement.
Source: Stacks 06YS (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def flatRepresentatives (R : Sheaf J CommRingCat.{r}) (P : Complex R) : Prop :=
  P.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ, SheafOfModules.IsFlatOnSite (P.X n)

private theorem resolves (P : Complex R) :
    ∃ (L : Complex R) (p : L ⟶ P), flatRepresentatives R L ∧ QuasiIso p := by
  obtain ⟨L, p, hL, hflat, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
  exact ⟨L, p, ⟨hL, fun n ↦ (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (L.X n)).symm (hflat n)⟩, hp⟩

variable [HasDerivedCategory.{dR} (Modules R)]
  [HasDerivedCategory.{dS} (Modules S)]
  [HasDerivedCategory.{dTY} (ℕᵒᵖ ⥤ Modules R)]
  [HasDerivedCategory.{dTX} (ℕᵒᵖ ⥤ Modules S)]

private noncomputable def representativeWhiskering
    (E : Type a) [Category.{b} E] :
    ((Functor.whiskeringLeft _ _ E).obj
      (ObjectProperty.ι (flatRepresentatives R) ⋙ DerivedCategory.Q)).FullyFaithful :=
  cochainRepresentativeWhiskering (flatRepresentatives R) resolves E

end CategoryTheory.StrictReduction
