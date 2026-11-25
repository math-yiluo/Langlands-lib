/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomDerivedBraiding
public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomEvaluationNaturality
public import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
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

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # External global derived Hom and coefficient cones

Source: Stacks Project, Cohomology on Sites, Tags 08J9, 08JC, 0A90 and 0G7D;
blueprint main-20261015, `lem-pur-kunneth-supported.proof.md`, paragraphs 1 and 3
(blueprint: def-pur-external-rhom-pairing-interface).

## Main definitions

* `globalHom`, `evaluation`, `pairing`: global derived Hom and its evaluation transpose.
* `HomModel`, `HasChainNormalization`: evaluation-normalized cochain representatives.
* `IsNatural`, `CommutesWithOpenRestriction`: the four variances and restriction square.
* `HasSignedHomShift`, `PreservesCoefficientCones`: both signed triangle comparisons.

The assembly theorem is in `Sheaf.Paper.ExternalRHomConePairing`. This module
contains the shared interface needed by its independent proof obligations.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048

universe u uC vC uD vD uB vB wC wD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.ExternalRHom

/-- Transpose an evaluation after its two representative comparisons.
Source: Stacks 08JA (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def modelTransposeOf
    {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    (c : B ⥤ C) (h : Cᵒᵖ ⥤ C ⥤ B)
    (tr : ∀ (E K : C) (Q : B), (c.obj Q ⊗ E ⟶ K) → (Q ⟶ (h.obj (op E)).obj K))
    (Q : B) (E K V W : C) (α : c.obj Q ⟶ V)
    (μ : V ⊗ E ⟶ W) (t : W ⟶ K) : Q ⟶ (h.obj (op E)).obj K :=
  tr E K Q ((α ▷ E) ≫ μ ≫ t)

/-- Compare the tensor of two represented objects using a lax tensor constraint.
Source: Stacks 06YS (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def tensorModelOf
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (E H : C) (M N : D)
    (f : M ⟶ F.obj E) (g : N ⟶ F.obj H) : M ⊗ N ⟶ F.obj (E ⊗ H) :=
  (f ⊗ₘ g) ≫ Functor.LaxMonoidal.μ F E H

/-- Tensor two comparison arrows and postcompose with two further comparisons.
Source: Stacks 06YS and 0G7D (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def tensorThenOf
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {E E' H H' K M : C} (f : E ⟶ E') (g : H ⟶ H')
    (t : E' ⊗ H' ⟶ K) (i : K ⟶ M) : E ⊗ H ⟶ M :=
  (f ⊗ₘ g) ≫ t ≫ i

/-- A summand inclusion in the ordinary total tensor complex.
Source: Stacks 0A90 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def tensorInclusionOf
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (K L' : CochainComplex C ℤ) (r q n : ℤ) (h : r + q = n) :
    K.X r ⊗ L'.X q ⟶ (K ⊗ L').X n :=
  HomologicalComplex.ιTensorObj K L' r q n h

/-- Transpose an ordinary evaluation after the localization tensor constraint.
Source: Stacks 08JA and 06YS (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def chainModelTransposeOf
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [MonoidalCategory (CochainComplex C ℤ)]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    {B : Type uB} [Category.{vB} B]
    (Q : CochainComplex C ℤ ⥤ D) [Q.LaxMonoidal]
    (c : B ⥤ D) (h : Dᵒᵖ ⥤ D ⥤ B)
    (tr : ∀ (E K : D) (U : B), (c.obj U ⊗ E ⟶ K) → (U ⟶ (h.obj (op E)).obj K))
    (U : B) (E I V : CochainComplex C ℤ) (α : c.obj U ⟶ Q.obj V)
    (t : V ⊗ E ⟶ I) : U ⟶ (h.obj (op (Q.obj E))).obj (Q.obj I) :=
  modelTransposeOf c h tr U (Q.obj E) (Q.obj I) (Q.obj V) (Q.obj (V ⊗ E)) α
    (Functor.LaxMonoidal.μ Q V E) (Q.map t)

/-- Pull an ordinary chain evaluation through the canonical termwise comparisons.
Source: Stacks 0G7E (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def pullComplexEvaluationOf
    {B : Type uB} [Category.{vB} B] [Preadditive B]
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [MonoidalCategory (CochainComplex C ℤ)]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [MonoidalCategory (CochainComplex D ℤ)]
    (F : C ⥤ D) [F.Additive] [(F.mapHomologicalComplex (.up ℤ)).Monoidal]
    (c : B ⥤ C) [c.Additive] (d : B ⥤ D) [d.Additive] (α : d ≅ c ⋙ F)
    (E K : CochainComplex C ℤ) (U : CochainComplex B ℤ)
    (t : (c.mapHomologicalComplex (.up ℤ)).obj U ⊗ E ⟶ K) :
    (d.mapHomologicalComplex (.up ℤ)).obj U ⊗
        (F.mapHomologicalComplex (.up ℤ)).obj E ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj K :=
  pullEvaluationOf (F.mapHomologicalComplex (.up ℤ))
    (c.mapHomologicalComplex (.up ℤ)) (d.mapHomologicalComplex (.up ℤ))
    (Functor.mapHomologicalComplexCompIso α.symm (.up ℤ)).symm
    (fun E' H' ↦ (Functor.Monoidal.μIso (F.mapHomologicalComplex (.up ℤ)) E' H').hom) E K U t

/-- Share the total-tensor instance before specializing the coefficient site.
Source: Stacks 0A90 (blueprint: def-pur-external-rhom-pairing-interface). -/
@[instance_reducible]
noncomputable def complexesMonoidalOf
    (C : Type uC) [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C] :
    MonoidalCategory (CochainComplex C ℤ) := inferInstance

section DerivedModels

variable {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{wC} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

/-- The ordinary-complex counit, checked before specializing its categories.
Source: Stacks 05RU and 06YS (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def leftDerivedModelOf (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
    (U : CochainComplex C ℤ) :
    F.leftDerivedFunctor.obj (DerivedCategory.Q.obj U) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj U) :=
  F.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).inv.app U) ≫
    F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient C (.up ℤ)).obj U) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app U) ≫
    (DerivedCategory.quotientCompQhIso D).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj U)

end DerivedModels

variable (A : Type (u + 1)) [CommRing A]

/-- Share the native total tensor of coefficient complexes.
Source: Stacks 0A90 (blueprint: def-pur-external-rhom-pairing-interface). -/
@[instance_reducible]
noncomputable def coefficientComplexMonoidal :
    MonoidalCategory (CochainComplex (ModuleCat.{u + 1} A) ℤ) := inferInstance

attribute [local instance] coefficientComplexMonoidal

/-- Ordinary module-valued sheaves, the recorded constant-coefficient encoding.
Source: Stacks 08J7 (blueprint: def-pur-external-rhom-pairing-interface). -/
abbrev Modules (X : Scheme.{u}) := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)

/-- Cochain complexes of ordinary constant-coefficient module sheaves.
Source: Stacks 0A8X (blueprint: def-pur-external-rhom-pairing-interface). -/
abbrev Complexes (X : Scheme.{u}) := CochainComplex (Modules A X) ℤ

/-- Cache the existing monoidal structure on ordinary module sheaves.
Source: Stacks 06YL (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable instance modulesMonoidal (X : Scheme.{u}) : MonoidalCategory (Modules A X) :=
  inferInstance

/-- Cache the native direct-sum total tensor structure on complexes.
Source: Stacks 0A90 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable instance complexesMonoidal (X : Scheme.{u}) : MonoidalCategory (Complexes A X) :=
  complexesMonoidalOf (Modules A X)

/-- Cache the native Koszul braiding on ordinary total complexes.
Source: Stacks 0A90 (blueprint: def-pur-external-rhom-pairing-interface). -/
@[instance_reducible]
noncomputable def complexesBraiding (X : Scheme.{u}) :
    BraidedCategory (Complexes A X) := inferInstance

attribute [local instance] complexesBraiding

/-- Cache the existing derived tensor before elaborating its braiding and adjunctions.
Source: Stacks 06YS (blueprint: def-pur-external-rhom-pairing-interface). -/
@[instance_reducible]
noncomputable def siteDerivedMonoidal (X : Scheme.{u}) :
    MonoidalCategory (DerivedCategoryModule A X) := inferInstance

attribute [local instance] siteDerivedMonoidal

/-- Cache the existing closed structure at the same derived tensor.
Source: Stacks 08J9 (blueprint: def-pur-external-rhom-pairing-interface). -/
@[instance_reducible]
noncomputable def siteDerivedClosed (X : Scheme.{u}) :
    MonoidalClosed (DerivedCategoryModule A X) := inferInstance

attribute [local instance] siteDerivedClosed

/-- Cache the canonical localization tensor comparison.
Source: Stacks 06YS (blueprint: def-pur-external-rhom-pairing-interface). -/
@[instance_reducible]
noncomputable def siteLocalizationMonoidal (X : Scheme.{u}) :
    (DerivedCategory.Q (C := Modules A X)).LaxMonoidal := inferInstance

attribute [local instance] siteLocalizationMonoidal

/-- Use the existing canonical derived Koszul braiding at this fixed sheaf category.
Naming the specialization shares its inferred structure arguments between the evaluations.
Source: Stacks 0A90 (blueprint: def-pur-external-rhom-pairing-interface). -/
@[instance_reducible]
noncomputable def derivedBraiding (X : Scheme.{u}) :
    BraidedCategory (DerivedCategoryModule A X) :=
  DerivedCategory.braidedCategory' (Modules A X)

attribute [local instance] derivedBraiding

/-- The existing derived constant-coefficient functor.
Source: Stacks 07A6 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable abbrev constant (X : Scheme.{u}) :
    DerivedCategory (ModuleCat.{u + 1} A) ⥤ DerivedCategoryModule A X :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedFunctor

/-- The existing constant-coefficient derived inverse image.
Source: Stacks 0G7E (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable abbrev pull {X P : Scheme.{u}} (a : P ⟶ X) :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A P :=
  (upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor

/-- Existing module-valued derived global sections.
Source: Stacks 07A6 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable abbrev sections (X : Scheme.{u}) :
    DerivedCategoryModule A X ⥤ DerivedCategory (ModuleCat.{u + 1} A) :=
  rightDerivedGlobalSections (ModuleCat.{u + 1} A) X

/-- The existing closed derived internal Hom of ordinary module sheaves.
Source: Stacks 08J9 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable abbrev internalHom (X : Scheme.{u}) :=
  MonoidalClosed.internalHom (C := DerivedCategoryModule A X)

/-- Existing tensor--Hom adjunction in the ordinary module encoding.
Source: Stacks 08J9 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def closedAdjunction {X : Scheme.{u}} (E : DerivedCategoryModule A X) :
    tensorLeft E ⊣ (internalHom A X).obj (op E) :=
  MonoidalClosed.internalHomAdjunction₂.adj E

/-- Existing derived constant--sections adjunction in the common coefficient universe.
Source: Stacks 07A6 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def constantSectionsAdjunction (X : Scheme.{u}) :
    constant A X ⊣ sections A X :=
  derivedConstantGlobalSectionsAdjunction (ModuleCat.{u + 1} A) X

/-- Global derived Hom, using the existing closed derived tensor and derived sections.
Source: Stacks 08J9 and 08JA (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def globalHom (X : Scheme.{u}) :
    (DerivedCategoryModule A X)ᵒᵖ ⥤ DerivedCategoryModule A X ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  internalHom A X ⋙ (Functor.whiskeringRight _ _ _).obj (sections A X)

/-- The composite of the existing constant/sections and tensor/Hom adjunctions.
Source: Stacks 08J9 and 07A6 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def globalAdjunction {X : Scheme.{u}} (E : DerivedCategoryModule A X) :
    (constant A X ⋙ tensorLeft E) ⊣ (globalHom A X).obj (op E) :=
  (constantSectionsAdjunction A X).comp (closedAdjunction A E)

/-- The tensor--Hom transpose, with the global coefficient on the left.
Source: Stacks 08J9 and 07A6 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def transpose {X : Scheme.{u}}
    (E K : DerivedCategoryModule A X) (Q : DerivedCategory (ModuleCat.{u + 1} A))
    (t : (constant A X).obj Q ⊗ E ⟶ K) :
    Q ⟶ ((globalHom A X).obj (op E)).obj K :=
  (globalAdjunction A E).homEquiv Q K ((β_ E ((constant A X).obj Q)).hom ≫ t)

/-- Evaluation of global derived morphisms, as the composite adjunction counit.
Source: Stacks 08J9 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def evaluation {X : Scheme.{u}} (E K : DerivedCategoryModule A X) :
    (constant A X).obj (((globalHom A X).obj (op E)).obj K) ⊗ E ⟶ K :=
  (β_ E ((constant A X).obj (((globalHom A X).obj (op E)).obj K))).inv ≫
    (globalAdjunction A E).counit.app K

/-- The tensor constraint of the existing canonical monoidal inverse image.
Source: Stacks 0G7E (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def pullTensorIso {X P : Scheme.{u}} (a : P ⟶ X)
    (E H : DerivedCategoryModule A X) :
    (pull A a).obj E ⊗ (pull A a).obj H ≅ (pull A a).obj (E ⊗ H) :=
  letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) a
  Functor.Monoidal.μIso (pull A a) E H

/-- The canonical constant-pullback comparison, with its existing orientation.
Source: Stacks 0G7E (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def constantPullbackIso {X P : Scheme.{u}} (a : P ⟶ X) :
    constant A P ≅ constant A X ⋙ pull A a :=
  Functor.leftDerivedFunctorNatIso
      (constantSheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a).symm ≪≫
        Functor.leftDerivedFunctorCompIso
          (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
          (upperStar (ModuleCat.{u + 1} A) a)

/-- Pull evaluation back, with the canonical constant and tensor comparisons.
Source: Stacks 08J9 and 0G7E (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def pulledEvaluation {X P : Scheme.{u}} (a : P ⟶ X)
    (E K : DerivedCategoryModule A X) :
    (constant A P).obj
      (((globalHom A X).obj (op E)).obj K) ⊗
        (pull A a).obj E ⟶
      (pull A a).obj K :=
  pullEvaluationOf (pull A a) (constant A X) (constant A P)
    (constantPullbackIso A a)
    (fun E' H' ↦ (pullTensorIso A a E' H').hom) E K
    (((globalHom A X).obj (op E)).obj K) (evaluation A E K)

/-- The external evaluation transpose, with the Koszul interchange between the second
Hom factor and the first coefficient factor. Source: Stacks 08J9 and 0A90
(blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def pairing {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (E K : DerivedCategoryModule A X) (H L' : DerivedCategoryModule A Y) :
    ((globalHom A X).obj (op E)).obj K ⊗ ((globalHom A Y).obj (op H)).obj L' ⟶
      ((globalHom A P).obj (op ((pull A a).obj E ⊗
        (pull A b).obj H))).obj
          ((pull A a).obj K ⊗
            (pull A b).obj L') :=
  pairingOf (constant A P) (globalHom A P) (transpose A (X := P))
    (constantSheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedTensorComparison
    (((globalHom A X).obj (op E)).obj K) (((globalHom A Y).obj (op H)).obj L')
    ((pull A a).obj E) ((pull A b).obj H) ((pull A a).obj K) ((pull A b).obj L')
    (pulledEvaluation A a E K) (pulledEvaluation A b H L')

/-- Existing localization of ordinary sheaf complexes.
Source: Stacks 05RU (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable abbrev siteQ (X : Scheme.{u}) : Complexes A X ⥤ DerivedCategoryModule A X :=
  DerivedCategory.Q

/-- Existing localization of coefficient complexes.
Source: Stacks 05RU (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable abbrev moduleQ : CochainComplex (ModuleCat.{u + 1} A) ℤ ⥤
    DerivedCategory (ModuleCat.{u + 1} A) :=
  DerivedCategory.Q

/-- Global A-linear Hom cochains with the standard Hom differential, without a
boundedness assumption. Source: Stacks 0A8X
(blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def homComplex {X : Scheme.{u}} (E I : Complexes A X) :
    CochainComplex (ModuleCat.{u + 1} A) ℤ where
  X n := ModuleCat.of A (CochainComplex.HomComplex.Cochain E I n)
  d n m := ModuleCat.ofHom (CochainComplex.HomComplex.δ_hom A E I n m)
  shape n m h := ModuleCat.hom_ext (LinearMap.ext
    (fun z ↦ CochainComplex.HomComplex.δ_shape n m h z))
  d_comp_d' n m k _ _ := ModuleCat.hom_ext (LinearMap.ext
    (fun z ↦ CochainComplex.HomComplex.δ_δ n m k z))

/-- The termwise constant complex.
Source: Stacks 0A8X (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable abbrev constantComplex (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)


/-- The ordinary source of a global chain evaluation, using the native total tensor.
Source: Stacks 0A8X and 0A90 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def chainEvaluationSource (X : Scheme.{u})
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (E : Complexes A X) : Complexes A X :=
  (constantComplex A X).obj U ⊗ E

/-- A constant local section is the image under the sheafification unit.
Source: Stacks 0A8X (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def constantSection (X : Scheme.{u}) (M : ModuleCat.{u + 1} A)
    (W : X.Etaleᵒᵖ) (w : M) :
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M).obj.obj W :=
  (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app W w

/-- The canonical pure tensor of local sections, followed by sheafification.
Source: Stacks 06YL (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def tensorSection {X : Scheme.{u}} (M N : Modules A X)
    (W : X.Etaleᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) : (M ⊗ N).obj.obj W :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} A)) M N).app W) (TensorProduct.tmul A m n)

/-- The pure tensor of sections in a specified total-complex summand.
Source: Stacks 0A90 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def tensorComplexSection {X : Scheme.{u}} (K L' : Complexes A X)
    (r q n : ℤ) (h : r + q = n) (W : X.Etaleᵒᵖ)
    (x : (K.X r).obj.obj W) (y : (L'.X q).obj.obj W) :
    ((K ⊗ L').X n).obj.obj W :=
  ((tensorInclusionOf K L' r q n h).hom.app W)
    (tensorSection A (K.X r) (L'.X q) W x y)

/-- The evaluation identity for a chain map to a global Hom complex. This fixes every
local component, including the unsigned ordinary evaluation.
Source: Stacks 0A8X and 08J9 (blueprint: def-pur-external-rhom-pairing-interface). -/
def IsChainEvaluation {X : Scheme.{u}} (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (f : U ⟶ homComplex A E I)
    (t : chainEvaluationSource A X U E ⟶ I) : Prop :=
  ∀ (r q : ℤ) (W : X.Etaleᵒᵖ) (w : U.X r) (e : (E.X q).obj.obj W),
    ((t.f (q + r)).hom.app W)
      (tensorComplexSection A ((constantComplex A X).obj U) E
        r q (q + r) (add_comm r q) W (constantSection A X (U.X r) W w) e) =
      (((((f.f r).hom w).v q (q + r) rfl).hom.app W) e)

/-- The canonical realization of ordinary module sheaves over the commutative
constant ring sheaf, using the existing scalar-extension functor and ring comparison.
Source: Stacks 03CV and 093J (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def ringedRealization (X : Scheme.{u}) :=
  Scheme.etaleConstantModuleFunctor X A ⋙
    SheafOfModules.restrictScalars (realizationRingIso X.smallEtaleTopology A).hom

/-- Scalar realization is additive because its underlying maps of sections are unchanged.
Source: Stacks 03CV (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable instance ringedRealizationAdditive (X : Scheme.{u}) :
    (ringedRealization A X).Additive where
  map_add := by intros; ext W x; rfl

/-- Apply canonical scalar realization degreewise, retaining the full ringed-site complex.
Source: Stacks 03CV and 0A8X (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def ringedComplex (X : Scheme.{u}) :=
  (ringedRealization A X).mapHomologicalComplex (.up ℤ)

/-- The ordinary-complex counit for constant sheaves.
Source: Stacks 07A6 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def constantModel (X : Scheme.{u})
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (constant A X).obj
      ((moduleQ A).obj U) ⟶ (siteQ A X).obj ((constantComplex A X).obj U) :=
  leftDerivedModelOf (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) U

/-- The ordinary-complex counit for exact inverse image.
Source: Stacks 0G7E (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def pullModel {X P : Scheme.{u}} (a : P ⟶ X) (E : Complexes A X) :
    (pull A a).obj ((siteQ A X).obj E) ⟶
      (siteQ A P).obj
        (((upperStar (ModuleCat.{u + 1} A) a).mapHomologicalComplex (.up ℤ)).obj E) :=
  leftDerivedModelOf (upperStar (ModuleCat.{u + 1} A) a) E

/-- The evaluation-normalized comparison with global Hom cochains. Its universal
component identity fixes the comparison rather than allowing arbitrary automorphisms.
Source: Stacks 08JA and 08J9 (blueprint: def-pur-external-rhom-pairing-interface). -/
def IsHomModel {X : Scheme.{u}} (E I : Complexes A X)
    (iso : (moduleQ A).obj (homComplex A E I) ≅
      ((globalHom A X).obj (op ((siteQ A X).obj E))).obj ((siteQ A X).obj I)) : Prop :=
  ∀ (U : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (f : U ⟶ homComplex A E I) (t : chainEvaluationSource A X U E ⟶ I),
    IsChainEvaluation A E I U f t →
    (moduleQ A).map f ≫ iso.hom =
      chainModelTransposeOf (siteQ A X) (constant A X) (globalHom A X)
        (transpose A (X := X)) ((moduleQ A).obj U) E I ((constantComplex A X).obj U)
        (constantModel A X U) t

/-- An isomorphism satisfying the universal chain-evaluation normalization.
Source: Stacks 08JA and 08J9 (blueprint: def-pur-external-rhom-pairing-interface). -/
def HomModel {X : Scheme.{u}} (E I : Complexes A X) :=
  { iso : (moduleQ A).obj (homComplex A E I) ≅
    ((globalHom A X).obj (op ((siteQ A X).obj E))).obj ((siteQ A X).obj I) //
    IsHomModel A E I iso }

/-- The comparison isomorphism of an evaluation-normalized Hom model.
Source: Stacks 08JA and 08J9 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def HomModel.iso {X : Scheme.{u}} {E I : Complexes A X}
    (m : HomModel A E I) :
    (moduleQ A).obj (homComplex A E I) ≅
      ((globalHom A X).obj (op ((siteQ A X).obj E))).obj ((siteQ A X).obj I) :=
  m.val

/-- Pulling global morphisms back is the transpose of pulled-back evaluation.
For an open immersion this is the ordinary restriction map.
Source: Stacks 08JB (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def restriction {X P : Scheme.{u}} (a : P ⟶ X)
    (E K : DerivedCategoryModule A X) :
    ((globalHom A X).obj (op E)).obj K ⟶
      ((globalHom A P).obj (op ((pull A a).obj E))).obj
        ((pull A a).obj K) :=
  transpose A _ _ _ (pulledEvaluation A a E K)

/-- The ordinary pulled-back complex, with no derived replacement.
Source: Stacks 0G7E (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable abbrev pullComplex {X P : Scheme.{u}} (a : P ⟶ X) :=
  (upperStar (ModuleCat.{u + 1} A) a).mapHomologicalComplex (.up ℤ)


/-- The source coefficient complex on P in the chain normalization.
Source: Stacks 0A90 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable abbrev externalComplex {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (E : Complexes A X) (H : Complexes A Y) : Complexes A P :=
  (pullComplex A a).obj E ⊗ (pullComplex A b).obj H

/-- The canonical comparison from the derived external coefficient to its ordinary model.
Source: Stacks 06YS and 0G7E (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def externalModel {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (E : Complexes A X) (H : Complexes A Y) :
    (pull A a).obj ((siteQ A X).obj E) ⊗ (pull A b).obj ((siteQ A Y).obj H) ⟶
      (siteQ A P).obj (externalComplex A a b E H) :=
  tensorModelOf (siteQ A P) ((pullComplex A a).obj E) ((pullComplex A b).obj H)
    ((pull A a).obj ((siteQ A X).obj E)) ((pull A b).obj ((siteQ A Y).obj H))
    (pullModel A a E) (pullModel A b H)

/-- The target representative map uses the inverses of the K-flat resolution maps,
then the ordinary K-flat tensor and its K-injective resolution. It never tensors
K-injective representatives as an ordinary tensor.
Source: Stacks 0G7D and 0G7E (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def targetModel {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (N I : Complexes A X) (M I' : Complexes A Y) (J : Complexes A P)
    (c : N ⟶ I) (c' : M ⟶ I') [QuasiIso c] [QuasiIso c']
    (i : externalComplex A a b N M ⟶ J) :
    (pull A a).obj ((siteQ A X).obj I) ⊗
      (pull A b).obj ((siteQ A Y).obj I') ⟶ (siteQ A P).obj J :=
  tensorThenOf ((pull A a).map (inv ((siteQ A X).map c)))
    ((pull A b).map (inv ((siteQ A Y).map c')))
    (externalModel A a b N M) ((siteQ A P).map i)

/-- The morphism on global derived Hom, with both variances explicit.
Source: Stacks 08J9 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def homMap {X : Scheme.{u}} {E E' K K' : DerivedCategoryModule A X}
    (f : E' ⟶ E) (g : K ⟶ K') :
    ((globalHom A X).obj (op E)).obj K ⟶ ((globalHom A X).obj (op E')).obj K' :=
  ((globalHom A X).map f.op).app K ≫ ((globalHom A X).obj (op E')).map g

/-- The comparison of inverse images around a commuting square.
Source: Stacks 03D8 (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable def squarePullIso {X X' P P' : Scheme.{u}}
    (a : P ⟶ X) (j : X' ⟶ X) (p : P' ⟶ P) (a' : P' ⟶ X')
    (h : p ≫ a = a' ≫ j) (E : DerivedCategoryModule A X) :
    (pull A p).obj ((pull A a).obj E) ≅ (pull A a').obj ((pull A j).obj E) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p a).symm.app E ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a' j (p ≫ a) h).app E

open CategoryTheory.Pretriangulated.Opposite

/-- Contravariant global derived Hom with fixed target.
Source: Stacks 08JC (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable abbrev homFirst (X : Scheme.{u}) (K : DerivedCategoryModule A X) :
    (DerivedCategoryModule A X)ᵒᵖ ⥤ DerivedCategory (ModuleCat.{u + 1} A) :=
  (globalHom A X).flip.obj K

/-- Exact inverse image carries the shift comparison transported from termwise inverse image.
Source: Stacks 0G7E (blueprint: def-pur-external-rhom-pairing-interface). -/
noncomputable instance pullCommShift {X P : Scheme.{u}} (a : P ⟶ X) :
    (pull A a).CommShift ℤ :=
  Functor.CommShift.ofIso
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a).symm ℤ

variable [homShift : ∀ (X : Scheme.{u}) (K : DerivedCategoryModule A X),
  (homFirst A X K).CommShift ℤ]

end AlgebraicGeometry.Etale.ExternalRHom
