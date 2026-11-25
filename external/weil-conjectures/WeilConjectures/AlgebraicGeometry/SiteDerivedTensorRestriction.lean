/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
-- r4: side KFlat instances (global there), as local instances of the live theorems
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-!
# Derived tensor with scalar restriction on a ringed site

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-lem-sf-kunneth-star/lem-trf-ordinary-kunneth.proof.md, Step 2;
Stacks Project, Tags 03EK, 06YS, 06YU, 06YY
(auxiliary; not a blueprint node).

The comparison on one K-flat factor is normalized by the recorded two-factor descent
comparison. The representative formula uses this comparison, the change-of-rings counit,
and the exact restriction factorization. A single family `e` occurs in both the naturality
and representative clauses. Local pure tensors specify both directions of the chain map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true

universe u v r w a b va vb wa wb

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

/-- The ordinary total tensor bifunctor, using the recorded monoidal sheaf tensor.
Source: Stacks, Tag 06YU (auxiliary; not a blueprint node). -/
def SiteTensorComplexFunctor (A : Sheaf J CommRingCat.{r}) :
    CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) ℤ ⥤ CochainComplex
          (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) ℤ ⥤ CochainComplex
          (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) ℤ := by
  letI := SheafOfModules.monoidalCategory A
  exact (MonoidalCategory.curriedTensor (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A))).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- A local tensor in the monoidal tensor, through the sheafification-unit pure tensor.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
def siteMonoidalTmul (M N : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) (U : Cᵒᵖ) (x : M.val.obj U)
          (y : N.val.obj U) :
    ((SheafOfModules.monoidalCategory R).tensorObj M N).val.obj U := by
  letI := SheafOfModules.monoidalCategory R
  exact (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
    (SheafOfModules.siteSheafTensorTmul M N U x y)

/-- Include a local pure tensor in bidegree `(i,j)` of the total tensor complex.
Source: Stacks, Tag 06YU (auxiliary; not a blueprint node). -/
def siteTotalTmul (P Q : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (i j : ℤ)
    (U : Cᵒᵖ) (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    ((((SiteTensorComplexFunctor R).obj P).obj Q).X (i + j)).val.obj U := by
  letI := SheafOfModules.monoidalCategory R
  exact (HomologicalComplex.ιMapBifunctor P Q
    (MonoidalCategory.curriedTensor (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) (ComplexShape.up ℤ) i j
          (i + j) rfl).val.app U
      (siteMonoidalTmul (R := R) (P.X i) (Q.X j) U x y)

/-- The resolving class selected by the recorded independent-coefficient descent theorem.
Source: Stacks, Tags 06YS, 06YU (auxiliary; not a blueprint node). -/
def tensorDescentClass [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  (SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R).choose

/-- Its specified comparison with the total tensor on complexes.
Source: Stacks, Tag 06YU (auxiliary; not a blueprint node). -/
def tensorDescentComplexIso [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  (SheafOfModules.siteHomotopyTensorExistsIndependentCoefficients.{u, v, r, w}
    J R).choose_spec.1.some

/-- Its specified comparison with the recorded derived tensor on the resolving class.
Source: Stacks, Tag 06YU (auxiliary; not a blueprint node). -/
def tensorDescentDerivedIso [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  (SheafOfModules.siteDerivedTensorExistsIndependentCoefficients.{u, v, r, w} J R).choose_spec.some

/-- K-flatness with flat terms, using exactly the two recorded predicates.
Source: Stacks, Tags 06YN, 06YS (auxiliary; not a blueprint node). -/
def TensorFlatRepresentative (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X i)

/-- The recorded derived tensor, curried without constructing a second tensor product.
Source: Stacks, Tag 06YU (auxiliary; not a blueprint node). -/
abbrev siteRestrictionDerivedTensor [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)

/-- Canonical two-sided computation: totalization, homotopy quotient, and descent.
Source: Stacks, Tag 06YU (auxiliary; not a blueprint node). -/
def tensorDescentPair [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    (P Q : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hP : TensorFlatRepresentative P) (hQ : TensorFlatRepresentative Q) :
    DerivedCategory.Q.obj (((SiteTensorComplexFunctor R).obj P).obj Q) ≅
      ((siteRestrictionDerivedTensor (R := R)).obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj Q) := by
  let d := SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R
  let p : (tensorDescentClass (R := R)).FullSubcategory :=
    ⟨(HomotopyCategory.quotient _ _).obj P, (d.choose_spec.1 _).2 hP⟩
  let q : (tensorDescentClass (R := R)).FullSubcategory :=
    ⟨(HomotopyCategory.quotient _ _).obj Q, (d.choose_spec.1 _).2 hQ⟩
  exact (DerivedCategory.quotientCompQhIso (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso ((tensorDescentComplexIso (R := R)).symm.app (P, Q)) ≪≫
    (tensorDescentDerivedIso (R := R)).app (p, q) ≪≫
    (SheafOfModules.siteDerivedTensorIndependentCoefficients J R).mapIso
      (Iso.prod ((DerivedCategory.quotientCompQhIso (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).app P)
        ((DerivedCategory.quotientCompQhIso (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).app Q))

set_option hygiene false in
local notation "𝓜" A:arg => ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)

set_option backward.isDefEq.respectTransparency true

section TensorProof

set_option backward.isDefEq.respectTransparency false in
private abbrev siteSectionModule (A : Sheaf J CommRingCat.{r}) (M : 𝓜 A) (V : Cᵒᵖ) :
    Module (A.obj.obj V) (M.val.obj V) :=
  ModuleCat.isModule (M.val.obj V)

attribute [local instance] siteSectionModule

end TensorProof

attribute [local instance] siteSectionModule

end CategoryTheory
