/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
import WeilConjectures.SecSmoothPurity.CochainPullbackTensorShift
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.ObjectProperty.Shift
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.Algebra.Homology.PullbackTensorResolving.PullbackTensorResolvingComputation

/-! # Canonical shifts and action units of derived tensor pullback

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 07A4;
more-algebra.tex, Tag 0FNH, item-shift-tensor; sites-modules.tex, Tag 03EL.
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit).

The helper predicates spell out the normalizations in this node. All tensors,
representative comparisons, cochain unitors and pullback maps are existing ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep the signed-shift data folded when checking the resolving comparison squares.
attribute [local irreducible] CategoryTheory.CommShift₂Setup.int
attribute [local irreducible]
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjMap₂CochainComplex
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjFlipMap₂CochainComplex

universe uC vC uD vD r wR wS

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules.PullbackTensorCanonical

private theorem whiskering_fullyFaithful_iso
    {A B D : Type*} [Category A] [Category B] [Category D]
    (p q : A ⥤ B) (e : p ≅ q)
    (h : Nonempty (((Functor.whiskeringLeft A B D).obj p).FullyFaithful)) :
    Nonempty (((Functor.whiskeringLeft A B D).obj q).FullyFaithful) := by
  obtain ⟨ff⟩ := h
  exact ⟨ff.ofIso ((Functor.whiskeringLeft A B D).mapIso e)⟩


attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] siteDerivedTensorIndependentCoefficients
attribute [local irreducible] representativeIso
attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
attribute [local irreducible] Functor.curry
attribute [local irreducible] Functor.mapHomologicalComplex
attribute [local irreducible] Functor.mapBifunctorHomologicalComplex
attribute [local irreducible] HomologicalComplex₂.total
attribute [local irreducible] CategoryTheory.CochainPullback.comparison
attribute [local irreducible] CategoryTheory.CochainPullback.unit
attribute [local irreducible] HomologicalComplex.single
attribute [local irreducible] HomologicalComplex.rightUnitor HomologicalComplex.leftUnitor

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{wR} (Modules.{uC, vC, r} R)]
  [HasDerivedCategory.{wS} (Modules.{uD, vD, r} S)]

local notation "MR" => Modules (C := C) (J := J) R
local notation "MS" => Modules (C := D) (J := K) S
variable (R) in
/-- The published derived tensor with a stable name for its presentation.
The data is exactly `derivedTensor R`; no localization is reselected.
Source: Stacks 06YU.
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
def canonicalDerivedTensor : DerivedCategory (MR) ⥤ DerivedCategory (MR) ⥤
    DerivedCategory (MR) := derivedTensor R

/-- The given published shift structure, in the stable derived-tensor presentation.
This definition returns its input structure; it selects no new comparisons.
Source: Stacks 06YU and 0FNH.
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
@[instance_reducible]
def canonicalDerivedTensorCommShift [(derivedTensor R).CommShift₂Int] :
    (canonicalDerivedTensor R).CommShift₂Int :=
  inferInstanceAs (derivedTensor R).CommShift₂Int

attribute [local instance] canonicalDerivedTensorCommShift

local notation "TR" => canonicalDerivedTensor (C := C) (J := J) R
local notation "TS" => canonicalDerivedTensor (C := D) (J := K) S
local notation "tR₀" => totalTensor (C := C) (J := J) R
local notation "tS₀" => totalTensor (C := D) (J := K) S
local notation "DR" => derivedTensor (C := C) (J := J) R
local notation "DS" => derivedTensor (C := D) (J := K) S

variable (R) in
/-- The published resolving isomorphism in the stable derived-tensor presentation.
Source: Stacks 06YU.
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
def canonicalRepresentativeIso
    (P Q : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n, IsFlatOnSite (J := J) (R := R) (Q.X n)) :
    DerivedCategory.Q.obj (((tR₀).obj P).obj Q) ≅
      ((TR).obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q) :=
  representativeIso R P Q hp hq hf hg

/-- Normalization of the two derived tensor shifts by signed total-complex shifts.
The fixed-argument comparisons agree with the published resolving comparison.
`CommShift` includes the zero and addition laws, and `CommShift₂Int` includes
naturality in the other derived argument.
Source: Stacks 06YU and 0FNH
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
def HasCanonicalTensorShifts [(DR).CommShift₂Int] : Prop :=
  ∀ (P : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
    (∃ cL : (tR₀).obj P ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (TR).obj (DerivedCategory.Q.obj P),
      NatTrans.CommShift cL.hom ℤ ∧
      ∀ (Q : CochainComplex (MR) ℤ) (hq : Q.IsKFlatIndependentCoefficients)
        (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
        cL.app Q = canonicalRepresentativeIso.{uC, vC, r, wR} R P Q hp hq hf hg) ∧
    (∃ cR : (tR₀).flip.obj P ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (TR).flip.obj (DerivedCategory.Q.obj P),
      NatTrans.CommShift cR.hom ℤ ∧
      ∀ (Q : CochainComplex (MR) ℤ) (hq : Q.IsKFlatIndependentCoefficients)
        (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
        cR.app Q = canonicalRepresentativeIso.{uC, vC, r, wR} R Q P hq hp hg hf)

variable (f : RingedPullback.{r, uC, vC, uD, vD} R S)
  (k : Comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)
  (L : DerivedCategory (Modules.{uC, vC, r} R) ⥤
    DerivedCategory (Modules.{uD, vD, r} S))

variable (epsilon : DerivedCategory.Q ⋙ L ⟶
  pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f ⋙ DerivedCategory.Q)

local notation "pullF" => pull (J := J) (K := K) (R := R) (S := S) f

/-- The two derived bifunctors in the comparison.
Source: Stacks 07A4
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
abbrev Phi := Functor.uncurry.obj (TR) ⋙ L

/-- Pull back each input before taking the published derived tensor.
Source: Stacks 07A4
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
abbrev Psi := (L.prod L) ⋙ Functor.uncurry.obj (TS)

/-- The Tag 07A4 representative square, in an equivalent form avoiding inverses
of computation maps. Its cochain comparison is the prescribed insertion-of-one map.
Source: Stacks 07A4
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
def IsNormalized (tau : Phi L ⟶ Psi L) : Prop :=
  ∀ (P Q : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
    ∃ (hp' : CochainComplex.IsKFlatIndependentCoefficients
        ((pullF).obj P))
      (hq' : CochainComplex.IsKFlatIndependentCoefficients
        ((pullF).obj Q))
      (hf' : ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (((pullF).obj P).X n))
      (hg' : ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (((pullF).obj Q).X n)),
      L.map (canonicalRepresentativeIso.{uC, vC, r, wR} R P Q hp hq hf hg).hom ≫
          tau.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (Functor.uncurry.obj (TS)).map
            (Prod.mkHom (epsilon.app P) (epsilon.app Q)) =
        epsilon.app (((tR₀).obj P).obj Q) ≫
          DerivedCategory.Q.map (comparison.{r, uC, vC, uD, vD}
            (J := J) (K := K) (R := R) (S := S) f k P Q).hom ≫
          (canonicalRepresentativeIso.{uD, vD, r, wS} S
            ((pullF).obj P) ((pullF).obj Q)
            hp' hq' hf' hg').hom

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] canonicalDerivedTensor canonicalRepresentativeIso

omit [HasDerivedCategory.{wR} (Modules.{uC, vC, r} R)] in
@[no_expose] private abbrev resolvingProperty : ObjectProperty (CochainComplex (MR) ℤ) :=
  fun P ↦ P.IsKFlatIndependentCoefficients ∧
    ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n)


omit [HasDerivedCategory.{wR} (Modules.{uC, vC, r} R)] in
private theorem exists_resolving
    (A : CochainComplex (MR) ℤ) :
    ∃ (P : CochainComplex (MR) ℤ) (a : P ⟶ A), resolvingProperty (R := R) P ∧
      QuasiIso a := by
  obtain ⟨P, a, hp, hf, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients A
  have hflat : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm (hf n)
  exact ⟨P, a, ⟨hp, hflat⟩, ha⟩

private theorem resolving_fullyFaithful :
    let P := resolvingProperty (R := R)
    Nonempty (((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (DerivedCategory (MR) × DerivedCategory (MR)) (DerivedCategory (MS))).obj
        ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let PR := resolvingProperty (R := R)
  let PH : ObjectProperty (HomotopyCategory (MR) (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory (MR) (.up ℤ),
      ∃ (Y : PH.FullSubcategory) (a : Y.obj ⟶ X),
        HomotopyCategory.quasiIso (MR) (.up ℤ) a := by
    intro X
    obtain ⟨P, a, ⟨hp, hflat⟩, ha⟩ := exists_resolving (R := R) X.as
    exact ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj P, hp, hflat⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map a,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff a).2 ha⟩
  have hff := CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex (MR) ℤ) (H := HomotopyCategory (MR) (.up ℤ))
    (D := DerivedCategory (MR)) (DerivedCategory (MS))
    (HomotopyCategory.quotient _ (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso (MR) (.up ℤ)) DerivedCategory.Qh
    PR PH (fun _ ↦ Iff.rfl) hres
  exact whiskering_fullyFaithful_iso _ _
    (NatIso.prod (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso (MR)))
      (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso (MR)))) hff

-- Converting the published total tensor to its cochain monoidal presentation is costly.
-- Converting the published total tensor to its cochain monoidal presentation is costly.
attribute [local irreducible] HasCanonicalTensorShifts IsNormalized

-- The statement combines independently sized derived and total-tensor presentations.
end SheafOfModules.PullbackTensorCanonical

-- Restore Mathlib's original instance and priority for importing modules.
attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
