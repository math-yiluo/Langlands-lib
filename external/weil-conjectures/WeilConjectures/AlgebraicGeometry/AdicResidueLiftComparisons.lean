/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicConstructibleFiniteReductions
public import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
public import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
public import WeilConjectures.CategoryTheory.SiteConstantModuleHom
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.BifunctorShift

/-! # Coefficient comparisons for local adic perfect lifting

Source: Stacks Project, Tags 09C6, 099L and 06YY.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- The algebraic lift of comparison, specified on all operations and constants.
Source: Stacks Tags 00YV and 03D2
(auxiliary; not a blueprint node). -/
def adicResidueComparisonData (X : Scheme.{u}) :=
  Classical.choice (CategoryTheory.ConstantCompletion.inverseImageData_exists
    (smallModelComparisonPullback.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X))

/-- Derived comparison with its canonical constant coefficient map.
Source: Stacks Tags 06YY and 099R
(auxiliary; not a blueprint node). -/
def adicResidueComparison (X : Scheme.{u}) (R : Type (max v (u + 1))) [CommRing R] :=
  (CategoryTheory.ConstantCompletion.derivedPull (adicResidueComparisonData.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
    (CategoryTheory.ConstantCompletion.constantMap (adicResidueComparisonData.{u, v} X) R)).functor

/-- Completed constant realization of a complex of coefficient modules, termwise.
Source: Stacks Tag 09C6 (auxiliary; not a blueprint node). -/
def adicResidueConstantPerfect (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :
    CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A
        J) :=
  let F := SheafOfModules.strictPerfectConstantSheaf (coefficientProEtaleModelTopology.{u, v} X) A ⋙
    SheafOfModules.restrictScalars
      (CategoryTheory.constantModuleHomRingIso (coefficientProEtaleModelTopology.{u, v} X) A).inv ⋙
    CategoryTheory.ConstantCompletion.change
      (CategoryTheory.ConstantCompletion.coefficientMap (coefficientProEtaleModelTopology.{u, v}
        X) A J)
  (CategoryTheory.ConstantCompletion.Q
    (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A
      J)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

/-- Cohomology in the standard localization used by the coefficient package.
Source: Stacks Tag 05RU (auxiliary; not a blueprint node). -/
abbrev adicResidueCohomology {D : Type w} [SmallCategory D]
    {T : GrothendieckTopology D} (R : Sheaf T CommRingCat.{w}) (q : ℤ) :
    CategoryTheory.ConstantCompletion.D R ⥤ CategoryTheory.ConstantCompletion.Mod R :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q

/-- Exact restriction to the actual localized site, at the same standard localization.
Source: Stacks Tag 03DJ (auxiliary; not a blueprint node). -/
def adicResidueRestriction {D : Type w} [SmallCategory D]
    {T : GrothendieckTopology D} (R : Sheaf T CommRingCat.{w}) (U : D) :
    CategoryTheory.ConstantCompletion.D R ⥤ CategoryTheory.ConstantCompletion.D (R.over U) :=
  letI := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod R)
  letI := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod (R.over U))
  CategoryTheory.ringedDerivedRestriction R U

/-- Cohomology of the existing total tensor with a module in degree zero.
With a K-flat first factor this is precisely the derived Tor test.
Source: Stacks Tags 06YS and 09C6
(auxiliary; not a blueprint node). -/
def adicResidueTensorCohomology {D : Type w} [SmallCategory D]
    {T : GrothendieckTopology D} (R : Sheaf T CommRingCat.{w})
    (P : CategoryTheory.ConstantCompletion.Cx R)
    (N : CategoryTheory.ConstantCompletion.Mod R) (q : ℤ) :
    CategoryTheory.ConstantCompletion.Mod R :=
  (((CategoryTheory.ringedKoszulTensor R).obj P).obj
    ((HomologicalComplex.single (CategoryTheory.ConstantCompletion.Mod R)
      (ComplexShape.up ℤ) 0).obj N)).homology q

/-- The residue-completion projection on the actual localized site.
Source: Stacks Tags 03DJ and 099M
(auxiliary; not a blueprint node). -/
def adicResidueLocalProjection (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :=
  ((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
    (CategoryTheory.ConstantCompletion.projection
      (coefficientProEtaleModelTopology.{u, v} X) A J n)

/-- Exact slice category over the completed coefficient ring.
Source: Stacks Tags 03DJ and 099M
(auxiliary; not a blueprint node). -/
abbrev AdicResidueLocalDerived (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :=
  CategoryTheory.ConstantCompletion.D
    ((CategoryTheory.ConstantCompletion.completed
      (coefficientProEtaleModelTopology.{u, v} X) A J).over U)

/-- Derived finite reduction on the slice, retaining the quotient coefficient action.
Source: Stacks Tags 06YY and 099M
(auxiliary; not a blueprint node). -/
def adicResidueLocalReduction (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :=
  CategoryTheory.ConstantCompletion.extend (adicResidueLocalProjection.{u, v} X J U n)

/-- Consecutive quotient reductions reassociate by the normalized scalar balancing map.
Source: Stacks Tags 06YY and 099M
(auxiliary; not a blueprint node). -/
def adicResidueLocalReductionStep (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :=
  let V := (coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U
  adicFiniteExtendComp (adicResidueLocalProjection.{u, v} X J U (n + 1))
    (V.map (CategoryTheory.ConstantCompletion.transition
      (coefficientProEtaleModelTopology.{u, v} X) A J n))
    (adicResidueLocalProjection.{u, v} X J U n) (by
      dsimp only [adicResidueLocalProjection]
      rw [← V.map_comp]
      congr 1
      simpa only [CategoryTheory.ConstantCompletion.projection,
        CategoryTheory.ConstantCompletion.finiteSystem,
        Functor.ofOpSequence_map_homOfLE_succ] using (limit.w
        (CategoryTheory.ConstantCompletion.finiteSystem
          (coefficientProEtaleModelTopology.{u, v} X) A J)
        (homOfLE (Nat.le_succ n)).op).symm)

/-- Hom reductions use scalar extension and conjugation by the same balancing maps.
Source: Stacks Tag 09C6
(auxiliary; not a blueprint node). -/
def adicResidueHomStep (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ) :
    ((adicResidueLocalReduction.{u, v} X J U (n + 1)).obj T ⟶
      (adicResidueLocalReduction.{u, v} X J U (n + 1)).obj M) →
    ((adicResidueLocalReduction.{u, v} X J U n).obj T ⟶
      (adicResidueLocalReduction.{u, v} X J U n).obj M) := fun f ↦
  let V := (coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U
  let τ := V.map (CategoryTheory.ConstantCompletion.transition
    (coefficientProEtaleModelTopology.{u, v} X) A J n)
  let e := adicResidueLocalReductionStep.{u, v} X J U n
  e.inv.app T ≫ (CategoryTheory.ConstantCompletion.extend τ).map f ≫ e.hom.app M

/-- The actual derived Hom tower between the finite reductions.
Source: Stacks Tag 09C6
(auxiliary; not a blueprint node). -/
def adicResidueHomTower (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M : AdicResidueLocalDerived.{u, v} X J U) : ℕᵒᵖ ⥤ Type (max v (u + 1) + 1) :=
  Functor.ofOpSequence
    (X := fun n ↦ ((adicResidueLocalReduction.{u, v} X J U n).obj T ⟶
      (adicResidueLocalReduction.{u, v} X J U n).obj M))
    (fun n ↦ ↾(adicResidueHomStep.{u, v} X J U T M n))

/-- Reduction of a single morphism gives a compatible section of the Hom tower.
Source: Stacks Tags 06YY and 09C6
(auxiliary; not a blueprint node). -/
def adicResidueHomSection (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    {T M : AdicResidueLocalDerived.{u, v} X J U} (f : T ⟶ M) :
    (adicResidueHomTower.{u, v} X J U T M).sections := by
  let F := adicResidueHomTower.{u, v} X J U T M
  let α : (Functor.const ℕᵒᵖ).obj PUnit ⟶ F :=
    NatTrans.ofOpSequence
      (fun n ↦ ↾(fun _ ↦ (adicResidueLocalReduction.{u, v} X J U n).map f)) (by
        intro n
        dsimp only [F, adicResidueHomTower]
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        ext x
        change (adicResidueLocalReduction.{u, v} X J U n).map f =
          adicResidueHomStep.{u, v} X J U T M n
            ((adicResidueLocalReduction.{u, v} X J U (n + 1)).map f)
        dsimp only [adicResidueHomStep, adicResidueLocalReduction]
        simpa only [Functor.comp_map, Category.assoc, Iso.inv_hom_id_app,
          Category.comp_id] using
          congrArg (fun k ↦ k ≫ (adicResidueLocalReductionStep.{u, v} X J U n).hom.app M)
            ((adicResidueLocalReductionStep.{u, v} X J U n).inv.naturality f))
  exact ⟨fun n ↦ α.app n PUnit.unit, fun {i j} g ↦
    congrArg (fun k ↦ k PUnit.unit) (α.naturality g).symm⟩

/-- Weak contractibility stated on the same slice and at the coefficient universe.
Source: Stacks Tags 090K and 09C6
(auxiliary; not a blueprint node). -/
def AdicResidueSliceWeaklyContractible (X : Scheme.{u})
    (U : coefficientProEtaleSiteModel.{u, v} X) : Prop :=
  ∀ (F G : Sheaf ((coefficientProEtaleModelTopology.{u, v} X).over U)
      (Type (max v (u + 1)))) (f : F ⟶ G),
    Epi f → Function.Surjective (f.hom.app (op (Over.mk (𝟙 U))))

end AlgebraicGeometry.Scheme
