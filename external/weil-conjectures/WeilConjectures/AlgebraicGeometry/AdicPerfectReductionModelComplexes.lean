/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons

/-! # Ordinary quotient complexes of constant perfect models

Source: Stacks Project, Tags 09C6, 06YY and 064B.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] adicResidueLocalReductionStep
  adicResidueConstantPerfect adicResidueRestriction

/-- The actual termwise completed constant complex restricted to the slice.
Source: Stacks Tag 09C6.
(auxiliary; not a blueprint node). -/
def adicPerfectLocalComplex (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :
    Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) :=
  let F := SheafOfModules.strictPerfectConstantSheaf
      (coefficientProEtaleModelTopology.{u, v} X) A ⋙
    SheafOfModules.restrictScalars
      (constantModuleHomRingIso (coefficientProEtaleModelTopology.{u, v} X) A).inv ⋙
    change (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J) ⋙
    SheafOfModules.overFunctor _ U
  (F.mapHomologicalComplex (.up ℤ)).obj P

attribute [local irreducible] adicPerfectLocalComplex

/-- Ordinary termwise reduction, before derived localization.
Source: Stacks Tags 09C6 and 06YY.
(auxiliary; not a blueprint node). -/
def adicPerfectQuotientComplex (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (n : ℕ) :
    Cx ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) :=
  ((change (adicResidueLocalProjection.{u, v} X J U n)).mapHomologicalComplex (.up ℤ)).obj
    (adicPerfectLocalComplex.{u, v} X J U P)

/-- The ring map used for the ordinary successor reduction on the slice.
Source: Stacks Tags 09C6 and 099M.
(auxiliary; not a blueprint node). -/
def adicPerfectQuotientScalarStep (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    (finite (coefficientProEtaleModelTopology.{u, v} X) A J (n + 1)).over U ⟶
      (finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U :=
  ((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
    (transition (coefficientProEtaleModelTopology.{u, v} X) A J n)

/-- The actual cone equation after restriction to the slice.
Source: Stacks Tag 099M.
(auxiliary; not a blueprint node).
Proof: restrict the limit cone equation at the successor arrow. -/
theorem adicPerfectQuotientScalarStep_comp (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    adicResidueLocalProjection.{u, v} X J U (n + 1) ≫ adicPerfectQuotientScalarStep.{u, v} X J U n =
      adicResidueLocalProjection.{u, v} X J U n := by
  let V := (coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U
  dsimp only [adicResidueLocalProjection, adicPerfectQuotientScalarStep]
  rw [← V.map_comp]
  congr 1
  simpa only [completed, projection, finiteSystem, Functor.ofOpSequence_map_homOfLE_succ] using
    (limit.w (finiteSystem (coefficientProEtaleModelTopology.{u, v} X) A J)
      (homOfLE (Nat.le_succ n)).op)

attribute [local irreducible] derivedExtension extend change

/-- Ordinary successor reassociation, fixed by scalar balancing on pure tensors.
Source: Stacks Tags 06YY and 09C6.
(auxiliary; not a blueprint node). -/
def adicPerfectQuotientStep (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (n : ℕ) :
    ((change (adicPerfectQuotientScalarStep.{u, v} X J U n)).mapHomologicalComplex (.up ℤ)).obj
        (adicPerfectQuotientComplex.{u, v} X J U P (n + 1)) ≅
      adicPerfectQuotientComplex.{u, v} X J U P n :=
  (Functor.mapHomologicalComplexCompIso
    (adicFiniteChangeComp (adicResidueLocalProjection.{u, v} X J U (n + 1))
      (adicPerfectQuotientScalarStep.{u, v} X J U n) ≪≫
        eqToIso (congrArg change (adicPerfectQuotientScalarStep_comp.{u, v} X J U n)))
    (.up ℤ)).app (adicPerfectLocalComplex.{u, v} X J U P)

attribute [local irreducible] adicPerfectQuotientComplex adicPerfectQuotientStep

/-- The existing derived balancing isomorphism, with its functors explicitly typed.
The explicit type prevents elaboration from expanding the full construction of
successive derived scalar extensions when using a component of this isomorphism.
Source: Stacks Tags 06YY and 09C6.
(auxiliary; not a blueprint node). -/
abbrev adicPerfectDerivedQuotientStep (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    adicResidueLocalReduction.{u, v} X J U (n + 1) ⋙
        extend (adicPerfectQuotientScalarStep.{u, v} X J U n) ≅
      adicResidueLocalReduction.{u, v} X J U n :=
  adicResidueLocalReductionStep.{u, v} X J U n

end AlgebraicGeometry.Scheme
