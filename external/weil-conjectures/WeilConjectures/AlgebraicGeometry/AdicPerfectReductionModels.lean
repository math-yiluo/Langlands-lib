/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionModelComplexes
import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionModelsCompatibility
import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionModelsKProjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Ordinary complexes computing reductions of constant perfect models -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] adicResidueLocalReductionStep
  adicResidueConstantPerfect adicResidueRestriction
  adicPerfectLocalComplex derivedExtension extend change
  adicPerfectQuotientComplex adicPerfectQuotientStep

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- A single constant perfect complex has K-projective ordinary quotient models and
compatible identifications with its actual derived reductions. The square compares
only object computations; no Hom/cohomology comparison is asserted here.

Source: Stacks Tags 09C6, 06YY, 064B, and 09C5 (exact evaluation).
(auxiliary; not a blueprint node).

Proof: split each finite projective term as a retract of a finite free module.
Constant realization, scalar extension, and restriction preserve these splittings.
All terms of the local complex and its ordinary reductions are therefore flat and
bounded above, hence K-flat. The K-flat computation counit and the exact restriction
comparison give the displayed isomorphisms. On the weakly contractible slice the
rank-one free module represents exact final-object evaluation, so it is projective.
Finite sums and retracts are projective; the bounded-above quotient complex is
therefore K-projective by Tag 064B. For the square, use the same counits at both
successor levels. The normalization of adicFiniteExtendComp is its K-flat counit
square with adicFiniteChangeComp; after exact restriction this is precisely the
stated equality. Both ordinary balancing maps multiply the two adjacent scalars,
so this square also commutes with the restriction comparison. Zero complexes,
the unit ideal, the zero ring, and the empty slice have the zero computations. -/
theorem adicPerfectReductionModels (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (_hU : AdicResidueSliceWeaklyContractible.{u, v} X U)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hP : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i)) :
    let R := fun n : ℕ ↦
      (finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U
    let C : (n : ℕ) → Cx (R n) := fun n ↦ adicPerfectQuotientComplex.{u, v} X J U P n
    let R₀ := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
    let ρ : (n : ℕ) → D R₀ ⥤ D (R n) := fun n ↦ adicResidueLocalReduction.{u, v} X J U n
    (∀ n : ℕ, (C n).IsKProjective) ∧
    let T : D R₀ := (adicResidueRestriction
      (completed (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
        (adicResidueConstantPerfect.{u, v} X J P)
    ∃ r : ∀ n : ℕ, (ρ n).obj T ≅ (Q (R n)).obj (C n),
      ∀ n : ℕ,
        (extend (adicPerfectQuotientScalarStep.{u, v} X J U n)).map (r (n + 1)).hom ≫
            (extendComparison (adicPerfectQuotientScalarStep.{u, v} X J U n)).app
              (C (n + 1)) ≫
            (Q (R n)).map (adicPerfectQuotientStep.{u, v} X J U P n).hom =
          (adicPerfectDerivedQuotientStep.{u, v} X J U n).hom.app T ≫ (r n).hom := by
  dsimp only
  exact ⟨adicPerfectReductionModels_kprojective.{u, v} X J U _hU P a b _ha _hb _hP,
    adicPerfectReductionModels_compatibility.{u, v} X J U _hU P a b _ha _hb _hP⟩

end AlgebraicGeometry.Scheme
