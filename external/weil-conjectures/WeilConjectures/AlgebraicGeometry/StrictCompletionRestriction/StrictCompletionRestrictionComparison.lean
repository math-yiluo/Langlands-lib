/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictScalarCompletionFunctorComparison
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictIntegralCompletionPresentation
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionLimits
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionFiniteConstantModels
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionScalarPresentation
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictIntegralScalarPullback
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionPrincipalQuotientModels

/-! # Strict completion under section action and pro-etale restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open WeilConjectures
open CategoryTheory.InternalAbelianSheafModule

-- Upstream's `HasDerivedCategory` instances on these module categories are found first and then
-- fail the final defeq check, which blocks `HasDerivedCategory.ofIsGrothendieckAbelian`.
attribute [-instance] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOverModules

namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def coefficientTower (X : Scheme.{u}) :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n ↦ sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (AdicCompletion.finiteRing l E X n))
    (fun n ↦ sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (AdicCompletion.transition l E X n))
private def coefficientUnit (X : Scheme.{u}) :
    (Functor.const ℕᵒᵖ).obj (ModuleObjectRingedComparison.ring
      (DerivedNakayama.integerRing l E) X) ⟶ coefficientTower l E X := by
  refine NatTrans.ofOpSequence (fun n ↦ sectionScalarMap.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (AdicCompletion.quotient l E X n)) ?_
  intro n
  simp only [Functor.const_obj_map, coefficientTower,
    Functor.ofOpSequence_map_homOfLE_succ]
  ext U x
  exact congrArg (fun f ↦ f.hom.app U x)
    (AdicCompletion.quotient_transition l E X n).symm

/-- The entire section-action and restriction assertion, with no boundedness,
Noetherianity or prime-invertibility assumptions.

Source: blueprint main-20261015, localizing-closure finite-model proof, Locality;
Stacks 09AA, 03EK, 03DB, 014E, 08TC
(blueprint: lem-sfb-strict-completion-restriction-comparison).

Proof plan (the seven steps of the node):
1. Section action is exact and unchanged on sections and scalar matrices. It
   preserves cokernels, cohomology and finite constant local models. The inverse
   equivalence identifies products by their projections.
2. The canonical coefficient isomorphisms are natural in the condensed ring;
   hence they identify the uniformizer, quotient units and quotient transitions.
3. For immersions use proEtale_immersion_inverseImage_preservesLimits. For site
   objects identify inverse image with slice restriction, exact and sectionwise
   product preserving. Compose these facts, including the empty composite.
4. The tensor comparisons on K-flat representatives identify reductions. Their
   normalization sends m tensor 1 to the same tensor, preserving quotient units
   and transitions. Section action has the same local-pure-tensor normalization.
5. In cone coordinates the comparison is (Fx,Fy). Its transition is (Fx,pi Fy)
   and its augmentation is (Fm,0). Substitution in (dx+pi^n y,-dy) proves that
   these are the specified strict reduction comparisons.
6. Product projections give beta F(1-T)=(1-T) beta. On the two Roos coordinates
   use beta diagonally; the augmentation becomes (((Fm,0))_n,0). Both the
   product projections and the zero coordinate are retained in Comparison.
7. Localize these chain isomorphisms using the completion-triangle comparison.
   The representative equation and unit equation identify the specified maps.
   Naturality comes from natural chain maps and localization. For composites,
   product projections and the two cone coordinates give the same comparison.
-/
theorem strict_completion_restriction_comparison :
    ∃ S : ∀ X : Scheme.{u}, Presentation.{u + 2, u + 1, u + 1} (AdicCompletion.Modules l E X),
      (∀ X : Scheme.{u}, IsIntegral l E X (S X)) ∧
      (∀ (X : Scheme.{u}) (M : AdicCompletion.Modules l E X),
        HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) X M ↔
        HasSectionFiniteConstantLocalModel l E X
          ((ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E)
            X).functor.obj M)) ∧
      (∀ X : Scheme.{u},
        ∃ T : Presentation.{u + 2, u + 1, u + 1}
          (ModuleObjectRingedComparison.Modules (DerivedNakayama.integerRing l E) X),
          IsSectionIntegral l E X T ∧
          Nonempty (Comparison.{u + 2, u + 1, u + 2, u + 1, u + 1, u + 1}
            (ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E) X).functor
            (S X) T)) ∧
      (∀ {X Y : Scheme.{u}} (h : X ⟶ Y),
        (MorphismProperty.multiplicativeClosure
          (fun {V W : Scheme.{u}} (f : V ⟶ W) ↦ IsImmersion f ∨ WeaklyEtale f)) h →
        (∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I)
          (CondensedRing.upperStar (DerivedNakayama.integerRing l E) h)) ∧
        Nonempty (Comparison.{u + 2, u + 1, u + 2, u + 1, u + 1, u + 1}
          (CondensedRing.upperStar (DerivedNakayama.integerRing l E) h)
          (S Y) (S X))) := by
  classical
  choose S hS using fun X : Scheme.{u} ↦ strictIntegralCompletionPresentation l E X
  refine ⟨S, hS, strictCompletionFiniteConstantModels l E, ?_, ?_⟩
  · intro X
    obtain ⟨data, hdata, _htower, hs, _hred, _hmaps, _hcompletion⟩ := hS X
    obtain ⟨T, hmap, hscalar⟩ := strictSectionScalarPresentation l E X data.d
    let B := coefficientTower l E X
    let ι := coefficientUnit l E X
    have hB : ∀ n : ℕ, B.obj (op n) =
        sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (AdicCompletion.finiteRing l E X n) := fun _ ↦ rfl
    have hι : ∀ n : ℕ, HEq (ι.app (op n))
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (AdicCompletion.quotient l E X n)) := fun _ ↦ HEq.rfl
    have hstep : ∀ n : ℕ, HEq (B.map (homOfLE (Nat.le_succ n)).op)
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (AdicCompletion.transition l E X n)) := by
      intro n
      dsimp only [B, coefficientTower]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
    obtain ⟨H, HM, t, _θ, _hθ, _hslice⟩ :=
      ModuleObjectRingedComparison.moduleObject_ringedSite_derived_comparison
        (DerivedNakayama.integerRing l E) X
    obtain ⟨hmodels, hcompletion'⟩ := strictSectionPrincipalQuotientModels l E X T data
      hdata hscalar B ι hB hι hstep H HM t
    refine ⟨T, ⟨data, hdata, hscalar, B, ι, hB, hι, hstep,
      ⟨H, HM, ⟨t⟩, hmodels⟩, hcompletion'⟩, ?_⟩
    apply strictScalarCompletionFunctorComparison
      (ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E) X).functor
      (S X) T
    · intro M
      rw [hs]
      exact hmap M
    · intro K
      infer_instance
  · intro X Y f hf
    let : PreservesLimitsOfSize.{u + 1, u + 1}
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f) :=
      strictCompletionRestrictionLimits (DerivedNakayama.integerRing l E) f hf
    let : PreservesLimitsOfSize.{0, 0}
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f) :=
      preservesLimitsOfSize_shrink (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)
    refine ⟨fun I ↦ inferInstance, ?_⟩
    apply strictScalarCompletionFunctorComparison
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f) (S Y) (S X)
    · exact strictIntegralScalarPullback l E f (S Y) (S X) (hS Y) (hS X)
    · intro K
      infer_instance

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
