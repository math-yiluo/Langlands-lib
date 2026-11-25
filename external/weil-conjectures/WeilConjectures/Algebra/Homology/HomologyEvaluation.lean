/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import WeilConjectures.Algebra.Homology.HomologyEvaluationCycleExistence
import WeilConjectures.Algebra.Homology.HomologyEvaluationUniqueness
import WeilConjectures.Algebra.Homology.HomologyEvaluationLocalIso

/-! # Homology evaluation and locally split finite free complexes

Source: Stacks Project, Tags 0A8X, 08DH and 0BQY.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- The uniquely characterized homology evaluation is perfect wherever the first complex
has a finite free zero-differential model and the second is a K-injective resolution
of a degree-zero module. No closed immersion or Koszul regularity enters this lemma.

Source: Stacks Project, sites-cohomology.tex, section-hom-complexes (0A8X);
cohomology.tex, section-internal-hom (08DH); duality.tex,
lemma-regular-ideal-ext (0BQY), zero-differential Hom calculation.
(blueprint: lem-sc-homology-evaluation-formal-complex).

Proof: Evaluate a degree-n Hom cocycle on a degree-minus-n cycle using the displayed
product projection. The Hom differential equation says the result is a degree-zero
cycle of J. Replacing the Hom cocycle by a boundary changes this value by a boundary
of J; replacing the T cycle by a boundary does the same. The bilinear evaluation
therefore descends through both homology cokernels. Curry it using the internal
Hom adjunction. Local lifts of classes to cycles exist because the homology class
maps are sheaf epimorphisms. This proves the displayed formula and also uniqueness:
check a map into internal Hom after evaluating on such lifts on a covering, then use
separatedness. The formula commutes with open restriction, which preserves cycles,
boundaries, homology and internal Hom. On the specified open site replace T by E
through the two quasi-isomorphisms in its roof. K-injectivity of the restricted J
makes both induced Hom-complex maps quasi-isomorphisms; evaluation commutes with
these maps. For E the Hom complex is a finite product of shifts of Hom(E^p,J).
Each E^p is finite free, so Hom(E^p,-) is exact. Only the p=-n summand contributes
to degree-n homology because J has no other cohomology. Its contribution is exactly
Hom(E^(-n),H^0(J)), and evaluation is the identity under this identification.
Thus evaluation is an isomorphism for E and hence for T. Rank zero, empty opens,
zero coefficient rings, and degrees outside the finite support give the same
calculation with zero objects. No chosen map or arbitrary existence witness
appears in the characterization of evaluation. -/
theorem exists_homologyEvaluation (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k)) :
    ∃! e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0),
      IsHomologyEvaluation X T J n e ∧
        ∀ (V : X.Opens) (W : V.toScheme.Opens),
          let Fc := moduleOpenOverComplexFunctor X V W
          CochainComplex.IsKInjective (Fc.obj J) →
          HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W) (Fc.obj T) →
          IsIso (((Scheme.Modules.restrictFunctor V.ι).map e).over W) := by
  obtain ⟨e, he⟩ := exists_homologyEvaluation_cycle X T J n
  refine ⟨e, ⟨he, ?_⟩, ?_⟩
  · intro V W
    dsimp only
    intro hI hT
    exact homologyEvaluation_local_iso_of_cycle X T J n hJ e he V W hI hT
  · intro e' h'
    exact (homologyEvaluation_unique_of_cycle X T J n e e' he h'.1).symm

/-- Homology evaluation, specified uniquely by cycle evaluation and its local calculation.
Source: Stacks Project, Tags 0A8X and 08DH.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
noncomputable def homologyEvaluation (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k)) :
    (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0) :=
  (exists_homologyEvaluation X T J n hJ).exists.choose

/-- The local perfection assertion for the uniquely specified evaluation map.
Source: Stacks Project, Tags 0A8X, 08DH and 0BQY.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
theorem homologyEvaluation_isIso (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
    (V : X.Opens) (W : V.toScheme.Opens)
    (hI : CochainComplex.IsKInjective ((moduleOpenOverComplexFunctor X V W).obj J))
    (hT : HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W)
      ((moduleOpenOverComplexFunctor X V W).obj T)) :
    IsIso (((Scheme.Modules.restrictFunctor V.ι).map
      (homologyEvaluation X T J n hJ)).over W) :=
  (exists_homologyEvaluation X T J n hJ).exists.choose_spec.2 V W hI hT

end CategoryTheory
