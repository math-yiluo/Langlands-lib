import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Evaluating single-degree comparisons through exact derived functors -/

noncomputable section

universe wB wT

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

variable {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory.{wB} B]
variable {T : Type*} [Category* T] [Abelian T] [HasDerivedCategory.{wT} T]
variable (E : B ⥤ T) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- Evaluate a given single-degree comparison using the canonical comparison
between the exact derived functor and singleFunctor. -/
def exactDerivedEvaluationSingleIso {K : DerivedCategory B} {X : B} (q : ℤ)
    (s : K ≅ (DerivedCategory.singleFunctor B q).obj X) :
    E.mapDerivedCategory.obj K ≅
      (DerivedCategory.singleFunctor T q).obj (E.obj X) :=
  E.mapDerivedCategory.mapIso s ≪≫ (E.mapDerivedCategorySingleFunctor q).app X

/-- An exact derived functor preserves a proved single-degree recovery,
with the canonical endpoint comparisons included. -/
@[reassoc] theorem exactDerivedEvaluation_single
    {K L : DerivedCategory B} {X Y : B} (q : ℤ)
    (s : K ≅ (DerivedCategory.singleFunctor B q).obj X)
    (t : L ≅ (DerivedCategory.singleFunctor B q).obj Y)
    (g : K ⟶ L) (h : X ⟶ Y)
    (hg : s.inv ≫ g ≫ t.hom = (DerivedCategory.singleFunctor B q).map h) :
    (exactDerivedEvaluationSingleIso E q s).inv ≫
        E.mapDerivedCategory.map g ≫
        (exactDerivedEvaluationSingleIso E q t).hom =
      (DerivedCategory.singleFunctor T q).map (E.map h) := by
  simp only [exactDerivedEvaluationSingleIso, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hg]
  have hn := (E.mapDerivedCategorySingleFunctor q).hom.naturality h
  simpa using congrArg
    (fun f => (E.mapDerivedCategorySingleFunctor q).inv.app X ≫ f) hn

end Langlands.Cohomology
