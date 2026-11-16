import Langlands.GroupScheme.Reductive.RelativePinnedNormalization
import Langlands.GroupScheme.Reductive.AffinePinnedComparisonDescent
import Langlands.GroupScheme.AutomorphicAction.LocallyInnerReflection

/-! # Descent criterion for unique normalized comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T V : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- Direct comparison pullback along an fppf cover reflects inner equivalence. -/
theorem innerEquivalent_of_pullComparison (p : V ⟶ T)
    [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
    {e d : Comparison f g}
    (h : IsFppfInnerEquivalent (pullComparison e p) (pullComparison d p)) :
    IsFppfInnerEquivalent e d := by
  have hi :
      IsFppfInnerEquivalent (comparisonToIterated p (pullComparison e p))
        (comparisonToIterated p (pullComparison d p)) :=
    (h.postcomp (baseChangeCompIso g p N.group)).precomp
      (baseChangeCompIso f p M.group).symm
  apply IsFppfInnerEquivalent.of_baseChange p
  simpa only [comparisonToIterated_pullComparison] using hi

/-- Inner equivalence is local for the actual normalized comparison pullback. -/
theorem innerEquivalent_pullComparison_iff (p : V ⟶ T)
    [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
    {e d : Comparison f g} :
    IsFppfInnerEquivalent (pullComparison e p) (pullComparison d p) ↔
      IsFppfInnerEquivalent e d :=
  ⟨innerEquivalent_of_pullComparison p, fun h => innerEquivalent_pullComparison h p⟩

/-- A comparison predicate is stable under arbitrary pullback and reflects
along an fppf cover. This is a property of the supplied predicate. -/
def IsFppfLocalComparisonPredicate (P : ComparisonPredicate.{u}) : Prop :=
  (∀ (M N : AffinePinnedModel.{u}) (T W : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g) (q : W ⟶ T),
    P M N f g e → P M N (q ≫ f) (q ≫ g) (pullComparison e q)) ∧
  (∀ (M N : AffinePinnedModel.{u}) (T V : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g) (p : V ⟶ T),
    Flat p → Surjective p → LocallyOfFinitePresentation p →
    P M N (p ≫ f) (p ≫ g) (pullComparison e p) → P M N f g e)

/-- Every comparison has, on some fppf cover, a unique normalized
representative of its local-inner class whose all-test family is independent.
Neither the cover nor the representative is supplied by this definition. -/
def HasFppfLocalNormalizedComparisons (P : ComparisonPredicate.{u}) : Prop :=
  ∀ (M N : AffinePinnedModel.{u}) (T : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g),
    ∃ (V : Scheme.{u}) (p : V ⟶ T),
      Flat p ∧ Surjective p ∧ LocallyOfFinitePresentation p ∧
      ∃ d : Comparison (p ≫ f) (p ≫ g),
        P M N (p ≫ f) (p ≫ g) d ∧
        IsFppfInnerEquivalent (pullComparison e p) d ∧
        (comparisonLocalIso p d).IsIndependent ∧
        ∀ k : Comparison (p ≫ f) (p ≫ g),
          P M N (p ≫ f) (p ≫ g) k →
          IsFppfInnerEquivalent (pullComparison e p) k → k = d

/-- Independent local representatives glue; local predicate and class
reflection give a global representative, and local uniqueness gives uniqueness. -/
theorem hasUniqueNormalizedComparisons_of_fppf
    {P : ComparisonPredicate.{u}} (hP : IsFppfLocalComparisonPredicate P)
    (hlocal : HasFppfLocalNormalizedComparisons P) :
    HasUniqueNormalizedComparisons P := by
  intro M N T f g e
  obtain ⟨V, p, hf, hs, hl, d, hdP, hdinner, hdind, hdunique⟩ :=
    hlocal M N T f g e
  let : Flat p := hf
  let : Surjective p := hs
  let : LocallyOfFinitePresentation p := hl
  let k : Comparison f g := descendComparison p d hdind
  have hk : pullComparison k p = d := pullComparison_descendComparison p d hdind
  have hkP : P M N f g k := hP.2 M N T V f g k p hf hs hl (hk.symm ▸ hdP)
  have hkinner : IsFppfInnerEquivalent e k :=
    innerEquivalent_of_pullComparison p (hk.symm ▸ hdinner)
  refine ⟨k, ⟨hkP, hkinner⟩, ?_⟩
  intro k' hk'
  apply pullComparison_injective p
  exact (hdunique (pullComparison k' p)
    (hP.1 M N T V f g k' p hk'.1)
    (innerEquivalent_pullComparison hk'.2 p)).trans hk.symm

end Langlands.GroupScheme.AffinePinnedModel
