import Langlands.GroupScheme.Reductive.AffinePinnedIndependence

/-! # Reduction of coherent pinned comparisons to local existence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace AffinePinnedModel

/-- Every actual comparison has a pinned representative of its inner class
on some fppf cover. Existence is the only assertion in this predicate. -/
def HasFppfLocalPinnedRepresentatives : Prop :=
  ∀ (M N : AffinePinnedModel.{u}) (T : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g),
    ∃ (V : Scheme.{u}) (p : V ⟶ T),
      Flat p ∧ Surjective p ∧ LocallyOfFinitePresentation p ∧
      ∃ d : Comparison (p ≫ f) (p ≫ g),
        IsFppfLocallyPinned d ∧ IsFppfInnerEquivalent (pullComparison e p) d

/-- The normalization predicate is the existing concrete fppf-local pinning
condition on actual comparisons. -/
abbrev fppfLocalPinningPredicate : ComparisonPredicate.{u} :=
  fun _ _ {_} _ _ e => IsFppfLocallyPinned e

/-- Actual fppf-local pinning is stable under pullback and detected by an
fppf cover. -/
theorem fppfLocalPinningPredicate_isLocal :
    IsFppfLocalComparisonPredicate fppfLocalPinningPredicate.{u} := by
  constructor
  · intro M N T W f g e q he
    exact he.pull q
  · intro M N T V f g e p hf hs hl he
    let : Flat p := hf
    let : Surjective p := hs
    let : LocallyOfFinitePresentation p := hl
    exact IsFppfLocallyPinned.of_pull p he

/-- Local existence, proved rigidity, and all-test independence give the
complete input to the existing comparison descent theorem. -/
theorem hasFppfLocalNormalizedComparisons_of_localPinnedRepresentatives
    (h : HasFppfLocalPinnedRepresentatives.{u}) :
    HasFppfLocalNormalizedComparisons fppfLocalPinningPredicate.{u} := by
  intro M N T f g e
  obtain ⟨V, p, hf, hs, hl, d, hd, hi⟩ := h M N T f g e
  refine ⟨V, p, hf, hs, hl, d, hd, hi,
    comparisonLocalIso_isIndependent e p d hd hi, ?_⟩
  intro k hk hik
  exact eq_of_fppfLocallyPinned_innerEquivalent hk hd (hik.symm.trans hi)

/-- Local pinned representatives descend to unique global representatives. -/
theorem hasUniquePinnedComparisons_of_localPinnedRepresentatives
    (h : HasFppfLocalPinnedRepresentatives.{u}) :
    HasUniqueNormalizedComparisons fppfLocalPinningPredicate.{u} :=
  hasUniqueNormalizedComparisons_of_fppf fppfLocalPinningPredicate_isLocal
    (hasFppfLocalNormalizedComparisons_of_localPinnedRepresentatives h)

/-- The actual pinning predicate, with its proved geometry and closure laws,
constructs all normalization data once local existence is supplied. -/
def normalizationOfLocalPinnedRepresentatives
    (h : HasFppfLocalPinnedRepresentatives.{u}) : RelativePinnedNormalization.{u} where
  normalized := fppfLocalPinningPredicate
  unique := hasUniquePinnedComparisons_of_localPinnedRepresentatives h
  refl M _ f := isFppfLocallyPinned_refl M f
  trans _ _ _ _ _ _ _ _ _ he hd := he.trans hd
  pull _ _ _ _ _ _ _ q he := he.pull q
  torus _ _ _ _ _ _ he := he.geometry.1
  cocharacter _ _ _ _ _ _ he := he.geometry.2

end AffinePinnedModel

/-- The unchanged coherent-comparison target follows from local existence
alone; uniqueness, descent, geometry and coherence have been proved. -/
theorem relativePinnedComparisonExistence_of_localPinnedRepresentatives
    (h : AffinePinnedModel.HasFppfLocalPinnedRepresentatives.{u}) :
    RelativePinnedComparisonExistenceStatement.{u} :=
  relativePinnedComparisonExistence_of_normalization
    (AffinePinnedModel.normalizationOfLocalPinnedRepresentatives h)

end Langlands.GroupScheme
