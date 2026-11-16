import Langlands.GroupScheme.Reductive.AffinePinnedComparisonPullback

/-! # Fppf-local concrete pinning preservation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N K : AffinePinnedModel.{u}} {T U V : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base} {h : T ⟶ K.base}

private theorem locallyPinned_pullAlong_iff (e : Comparison f g) (q : U ⟶ T)
    {f' : U ⟶ M.base} {g' : U ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g') :
    IsLocallyPinned (pullComparisonAlong e q hf hg) ↔
      IsLocallyPinned (pullComparison e q) := by
  subst f'
  subst g'
  rw [pullComparisonAlong_rfl]

/-- Concrete pinning preservation is insensitive to reassociation of a
two-step normalized pullback, through the actual tower comparison. -/
theorem isLocallyPinned_pullComparison_comp_iff (e : Comparison f g)
    (q : U ⟶ T) (r : V ⟶ U) :
    IsLocallyPinned (pullComparison (pullComparison e q) r) ↔
      IsLocallyPinned (pullComparison e (r ≫ q)) := by
  rw [← locallyPinned_pullAlong_iff (pullComparison e q) r
    (Category.assoc r q f).symm (Category.assoc r q g).symm,
    ← pullComparisonAlong_rfl e q, pullComparisonAlong_comp,
    pullComparisonAlong_rfl]

/-- Refining a test map preserves a concrete pinned comparison with the
specified total base map. -/
theorem IsLocallyPinned.pullComparison_of_factorization {e : Comparison f g}
    (q : U ⟶ T) (he : IsLocallyPinned (pullComparison e q))
    (r : V ⟶ U) (p : V ⟶ T) (hp : r ≫ q = p) :
    IsLocallyPinned (pullComparison e p) := by
  subst p
  exact (isLocallyPinned_pullComparison_comp_iff e q r).mp (he.pull r)

/-- The actual comparison becomes concretely pinned on one fppf cover.
No constant root relabelling is chosen on the common scheme. -/
def IsFppfLocallyPinned (e : Comparison f g) : Prop :=
  ∃ (U : Scheme.{u}) (q : U ⟶ T),
    Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      IsLocallyPinned (pullComparison e q)

/-- Concrete pinning preservation gives its fppf-local form. -/
theorem IsLocallyPinned.fppfLocallyPinned {e : Comparison f g}
    (he : IsLocallyPinned e) : IsFppfLocallyPinned e :=
  ⟨T, 𝟙 T, inferInstance, inferInstance, inferInstance, he.pull (𝟙 T)⟩

/-- Fppf-local pinning preservation is stable under every scheme pullback. -/
theorem IsFppfLocallyPinned.pull {e : Comparison f g}
    (he : IsFppfLocallyPinned e) (p : V ⟶ T) :
    IsFppfLocallyPinned (pullComparison e p) := by
  obtain ⟨U, q, hqf, hqs, hql, hq⟩ := he
  let : Flat q := hqf
  let : Surjective q := hqs
  let : LocallyOfFinitePresentation q := hql
  let r : pullback q p ⟶ U := pullback.fst q p
  let s : pullback q p ⟶ V := pullback.snd q p
  refine ⟨pullback q p, s, inferInstance, inferInstance, inferInstance, ?_⟩
  apply (isLocallyPinned_pullComparison_comp_iff e p s).mpr
  exact hq.pullComparison_of_factorization q r (s ≫ p) pullback.condition

/-- One arbitrary fppf cover detects the fppf-local pinning predicate. -/
theorem IsFppfLocallyPinned.of_pull {e : Comparison f g} (q : U ⟶ T)
    [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (he : IsFppfLocallyPinned (pullComparison e q)) : IsFppfLocallyPinned e := by
  obtain ⟨V, r, hrf, hrs, hrl, hr⟩ := he
  let : Flat r := hrf
  let : Surjective r := hrs
  let : LocallyOfFinitePresentation r := hrl
  refine ⟨V, r ≫ q, inferInstance, inferInstance, inferInstance, ?_⟩
  exact (isLocallyPinned_pullComparison_comp_iff e q r).mp hr

/-- Fppf-local pinning predicates compose after the common fppf refinement. -/
theorem IsFppfLocallyPinned.trans {e : Comparison f g} {d : Comparison g h}
    (he : IsFppfLocallyPinned e) (hd : IsFppfLocallyPinned d) :
    IsFppfLocallyPinned (e ≪≫ d) := by
  obtain ⟨U, q, hqf, hqs, hql, hq⟩ := he
  obtain ⟨V, p, hpf, hps, hpl, hp⟩ := hd
  let : Flat q := hqf
  let : Surjective q := hqs
  let : LocallyOfFinitePresentation q := hql
  let : Flat p := hpf
  let : Surjective p := hps
  let : LocallyOfFinitePresentation p := hpl
  let r : pullback q p ⟶ U := pullback.fst q p
  let s : pullback q p ⟶ V := pullback.snd q p
  refine ⟨pullback q p, r ≫ q, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [pullComparison_trans]
  exact (hq.pullComparison_of_factorization q r (r ≫ q) rfl).trans
    (hp.pullComparison_of_factorization p s (r ≫ q) pullback.condition.symm)

@[simp]
theorem isFppfLocallyPinned_refl (M : AffinePinnedModel.{u}) (f : T ⟶ M.base) :
    IsFppfLocallyPinned (Iso.refl (M.groupOver f)) :=
  (isLocallyPinned_refl M f).fppfLocallyPinned

/-- Both geometric clauses are global consequences of fppf-local pinning. -/
theorem IsFppfLocallyPinned.geometry {e : Comparison f g}
    (he : IsFppfLocallyPinned e) : PreservesTorus e ∧ PreservesCocharacter e := by
  obtain ⟨U, q, hqf, hqs, hql, hq⟩ := he
  let : Flat q := hqf
  let : Surjective q := hqs
  let : LocallyOfFinitePresentation q := hql
  exact ⟨PreservesTorus.of_pull q hq.1, PreservesCocharacter.of_pull q hq.2.1⟩

end Langlands.GroupScheme.AffinePinnedModel
