import Langlands.GroupScheme.AutomorphicAction.LocallyInnerTransport
import Langlands.GroupScheme.Reductive.RelativePinnedComparisonStatement

/-! # Assembling coherent comparisons from unique normalized representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Inner-equivalent comparisons have a unique discrepancy section for every
supplied full-centre quotient and compatible action. -/
theorem IsFppfInnerEquivalent.existsUnique_adjointPoint
    {S : Scheme.{u}} {G H A : GroupScheme S} {e d : G ≅ H}
    (h : IsFppfInnerEquivalent e d) (p : G ⟶ A)
    (hp : RelativeRoot.IsFppfQuotient (center G) p) (a : AutomorphicAction A G)
    (ha : a.restrict p = AutomorphicAction.conjugation (𝟙 G)) :
    ∃! x : Over.mk (𝟙 S) ⟶ A.X, a.basePointIso x = e ≪≫ d.symm := by
  exact IsFppfLocallyInner.existsUnique_adjointPoint h p hp a ha

namespace AffinePinnedModel

set_option maxHeartbeats 800000 in
/-- Direct normalized pullback comparisons preserve the local-inner class. -/
theorem innerEquivalent_pullComparison
    {M N : AffinePinnedModel.{u}} {T W : Scheme.{u}}
    {f : T ⟶ M.base} {g : T ⟶ N.base} {e d : Comparison f g}
    (h : IsFppfInnerEquivalent e d) (q : W ⟶ T) :
    IsFppfInnerEquivalent (pullComparison e q) (pullComparison d q) := by
  have hb :
      IsFppfInnerEquivalent ((GroupScheme.baseChange q).mapIso e)
        ((GroupScheme.baseChange q).mapIso d) := h.baseChange q
  have hp := hb.postcomp (baseChangeCompIso g q N.group).symm
  exact hp.precomp (baseChangeCompIso f q M.group)

/-- A family of predicates on comparisons between any two supplied models. -/
abbrev ComparisonPredicate :=
  ∀ (M N : AffinePinnedModel.{u}) {T : Scheme.{u}}
    (f : T ⟶ M.base) (g : T ⟶ N.base), Comparison f g → Prop

/-- Every local-inner class has exactly one representative satisfying `P`. -/
def HasUniqueNormalizedComparisons (P : ComparisonPredicate.{u}) : Prop :=
  ∀ (M N : AffinePinnedModel.{u}) {T : Scheme.{u}}
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g),
    ∃! d : Comparison f g, P M N f g d ∧ IsFppfInnerEquivalent e d

end AffinePinnedModel

open AffinePinnedModel

/-- Sufficient normalization data. Existence of these data is not asserted:
the predicate must provide actual unique representatives, geometric
preservation, and stability under composition and arbitrary pullback. -/
structure RelativePinnedNormalization where
  normalized : ComparisonPredicate.{u}
  unique : HasUniqueNormalizedComparisons normalized
  refl : ∀ (M : AffinePinnedModel.{u}) (T : Scheme.{u}) (f : T ⟶ M.base),
    normalized M M f f (Iso.refl (M.groupOver f))
  trans : ∀ (M N K : AffinePinnedModel.{u}) (T : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (h : T ⟶ K.base)
    (e : Comparison f g) (d : Comparison g h),
    normalized M N f g e → normalized N K g h d →
      normalized M K f h (e ≪≫ d)
  pull : ∀ (M N : AffinePinnedModel.{u}) (T W : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g) (q : W ⟶ T),
    normalized M N f g e →
      normalized M N (q ≫ f) (q ≫ g) (pullComparison e q)
  torus : ∀ (M N : AffinePinnedModel.{u}) (T : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g),
    normalized M N f g e →
      ∃ τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates,
        M.inclusionOver f ≫ e.hom = τ.hom ≫ N.inclusionOver g
  cocharacter : ∀ (M N : AffinePinnedModel.{u}) (T : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g),
    normalized M N f g e →
      M.cocharacterOver f ≫ e.hom = N.cocharacterOver g

namespace RelativePinnedNormalization

variable (n : RelativePinnedNormalization.{u})

/-- Choose the unique normalized representative in the supplied class. -/
def correction (M N : AffinePinnedModel.{u}) {T : Scheme.{u}}
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g) : Comparison f g :=
  (n.unique M N f g e).exists.choose

/-- The chosen correction satisfies the predicate and has the original class. -/
theorem correction_spec (M N : AffinePinnedModel.{u}) {T : Scheme.{u}}
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g) :
    n.normalized M N f g (n.correction M N f g e) ∧
      IsFppfInnerEquivalent e (n.correction M N f g e) :=
  (n.unique M N f g e).exists.choose_spec

/-- Any normalized representative of this class equals the chosen correction. -/
theorem correction_unique (M N : AffinePinnedModel.{u}) {T : Scheme.{u}}
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e d : Comparison f g)
    (hd : n.normalized M N f g d) (he : IsFppfInnerEquivalent e d) :
    d = n.correction M N f g e :=
  (n.unique M N f g e).unique ⟨hd, he⟩ (n.correction_spec M N f g e)

/-- The chosen correction depends only on the local-inner class. -/
theorem correction_eq_of_innerEquivalent (M N : AffinePinnedModel.{u})
    {T : Scheme.{u}} (f : T ⟶ M.base) (g : T ⟶ N.base)
    {e d : Comparison f g} (h : IsFppfInnerEquivalent e d) :
    n.correction M N f g e = n.correction M N f g d :=
  (n.correction_unique M N f g e (n.correction M N f g d)
    (n.correction_spec M N f g d).1 (h.trans (n.correction_spec M N f g d).2)).symm

/-- Uniqueness supplies all coherence laws, and local innerness supplies every
required full-centre adjoint section. -/
def toRelativePinnedComparison : RelativePinnedComparison.{u} where
  compare := fun M N {T} f g e => n.correction M N f g e
  compare_refl M T f := by
    exact (n.correction_unique M M f f (Iso.refl (M.groupOver f))
      (Iso.refl (M.groupOver f)) (n.refl M T f)
      (IsFppfInnerEquivalent.refl _)).symm
  compare_trans M N K T f g h e d := by
    exact (n.correction_unique M K f h (e ≪≫ d)
      (n.correction M N f g e ≪≫ n.correction N K g h d)
      (n.trans M N K T f g h _ _
        (n.correction_spec M N f g e).1 (n.correction_spec N K g h d).1)
      ((n.correction_spec M N f g e).2.comp
        (n.correction_spec N K g h d).2)).symm
  compare_pull M N T W f g e q := by
    exact (n.correction_unique M N (q ≫ f) (q ≫ g) (pullComparison e q)
      (pullComparison (n.correction M N f g e) q)
      (n.pull M N T W f g _ q (n.correction_spec M N f g e).1)
      (innerEquivalent_pullComparison (n.correction_spec M N f g e).2 q)).symm
  torus M N T f g e :=
    n.torus M N T f g _ (n.correction_spec M N f g e).1
  cocharacter M N T f g e :=
    n.cocharacter M N T f g _ (n.correction_spec M N f g e).1
  inner M N T f g e A p hp a ha :=
    ((n.correction_spec M N f g e).2.existsUnique_adjointPoint p hp a ha).exists

end RelativePinnedNormalization

/-- Conditional assembly of the unchanged target; constructing the supplied
normalization data is the remaining mathematical input. -/
theorem relativePinnedComparisonExistence_of_normalization
    (n : RelativePinnedNormalization.{u}) : RelativePinnedComparisonExistenceStatement.{u} :=
  ⟨n.toRelativePinnedComparison⟩

end Langlands.GroupScheme
