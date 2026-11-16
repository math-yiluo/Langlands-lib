import Langlands.GroupScheme.Reductive.AffinePinnedAtlasInner

/-! # Actual adjoint points inducing corrected atlas transitions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Descent

/-- Direct pullback respects inverse actual isomorphisms. -/
theorem pullIso_symm {S T W : Scheme.{u}} (q : W ⟶ T)
    {f g : T ⟶ S} {r s : W ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s) {G H : GroupScheme S}
    (e : (baseChange f).obj G ≅ (baseChange g).obj H) :
    pullIso q hg hf e.symm = (pullIso q hf hg e).symm := by
  apply Iso.ext
  simp [pullIso]

end Descent

namespace AffinePinnedChart

open Descent

/-- A chart's inverse transition is induced by a point of the original relative quotient. -/
theorem exists_relativePointIso_transition_symm {S T : Scheme.{u}}
    {G Q : GroupScheme S} (P : RelativePinnedComparison.{u})
    (C D : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hg : g ≫ D.map = k)
    (p : G ⟶ Q) (hp : RelativeRoot.IsFppfQuotient (center G) p)
    (c : AutomorphicAction Q G)
    (hc : c.restrict p = AutomorphicAction.conjugation (𝟙 G)) :
    ∃ x : Over.mk k ⟶ Q.X,
      (C.transition P D f g k hf hg).symm = c.relativePointIso x := by
  have hc' : (c.baseChange k).restrict ((baseChange k).map p) =
      AutomorphicAction.conjugation (𝟙 ((baseChange k).obj G)) := by
    rw [← AutomorphicAction.baseChange_restrict, hc,
      AutomorphicAction.baseChange_conjugation, CategoryTheory.Functor.map_id]
  obtain ⟨x, hx⟩ := C.exists_basePointIso_transition_symm P D f g k hf hg
    ((baseChange k).obj Q) ((baseChange k).map p) (hp.baseChange_center k)
    (c.baseChange k) hc'
  refine ⟨LocalGroupIso.coverPointsEquiv Q (𝟙 (Over.mk k)) x, ?_⟩
  simpa only [AutomorphicAction.relativePointIso, Over.mk_hom, MulEquiv.symm_apply_apply] using hx.symm

end AffinePinnedChart

namespace AffinePinnedAtlas

open Descent CoproductComponents

variable {S T : Scheme.{u}} {G Q : GroupScheme S}
    (A : AffinePinnedAtlas G) (P : RelativePinnedComparison.{u})
    (p : G ⟶ Q) (hp : RelativeRoot.IsFppfQuotient (center G) p)
    (c : AutomorphicAction Q G)
    (hc : c.restrict p = AutomorphicAction.conjugation (𝟙 G))

include p hp hc

/-- Disjoint target components assemble actual points inducing chart-to-atlas transitions. -/
theorem exists_relativePointIso_chartToAtlas_symm
    (C : AffinePinnedChart G) (f : T ⟶ C.model.base)
    (b : T ⟶ A.space) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hb : b ≫ A.projection = k) :
    ∃ x : Over.mk k ⟶ Q.X,
      (A.chartToAtlas P C f b k hf hb).symm = c.relativePointIso x := by
  apply DisjointComponents.exists_relativePointIso (toBase b) k c
  intro i
  rw [pullIso_symm, A.chartToAtlas_on_chart P C f b k hf hb i
    (toBase b i) (toComponent b i) (component_condition b i) _ rfl]
  exact C.exists_relativePointIso_transition_symm P (A.chart i) _ _ _ _ _ p hp c hc

/-- Both arbitrary atlas coordinates admit an actual point inducing the inverse transition. -/
theorem exists_relativePointIso_transition_symm
    (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k) :
    ∃ x : Over.mk k ⟶ Q.X,
      (A.transition P a b k ha hb).symm = c.relativePointIso x := by
  apply DisjointComponents.exists_relativePointIso (toBase a) k c
  intro i
  rw [pullIso_symm, transition,
    DisjointComponents.pullIso_pullbackIsoAlong (toBase a) (fun _ => rfl) (fun _ => rfl)]
  exact A.exists_relativePointIso_chartToAtlas_symm P p hp c hc _ _ _ _ _ _

/-- An actual chosen adjoint point inducing each inverse corrected atlas transition. -/
def transitionInnerPoint (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k) :
    Over.mk k ⟶ Q.X :=
  Classical.choose (A.exists_relativePointIso_transition_symm P p hp c hc a b k ha hb)

/-- The chosen point induces the entire actual transition automorphism. -/
theorem transitionInnerPoint_spec (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k) :
    (A.transition P a b k ha hb).symm =
      c.relativePointIso (A.transitionInnerPoint P p hp c hc a b k ha hb) :=
  Classical.choose_spec (A.exists_relativePointIso_transition_symm P p hp c hc a b k ha hb)

end AffinePinnedAtlas

end Langlands.GroupScheme
