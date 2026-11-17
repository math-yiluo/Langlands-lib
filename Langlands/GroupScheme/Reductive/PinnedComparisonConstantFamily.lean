import Langlands.GroupScheme.Reductive.PinnedComparisonLabels
import Langlands.GroupScheme.Reductive.OuterIsomorphismPinnedNormalization
import Langlands.GroupScheme.Reductive.RelativePinnedExistenceReduction
import Langlands.GroupScheme.LocalGroupIsoCoproductClassification
import Langlands.GroupScheme.LocalGroupIsoNormalization

/-! # The actual constant family of pinned comparison representatives -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}}

namespace ComparisonLabel

variable (d : ComparisonLabel M N)
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    {S : Scheme.{u}} (f : S ⟶ M.base) (g : S ⟶ N.base)

/-- The canonical representative as an all-test family over a relative test. -/
def localFamily (T : Over S) : LocalGroupIso (M.groupOver f) (N.groupOver g) T :=
  LocalGroupIso.ofBaseChangeIso
    (comparisonToIterated T.hom (d.representative hAffine (T.hom ≫ f) (T.hom ≫ g)))

/-- Canonical comparison representatives respect explicitly identified base maps. -/
theorem representative_pullAlong {T W : Scheme.{u}} (f : T ⟶ M.base)
    (g : T ⟶ N.base) (r : W ⟶ T) {f' : W ⟶ M.base} {g' : W ⟶ N.base}
    (hf : r ≫ f = f') (hg : r ≫ g = g') :
    pullComparisonAlong (d.representative hAffine f g) r hf hg =
      d.representative hAffine f' g' := by
  subst f'
  subst g'
  simpa only [pullComparisonAlong_rfl] using d.representative_pull hAffine f g r

/-- The canonical representative family respects every relative refinement. -/
theorem localFamily_refine {T W : Over S} (r : W ⟶ T) :
    (d.localFamily hAffine f g T).refine r = d.localFamily hAffine f g W := by
  unfold localFamily
  rw [LocalGroupIso.ofBaseChangeIso_refine]
  congr 1
  rw [← comparisonToIterated_pullAlong T.hom r.left W.hom (Over.w r)]
  rw [d.representative_pullAlong]

/-- The full root-datum label is detected by equality of families on any nonempty test. -/
theorem eq_of_localFamily_eq (c : ComparisonLabel M N) (T : Over S) (x : T.left)
    (h : d.localFamily hAffine f g T = c.localFamily hAffine f g T) : d = c := by
  have h' := congrArg LocalGroupIso.toBaseChangeIso h
  simp only [localFamily, LocalGroupIso.toBaseChangeIso_ofBaseChangeIso] at h'
  exact d.eq_of_representative_eq c hAffine (T.hom ≫ f) (T.hom ≫ g) x
    (comparisonToIterated_injective T.hom h')

end ComparisonLabel

variable (M N : AffinePinnedModel.{u})
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    {S : Scheme.{u}} (f : S ⟶ M.base) (g : S ⟶ N.base)

/-- The actual all-test family on the coproduct of full lattice labels. -/
def constantPinnedFamily : LocalGroupIso (M.groupOver f) (N.groupOver g)
    (GroupIsomorphismScheme.constantParameter S (ComparisonLabel M N)) :=
  LocalGroupIso.constantFamily (fun d : ComparisonLabel M N =>
    d.localFamily hAffine f g (Over.mk (𝟙 S)))

/-- Distinct full lattice labels remain disjoint after arbitrary common-base change. -/
theorem constantPinnedFamily_refine_injective (T : Over S) :
    Function.Injective (fun b : T ⟶ GroupIsomorphismScheme.constantParameter S
      (ComparisonLabel M N) => (constantPinnedFamily M N hAffine f g).refine b) := by
  apply LocalGroupIso.constantFamily_refine_injective
  intro d c W h
  rw [d.localFamily_refine, c.localFamily_refine] at h
  by_cases hW : Nonempty W.left
  · exact Or.inl (d.eq_of_localFamily_eq hAffine f g c W hW.some h)
  · exact Or.inr (not_nonempty_iff.mp hW)

/-- A comparison satisfying the normalization predicate is fixed by normalization. -/
theorem localNormalize_eq_of_normalized (n : RelativePinnedNormalization.{u})
    (T : Over S) (E : LocalGroupIso (M.groupOver f) (N.groupOver g) T)
    (hE : n.normalized M N (T.hom ≫ f) (T.hom ≫ g)
      (comparisonFromIterated T.hom E.toBaseChangeIso)) :
    (n.actualNormalization M N f g).localNormalize T E = E := by
  apply LocalGroupIso.baseChangeIsoEquiv.symm.injective
  change ((n.actualNormalization M N f g).localNormalize T E).toBaseChangeIso =
    E.toBaseChangeIso
  rw [GroupIsomorphismScheme.ActualNormalization.localNormalize_toBaseChangeIso]
  change comparisonToIterated T.hom
    (n.correction M N (T.hom ≫ f) (T.hom ≫ g)
      (comparisonFromIterated T.hom E.toBaseChangeIso)) = E.toBaseChangeIso
  rw [← n.correction_unique M N (T.hom ≫ f) (T.hom ≫ g)
    (comparisonFromIterated T.hom E.toBaseChangeIso)
    (comparisonFromIterated T.hom E.toBaseChangeIso) hE (IsFppfInnerEquivalent.refl _)]
  exact comparisonToIterated_fromIterated T.hom E.toBaseChangeIso

/-- Fixedness of the labelled representatives holds even when the test's label
varies locally, because it can be checked on the component pullback cover. -/
theorem constantPinnedFamily_normalized (n : RelativePinnedNormalization.{u})
    (hn : ∀ (d : ComparisonLabel M N) (T : Over S),
      n.normalized M N (T.hom ≫ f) (T.hom ≫ g)
        (d.representative hAffine (T.hom ≫ f) (T.hom ≫ g)))
    (T : Over S) (b : T ⟶ GroupIsomorphismScheme.constantParameter S
      (ComparisonLabel M N)) :
    (n.actualNormalization M N f g).localNormalize T
        ((constantPinnedFamily M N hAffine f g).refine b) =
      (constantPinnedFamily M N hAffine f g).refine b := by
  let V := fun _ : ComparisonLabel M N => Over.mk (𝟙 S)
  let E := constantPinnedFamily M N hAffine f g
  apply LocalGroupIso.eq_of_refine_cover (Scheme.zariskiTopology.over S)
    (fun d => pullback b (Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart.sigmaOverι V d))
    (fun d => pullback.fst b (Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart.sigmaOverι V d))
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart.pullbackOpenCover V b).mem_grothendieckTopology
  · intro d
    let i := Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart.sigmaOverι V d
    let W := pullback b i
    let p : W ⟶ T := pullback.fst b i
    have he : (E.refine b).refine p = d.localFamily hAffine f g W := by
      rw [LocalGroupIso.refine_comp, pullback.condition, ← LocalGroupIso.refine_comp]
      change ((LocalGroupIso.coproduct V (fun c : ComparisonLabel M N =>
        c.localFamily hAffine f g (Over.mk (𝟙 S)))).refine i).refine
          (pullback.snd b i) = _
      rw [LocalGroupIso.coproduct_refine_ι]
      exact d.localFamily_refine hAffine f g (pullback.snd b i)
    change ((n.actualNormalization M N f g).localNormalize T (E.refine b)).refine p =
      (E.refine b).refine p
    rw [← GroupIsomorphismScheme.ActualNormalization.localNormalize_refine, he]
    apply localNormalize_eq_of_normalized M N f g n W
    simpa only [ComparisonLabel.localFamily, LocalGroupIso.toBaseChangeIso_ofBaseChangeIso,
      comparisonFromIterated_toIterated] using hn d W

end Langlands.GroupScheme.AffinePinnedModel
