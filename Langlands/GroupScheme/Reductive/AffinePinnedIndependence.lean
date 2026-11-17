import Langlands.GroupScheme.Reductive.AffinePinnedInnerUniqueness

/-! # Independence of pinned comparisons in a fixed inner class -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T V U : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- Direct pullback sections and original relative test points are the same
actual points, with the prescribed composite base map. -/
def testPointsEquiv (f : T ⟶ M.base) (W : Over T) :
    (Over.mk (𝟙 W.left) ⟶ (M.groupOver (W.hom ≫ f)).X) ≃*
      (W ⟶ (M.groupOver f).X) :=
  (baseChangeBasePointsEquiv (W.hom ≫ f) M.group).trans
    (baseChangePointsEquiv f M.group W).symm

theorem testPointsEquiv_fst (f : T ⟶ M.base) (W : Over T)
    (x : Over.mk (𝟙 W.left) ⟶ (M.groupOver (W.hom ≫ f)).X) :
    (testPointsEquiv f W x).left ≫ pullback.fst M.group.X.hom f =
      x.left ≫ pullback.fst M.group.X.hom (W.hom ≫ f) := by
  have h := (baseChangePointsEquiv f M.group W).apply_symm_apply
    (baseChangeBasePointsEquiv (W.hom ≫ f) M.group x)
  have h' := congrArg (fun k => k.left) h
  change (testPointsEquiv f W x).left ≫ pullback.fst M.group.X.hom f =
    x.left ≫ pullback.fst M.group.X.hom (W.hom ≫ f) at h'
  exact h'

/-- Fppf-local pinning is preserved by pullback to specified equal endpoints. -/
theorem IsFppfLocallyPinned.pullAlong {e : Comparison f g}
    (he : IsFppfLocallyPinned e) (q : U ⟶ T)
    {f' : U ⟶ M.base} {g' : U ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g') :
    IsFppfLocallyPinned (pullComparisonAlong e q hf hg) := by
  subst f'
  subst g'
  simpa only [pullComparisonAlong_rfl] using he.pull q

/-- Inner equivalence is preserved by the same specified-endpoint pullback. -/
theorem innerEquivalent_pullAlong {e d : Comparison f g}
    (hi : IsFppfInnerEquivalent e d) (q : U ⟶ T)
    {f' : U ⟶ M.base} {g' : U ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g') :
    IsFppfInnerEquivalent (pullComparisonAlong e q hf hg)
      (pullComparisonAlong d q hf hg) := by
  subst f'
  subst g'
  simpa only [pullComparisonAlong_rfl] using innerEquivalent_pullComparison hi q

/-- Pulling a global comparison through a cover point is its direct pullback. -/
theorem pullComparisonAlong_pullComparison (e : Comparison f g)
    (p : V ⟶ T) (q : U ⟶ V) (r : U ⟶ T) (hqr : q ≫ p = r) :
    pullComparisonAlong (pullComparison e p) q
        (by rw [← Category.assoc, hqr])
        (by rw [← Category.assoc, hqr]) =
      pullComparison e r := by
  subst r
  rw [← pullComparisonAlong_rfl e p, pullComparisonAlong_comp]
  exact pullComparisonAlong_rfl e (q ≫ p)

/-- Pull the comparison on a cover to the test underlying one cover point. -/
def comparisonAtCoverPoint (p : V ⟶ T)
    (d : Comparison (p ≫ f) (p ≫ g)) {W : Over T} (a : W ⟶ Over.mk p) :
    Comparison (W.hom ≫ f) (W.hom ≫ g) :=
  pullComparisonAlong d a.left
    (by
      have ha : a.left ≫ p = W.hom := a.w
      rw [← Category.assoc, ha])
    (by
      have ha : a.left ≫ p = W.hom := a.w
      rw [← Category.assoc, ha])

@[reassoc]
private theorem compIso_hom_fst_fst (f : T ⟶ M.base) (p : V ⟶ T) :
    (baseChangeCompIso f p M.group).hom.hom.hom.left ≫
        pullback.fst (M.groupOver f).X.hom p ≫ pullback.fst M.group.X.hom f =
      pullback.fst M.group.X.hom (p ≫ f) := by
  change (baseChangeCompIso f p M.group).hom.hom.hom.left ≫
    pullback.fst (pullback.snd M.group.X.hom f) p ≫
      pullback.fst M.group.X.hom f = _
  rw [← baseChangeCompIso_inv_fst]
  change ((baseChangeCompIso f p M.group).hom ≫
    (baseChangeCompIso f p M.group).inv).hom.hom.left ≫ _ = _
  simp

@[reassoc]
private theorem map_fst {S : Scheme.{u}} {G H : GroupScheme S}
    (p : U ⟶ S) (d : G ⟶ H) :
    ((baseChange p).map d).hom.hom.left ≫ pullback.fst H.X.hom p =
      pullback.fst G.X.hom p ≫ d.hom.hom.left :=
  pullback.lift_fst _ _ _

private theorem coverPoint_comp (f : T ⟶ M.base) (p : V ⟶ T)
    {W : Over T} (a : W ⟶ Over.mk p) : a.left ≫ (p ≫ f) = W.hom ≫ f := by
  have ha : a.left ≫ p = W.hom := a.w
  rw [← Category.assoc, ha]

@[reassoc] private theorem coverPoint_lift (f : T ⟶ M.base) (p : V ⟶ T)
    {W : Over T} (a : W ⟶ Over.mk p)
    (x : Over.mk (𝟙 W.left) ⟶ (M.groupOver (W.hom ≫ f)).X) :
    x.left ≫ (Descent.pullbackComparison (p ≫ f) a.left (W.hom ≫ f)
        (coverPoint_comp f p a) M.group).inv.hom.hom.left ≫
        pullback.fst (M.groupOver (p ≫ f)).X.hom a.left =
      ((LocalGroupIso.coverPointsEquiv (M.groupOver f) a).symm
        (testPointsEquiv f W x)).left ≫
        (baseChangeCompIso f p M.group).inv.hom.hom.left := by
  let alpha := Descent.pullbackComparison (p ≫ f) a.left (W.hom ≫ f)
    (coverPoint_comp f p a) M.group
  let z := (LocalGroupIso.coverPointsEquiv (M.groupOver f) a).symm
    (testPointsEquiv f W x)
  have hz : z.left ≫ pullback.fst (M.groupOver f).X.hom p =
      (testPointsEquiv f W x).left := by
    have h := congrArg (fun k => k.left)
      ((LocalGroupIso.coverPointsEquiv (M.groupOver f) a).apply_symm_apply
        (testPointsEquiv f W x))
    rw [LocalGroupIso.coverPointsEquiv_left] at h
    change z.left ≫ pullback.fst (M.groupOver f).X.hom p =
      (testPointsEquiv f W x).left at h
    exact h
  apply pullback.hom_ext
  · change x.left ≫ alpha.inv.hom.hom.left ≫
      pullback.fst (M.groupOver (p ≫ f)).X.hom a.left ≫
        pullback.fst M.group.X.hom (p ≫ f) =
      (z.left ≫ (baseChangeCompIso f p M.group).inv.hom.hom.left) ≫
        pullback.fst M.group.X.hom (p ≫ f)
    dsimp only [alpha]
    rw [Descent.pullbackComparison_inv_fst]
    rw [Category.assoc, baseChangeCompIso_inv_fst]
    change _ = z.left ≫ pullback.fst (M.groupOver f).X.hom p ≫
      pullback.fst M.group.X.hom f
    rw [← Category.assoc, hz, testPointsEquiv_fst]
  · change x.left ≫ alpha.inv.hom.hom.left ≫
      pullback.fst (M.groupOver (p ≫ f)).X.hom a.left ≫
        pullback.snd M.group.X.hom (p ≫ f) =
      (z.left ≫ (baseChangeCompIso f p M.group).inv.hom.hom.left) ≫
        pullback.snd M.group.X.hom (p ≫ f)
    have hx := Over.w (x ≫ alpha.inv.hom.hom)
    change (x.left ≫ alpha.inv.hom.hom.left) ≫
      pullback.snd (M.groupOver (p ≫ f)).X.hom a.left = 𝟙 W.left at hx
    have hz' := Over.w (z ≫ (baseChangeCompIso f p M.group).inv.hom.hom)
    change (z.left ≫ (baseChangeCompIso f p M.group).inv.hom.hom.left) ≫
      pullback.snd M.group.X.hom (p ≫ f) = a.left at hz'
    rw [hz']
    change x.left ≫ alpha.inv.hom.hom.left ≫
      pullback.fst (M.groupOver (p ≫ f)).X.hom a.left ≫
        (M.groupOver (p ≫ f)).X.hom = a.left
    rw [pullback.condition, ← Category.assoc, ← Category.assoc, hx]
    exact Category.id_comp a.left

/-- The direct pullback at a cover point evaluates to the local all-test map. -/
theorem comparisonAtCoverPoint_toFun (p : V ⟶ T)
    (d : Comparison (p ≫ f) (p ≫ g)) {W : Over T} (a : W ⟶ Over.mk p)
    (x : Over.mk (𝟙 W.left) ⟶ (M.groupOver (W.hom ≫ f)).X) :
    testPointsEquiv g W (x ≫ (comparisonAtCoverPoint p d a).hom.hom.hom) =
      (comparisonLocalIso p d).toFun a (testPointsEquiv f W x) := by
  apply (baseChangePointsEquiv g N.group W).injective
  apply Over.OverMorphism.ext
  change (testPointsEquiv g W (x ≫ (comparisonAtCoverPoint p d a).hom.hom.hom)).left ≫
      pullback.fst N.group.X.hom g =
    ((comparisonLocalIso p d).toFun a (testPointsEquiv f W x)).left ≫
      pullback.fst N.group.X.hom g
  rw [testPointsEquiv_fst]
  simp only [comparisonAtCoverPoint, pullComparisonAlong, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Grp.comp_hom_hom, Over.comp_left, Category.assoc]
  rw [Descent.pullbackComparison_hom_fst, map_fst_assoc, coverPoint_lift_assoc]
  unfold comparisonLocalIso
  rw [LocalGroupIso.ofBaseChangeIso_toFun_left]
  simp only [comparisonToIterated, Iso.trans_hom, Iso.symm_hom,
    Grp.comp_hom_hom, Over.comp_left, Category.assoc]
  exact congrArg
    (fun k => ((LocalGroupIso.coverPointsEquiv (M.groupOver f) a).symm
      (testPointsEquiv f W x)).left ≫
        (baseChangeCompIso f p M.group).inv.hom.hom.left ≫ d.hom.hom.hom.left ≫ k)
    (compIso_hom_fst_fst g p).symm

/-- Pinned comparisons in a pulled-back inner class agree on every relative
scheme test and every pair of points of the cover. -/
theorem comparisonLocalIso_isIndependent (e : Comparison f g) (p : V ⟶ T)
    (d : Comparison (p ≫ f) (p ≫ g)) (hd : IsFppfLocallyPinned d)
    (hi : IsFppfInnerEquivalent (pullComparison e p) d) :
    (comparisonLocalIso p d).IsIndependent := by
  intro W a b y
  change (comparisonLocalIso p d).toFun a y = (comparisonLocalIso p d).toFun b y
  have hpin (c : W ⟶ Over.mk p) :
      IsFppfLocallyPinned (comparisonAtCoverPoint p d c) :=
    hd.pullAlong c.left (coverPoint_comp f p c) (coverPoint_comp g p c)
  have hinner (c : W ⟶ Over.mk p) :
      IsFppfInnerEquivalent (pullComparison e W.hom) (comparisonAtCoverPoint p d c) := by
    have h := innerEquivalent_pullAlong hi c.left
      (coverPoint_comp f p c) (coverPoint_comp g p c)
    rw [pullComparisonAlong_pullComparison e p c.left W.hom
      (show c.left ≫ p = W.hom from c.w)] at h
    exact h
  have heq := eq_of_fppfLocallyPinned_innerEquivalent (hpin a) (hpin b)
    ((hinner a).symm.trans (hinner b))
  let x := (testPointsEquiv f W).symm y
  have hx : testPointsEquiv f W x = y := (testPointsEquiv f W).apply_symm_apply y
  have h := congrArg (fun c : Comparison (W.hom ≫ f) (W.hom ≫ g) =>
    testPointsEquiv g W (x ≫ c.hom.hom.hom)) heq
  simpa only [comparisonAtCoverPoint_toFun, hx] using h

/-- Independence for fppf-locally pinned comparisons in any pulled-back inner
class. The cover map itself need not satisfy any geometric hypotheses. -/
def PinnedComparisonIndependence : Prop :=
  ∀ (M N : AffinePinnedModel.{u}) (T V : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g)
    (p : V ⟶ T) (d : Comparison (p ≫ f) (p ≫ g)),
    IsFppfLocallyPinned d → IsFppfInnerEquivalent (pullComparison e p) d →
      (comparisonLocalIso p d).IsIndependent

/-- Rigidity of pinned comparisons supplies the full all-test independence. -/
theorem pinnedComparisonIndependence : PinnedComparisonIndependence.{u} := by
  intro M N T V f g e p d hd hi
  exact comparisonLocalIso_isIndependent e p d hd hi

end Langlands.GroupScheme.AffinePinnedModel
