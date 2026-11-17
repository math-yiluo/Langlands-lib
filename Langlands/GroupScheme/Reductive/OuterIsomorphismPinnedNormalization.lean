import Langlands.GroupScheme.OuterIsomorphismActualNormalization
import Langlands.GroupScheme.Reductive.RelativePinnedNormalization
import Langlands.GroupScheme.Reductive.AffinePinnedComparisonDescent
import Langlands.GroupScheme.Reductive.AffinePinnedComparisonPullback

/-! # Pinned comparison normalization on actual isomorphism schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {S T W : Scheme.{u}}
  {f : S ⟶ M.base} {g : S ⟶ N.base}

/-- Express an isomorphism of iterated pullbacks as a direct comparison. -/
def comparisonFromIterated (p : T ⟶ S)
    (e : (baseChange p).obj (M.groupOver f) ≅
      (baseChange p).obj (N.groupOver g)) : Comparison (p ≫ f) (p ≫ g) :=
  baseChangeCompIso f p M.group ≪≫ e ≪≫ (baseChangeCompIso g p N.group).symm

@[simp] theorem comparisonToIterated_fromIterated (p : T ⟶ S)
    (e : (baseChange p).obj (M.groupOver f) ≅
      (baseChange p).obj (N.groupOver g)) :
    comparisonToIterated p (comparisonFromIterated p e) = e := by
  apply Iso.ext
  simp [comparisonToIterated, comparisonFromIterated]

@[simp] theorem comparisonFromIterated_toIterated (p : T ⟶ S)
    (d : Comparison (p ≫ f) (p ≫ g)) :
    comparisonFromIterated p (comparisonToIterated p d) = d := by
  apply Iso.ext
  simp [comparisonToIterated, comparisonFromIterated]

theorem comparisonToIterated_injective (p : T ⟶ S) :
    Function.Injective (comparisonToIterated (f := f) (g := g) p) := by
  intro e d h
  simpa only [comparisonFromIterated_toIterated] using
    congrArg (comparisonFromIterated p) h

/-- Direct comparisons and actual iterated pullback isomorphisms are equivalent. -/
def comparisonIteratedEquiv (p : T ⟶ S) :
    Comparison (p ≫ f) (p ≫ g) ≃
      ((baseChange p).obj (M.groupOver f) ≅
        (baseChange p).obj (N.groupOver g)) where
  toFun := comparisonToIterated p
  invFun := comparisonFromIterated p
  left_inv := comparisonFromIterated_toIterated p
  right_inv := comparisonToIterated_fromIterated p

/-- The direct/iterated equivalence respects refinement with specified base maps. -/
theorem comparisonToIterated_pullAlong (p : T ⟶ S) (r : W ⟶ T)
    (b : W ⟶ S) (hr : r ≫ p = b)
    (d : Comparison (p ≫ f) (p ≫ g)) :
    comparisonToIterated b
        (pullComparisonAlong d r
          ((Category.assoc r p f).symm.trans (congrArg (fun k => k ≫ f) hr))
          ((Category.assoc r p g).symm.trans (congrArg (fun k => k ≫ g) hr))) =
      Descent.pullIso r hr hr (comparisonToIterated p d) := by
  let hf := (Category.assoc r p f).symm.trans (congrArg (fun k => k ≫ f) hr)
  let hg := (Category.assoc r p g).symm.trans (congrArg (fun k => k ≫ g) hr)
  have hs := Dynamic.pullbackComparison_tower (G := M.group)
    f p (p ≫ f) rfl r b (b ≫ f) hr rfl hf
  have ht := Dynamic.pullbackComparison_tower (G := N.group)
    g p (p ≫ g) rfl r b (b ≫ g) hr rfl hg
  have hsi :
      (Descent.pullbackComparison f b (b ≫ f) rfl M.group).hom ≫
          (Descent.pullbackComparison (p ≫ f) r (b ≫ f) hf M.group).inv =
        (Descent.pullbackComparison p r b hr (M.groupOver f)).inv ≫
          (baseChange r).map
            (Descent.pullbackComparison f p (p ≫ f) rfl M.group).hom := by
    apply (cancel_epi
      (Descent.pullbackComparison p r b hr (M.groupOver f)).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using
      congrArg (fun k => k ≫
        (Descent.pullbackComparison (p ≫ f) r (b ≫ f) hf M.group).inv) hs.symm
  change (baseChangeCompIso f b M.group).inv ≫
      (Descent.pullbackComparison (p ≫ f) r (b ≫ f) hf M.group).inv =
    (Descent.pullbackComparison p r b hr (M.groupOver f)).inv ≫
      (baseChange r).map (baseChangeCompIso f p M.group).inv at hsi
  change (baseChange r).map (baseChangeCompIso g p N.group).inv ≫
      (Descent.pullbackComparison (p ≫ g) r (b ≫ g) hg N.group).hom =
    (Descent.pullbackComparison p r b hr (N.groupOver g)).hom ≫
      (baseChangeCompIso g b N.group).inv at ht
  have hti :
      (Descent.pullbackComparison (p ≫ g) r (b ≫ g) hg N.group).hom ≫
          (baseChangeCompIso g b N.group).hom =
        (baseChange r).map (baseChangeCompIso g p N.group).hom ≫
          (Descent.pullbackComparison p r b hr (N.groupOver g)).hom := by
    apply (cancel_epi ((baseChange r).map (baseChangeCompIso g p N.group).inv)).mp
    conv_rhs =>
      rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun k => k ≫ (baseChangeCompIso g b N.group).hom) ht
  apply Iso.ext
  simp only [comparisonToIterated, pullComparisonAlong, Descent.pullIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [← Category.assoc (baseChangeCompIso f b M.group).inv, hsi,
    Category.assoc, hti]

/-- The inverse equivalence also commutes with arbitrary refinement. -/
theorem comparisonFromIterated_pullAlong (p : T ⟶ S) (r : W ⟶ T)
    (b : W ⟶ S) (hr : r ≫ p = b)
    (e : (baseChange p).obj (M.groupOver f) ≅
      (baseChange p).obj (N.groupOver g)) :
    comparisonFromIterated b (Descent.pullIso r hr hr e) =
      pullComparisonAlong (comparisonFromIterated p e) r
        ((Category.assoc r p f).symm.trans (congrArg (fun k => k ≫ f) hr))
        ((Category.assoc r p g).symm.trans (congrArg (fun k => k ≫ g) hr)) := by
  apply comparisonToIterated_injective b
  rw [comparisonToIterated_fromIterated, comparisonToIterated_pullAlong,
    comparisonToIterated_fromIterated]

/-- Conjugation by actual comparison isomorphisms preserves inner classes. -/
theorem innerEquivalent_comparisonFromIterated (p : T ⟶ S)
    {e d : (baseChange p).obj (M.groupOver f) ≅
      (baseChange p).obj (N.groupOver g)} (h : IsFppfInnerEquivalent e d) :
    IsFppfInnerEquivalent (comparisonFromIterated p e)
      (comparisonFromIterated p d) :=
  (h.postcomp (baseChangeCompIso g p N.group).symm).precomp
    (baseChangeCompIso f p M.group)

theorem innerEquivalent_comparisonToIterated (p : T ⟶ S)
    {e d : Comparison (p ≫ f) (p ≫ g)} (h : IsFppfInnerEquivalent e d) :
    IsFppfInnerEquivalent (comparisonToIterated p e)
      (comparisonToIterated p d) :=
  (h.postcomp (baseChangeCompIso g p N.group)).precomp
    (baseChangeCompIso f p M.group).symm

end Langlands.GroupScheme.AffinePinnedModel

namespace Langlands.GroupScheme.RelativePinnedNormalization

open AffinePinnedModel

variable (n : RelativePinnedNormalization.{u})

/-- Correction respects pullback with explicitly equal endpoint maps. -/
theorem correction_pullAlong (M N : AffinePinnedModel.{u}) {T W : Scheme.{u}}
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g) (q : W ⟶ T)
    {f' : W ⟶ M.base} {g' : W ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g') :
    n.correction M N f' g' (pullComparisonAlong e q hf hg) =
      pullComparisonAlong (n.correction M N f g e) q hf hg := by
  subst f'
  subst g'
  simpa only [pullComparisonAlong_rfl, toRelativePinnedComparison] using
    n.toRelativePinnedComparison.compare_pull M N T W f g e q

/-- Supplied pinned normalization gives natural inner-class normalization of
actual isomorphisms on every relative test of the common base. -/
def actualNormalization (M N : AffinePinnedModel.{u}) {S : Scheme.{u}}
    (f : S ⟶ M.base) (g : S ⟶ N.base) :
    GroupIsomorphismScheme.ActualNormalization
      (G := M.groupOver f) (H := N.groupOver g) where
  normalize T e :=
    comparisonToIterated T.hom
      (n.correction M N (T.hom ≫ f) (T.hom ≫ g)
        (comparisonFromIterated T.hom e))
  naturality {T W} t e := by
    rw [comparisonFromIterated_pullAlong, n.correction_pullAlong,
      comparisonToIterated_pullAlong]
  invariant T e d h := by
    exact congrArg (comparisonToIterated T.hom)
      (n.correction_eq_of_innerEquivalent M N (T.hom ≫ f) (T.hom ≫ g)
        (innerEquivalent_comparisonFromIterated T.hom h))
  inner T e := by
    have h := innerEquivalent_comparisonToIterated T.hom
      (n.correction_spec M N (T.hom ≫ f) (T.hom ≫ g)
        (comparisonFromIterated T.hom e)).2
    simpa only [comparisonToIterated_fromIterated] using h

end Langlands.GroupScheme.RelativePinnedNormalization
