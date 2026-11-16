import Langlands.GroupScheme.Reductive.AffinePinnedLocalPinning
import Langlands.GroupScheme.Dynamic.PresentationComparison

/-! # Coherent pullback with explicitly equal comparison endpoints -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T U V : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- Pull an actual comparison to explicitly specified equal endpoint maps. -/
def pullComparisonAlong (e : Comparison f g) (q : U ⟶ T)
    {f' : U ⟶ M.base} {g' : U ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g') : Comparison f' g' :=
  (Descent.pullbackComparison f q f' hf M.group).symm ≪≫
    (baseChange q).mapIso e ≪≫ Descent.pullbackComparison g q g' hg N.group

@[simp]
theorem pullComparisonAlong_rfl (e : Comparison f g) (q : U ⟶ T) :
    pullComparisonAlong e q rfl rfl = pullComparison e q := by
  simp [pullComparisonAlong, Descent.pullbackComparison, pullComparison]

/-- The supplied actual direct/iterated identifications satisfy tower
coherence even when the two models have different original bases. -/
theorem pullComparisonAlong_comp (e : Comparison f g) (q : U ⟶ T) (r : V ⟶ U)
    {f' : U ⟶ M.base} {g' : U ⟶ N.base}
    {f'' : V ⟶ M.base} {g'' : V ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g')
    (hrf : r ≫ f' = f'') (hrg : r ≫ g' = g'') :
    pullComparisonAlong (pullComparisonAlong e q hf hg) r hrf hrg =
      pullComparisonAlong e (r ≫ q)
        ((Category.assoc _ _ _).trans ((congrArg (fun b => r ≫ b) hf).trans hrf))
        ((Category.assoc _ _ _).trans ((congrArg (fun b => r ≫ b) hg).trans hrg)) := by
  let hsf := (Category.assoc r q f).trans
    ((congrArg (fun b => r ≫ b) hf).trans hrf)
  let htg := (Category.assoc r q g).trans
    ((congrArg (fun b => r ≫ b) hg).trans hrg)
  have hs := Dynamic.pullbackComparison_tower (G := M.group)
    f q f' hf r (r ≫ q) f'' rfl hsf hrf
  have ht := Dynamic.pullbackComparison_tower (G := N.group)
    g q g' hg r (r ≫ q) g'' rfl htg hrg
  have hsi :
      (baseChange r).mapIso (Descent.pullbackComparison f q f' hf M.group) ≪≫
          Descent.pullbackComparison f' r f'' hrf M.group =
        Descent.pullbackComparison q r (r ≫ q) rfl (M.groupOver f) ≪≫
          Descent.pullbackComparison f (r ≫ q) f'' hsf M.group :=
    Iso.ext hs
  have hsinv := congrArg Iso.inv hsi
  change (Descent.pullbackComparison f' r f'' hrf M.group).inv ≫
      (baseChange r).map (Descent.pullbackComparison f q f' hf M.group).inv =
    (Descent.pullbackComparison f (r ≫ q) f'' hsf M.group).inv ≫
      (Descent.pullbackComparison q r (r ≫ q) rfl (M.groupOver f)).inv at hsinv
  apply Iso.ext
  simp only [pullComparisonAlong, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (Descent.pullbackComparison f' r f'' hrf M.group).inv,
    hsinv, Category.assoc, ht,
    Descent.pullbackComparison_naturality_assoc, Iso.inv_hom_id_assoc]

/-- The concrete pinning predicate respects pullback with specified equal
endpoints as well as the normalized direct pullback. -/
theorem IsLocallyPinned.pullAlong {e : Comparison f g} (he : IsLocallyPinned e)
    (q : U ⟶ T) {f' : U ⟶ M.base} {g' : U ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g') :
    IsLocallyPinned (pullComparisonAlong e q hf hg) := by
  subst f'
  subst g'
  simpa only [pullComparisonAlong_rfl] using he.pull q

end Langlands.GroupScheme.AffinePinnedModel
