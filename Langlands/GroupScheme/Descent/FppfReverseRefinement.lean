import Langlands.GroupScheme.Descent.ReverseRefinement
import Langlands.GroupScheme.Descent.FppfHomDescent
import Langlands.GroupScheme.Descent.FppfReflection

/-! # Recovering actual solutions from an fppf refinement -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent

variable {B S V T U : Scheme.{u}}

namespace Solution

variable {p : S ⟶ B} [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  {G H : GroupScheme S} {D : Datum p G} {E : Datum p H}

def descendIsoOfFppf (s : Solution D) (t : Solution E)
    (e : G ≅ H) (he : Compatible D E e.hom) : s.obj ≅ t.obj := by
  let f := s.descendHomOfFppf t e.hom he
  have hf : (GroupScheme.baseChange p).map f = (s.iso ≪≫ e ≪≫ t.iso.symm).hom :=
    FppfHomDescent.baseChange_hom p _ _
  letI : IsIso ((GroupScheme.baseChange p).map f) := by
    rw [hf]
    infer_instance
  exact GroupScheme.isoOfFppfBaseChange p f

theorem baseChange_descendIsoOfFppf (s : Solution D) (t : Solution E)
    (e : G ≅ H) (he : Compatible D E e.hom) :
    (GroupScheme.baseChange p).map (s.descendIsoOfFppf t e he).hom ≫ t.iso.hom =
      s.iso.hom ≫ e.hom :=
  s.baseChange_descendHomOfFppf t e.hom he

end Solution

namespace Datum

variable {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G)

variable (q : V ⟶ S) [Flat (q ≫ p)] [LocallyOfFinitePresentation (q ≫ p)] [Surjective (q ≫ p)]
  (s : Solution (D.refine q))

/-- The comparison descends along the pullback of the refined cover. -/
def fppfRefinementComparison :
    (Langlands.GroupScheme.baseChange p).obj s.obj ≅ G :=
  (D.refinementSolutionOnCover q s).descendIsoOfFppf
    (D.transitionSolution (pullback.snd (q ≫ p) p) (pullback.fst (q ≫ p) p ≫ q)
      (by simpa only [Category.assoc] using
        (pullback.condition (f := q ≫ p) (g := p))))
    (Iso.refl _) (compatible_id _)

/-- Pullback of the descended comparison gives the supplied local comparison. -/
theorem fppfRefinementComparison_baseChange :
    (Langlands.GroupScheme.baseChange (pullback.snd (q ≫ p) p)).map
        (D.fppfRefinementComparison q s).hom =
      (squareComparison p (pullback.snd (q ≫ p) p) (q ≫ p)
        (pullback.fst (q ≫ p) p) pullback.condition.symm s.obj).hom ≫
      (Langlands.GroupScheme.baseChange (pullback.fst (q ≫ p) p)).map s.iso.hom ≫
      (pullbackComparison q (pullback.fst (q ≫ p) p)
        (pullback.fst (q ≫ p) p ≫ q) rfl G).hom ≫
      (D.transition (pullback.fst (q ≫ p) p ≫ q) (pullback.snd (q ≫ p) p)
        (by simpa only [Category.assoc] using
          (pullback.condition (f := q ≫ p) (g := p)))).hom := by
  let a := D.refinementSolutionOnCover q s
  let b := D.transitionSolution (pullback.snd (q ≫ p) p)
    (pullback.fst (q ≫ p) p ≫ q)
    (by simpa only [Category.assoc] using (pullback.condition (f := q ≫ p) (g := p)))
  have h := a.baseChange_descendIsoOfFppf b (Iso.refl _) (compatible_id _)
  have hh : (Langlands.GroupScheme.baseChange (pullback.snd (q ≫ p) p)).map
      (D.fppfRefinementComparison q s).hom = a.iso.hom ≫ b.iso.inv := by
    apply (cancel_mono b.iso.hom).mp
    simpa only [fppfRefinementComparison, a, b, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Iso.refl_hom] using h
  rw [hh]
  simp only [a, b, refinementSolutionOnCover, collapseReindexSolution,
    Solution.mapIso, Solution.reindex, transitionSolution, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_inv, Category.assoc]

/-- The local recovery formula remains valid on any test scheme over the cross overlap. -/
theorem fppfRefinementComparison_restrict
    (k : U ⟶ pullback (q ≫ p) p) (b : U ⟶ S) (a : U ⟶ V)
    (hb : k ≫ pullback.snd (q ≫ p) p = b)
    (ha : k ≫ pullback.fst (q ≫ p) p = a) :
    (Langlands.GroupScheme.baseChange b).map (D.fppfRefinementComparison q s).hom =
      (squareComparison p b (q ≫ p) a (by
        simpa only [← hb, ← ha, Category.assoc] using
          congrArg (k ≫ ·) (pullback.condition (f := q ≫ p) (g := p)).symm) s.obj).hom ≫
      (Langlands.GroupScheme.baseChange a).map s.iso.hom ≫
      (pullbackComparison q a (a ≫ q) rfl G).hom ≫
      (D.transition (a ≫ q) b (by
        simpa only [← hb, ← ha, Category.assoc] using
          congrArg (k ≫ ·) (pullback.condition (f := q ≫ p) (g := p)))).hom := by
  let r := pullback.snd (q ≫ p) p
  let v := pullback.fst (q ≫ p) p
  have hw : (v ≫ q) ≫ p = r ≫ p := by
    simpa only [Category.assoc] using (pullback.condition (f := q ≫ p) (g := p))
  have h := congrArg
    (fun f => (Langlands.GroupScheme.baseChange k).map f ≫
      (pullbackComparison r k b hb G).hom) (D.fppfRefinementComparison_baseChange q s)
  rw [pullbackComparison_naturality] at h
  simp only [Functor.map_comp, Category.assoc] at h
  rw [D.map_transition k (v ≫ q) r hw (a ≫ q) b
    (by rw [← ha, Category.assoc]) hb] at h
  rw [← Category.assoc ((Langlands.GroupScheme.baseChange k).map
      (pullbackComparison q v (v ≫ q) rfl G).hom)
      (pullbackComparison (v ≫ q) k (a ≫ q)
      (by rw [← ha, Category.assoc]) G).hom,
    pullbackComparison_assoc q k v a ha G] at h
  simp only [Category.assoc] at h
  rw [← Category.assoc ((Langlands.GroupScheme.baseChange k).map
      ((Langlands.GroupScheme.baseChange v).map s.iso.hom))
      (pullbackComparison v k a ha
      ((Langlands.GroupScheme.baseChange q).obj G)).hom,
    pullbackComparison_naturality v k a ha s.iso.hom] at h
  simp only [Category.assoc] at h
  rw [← Category.assoc ((Langlands.GroupScheme.baseChange k).map
      (squareComparison p r (q ≫ p) v pullback.condition.symm s.obj).hom)
      (pullbackComparison v k a ha
      ((Langlands.GroupScheme.baseChange (q ≫ p)).obj s.obj)).hom,
    squareComparison_pullback p r (q ≫ p) v pullback.condition.symm k b a hb ha s.obj]
    at h
  exact (cancel_epi
    (pullbackComparison r k b hb ((Langlands.GroupScheme.baseChange p).obj s.obj)).hom).mp
      (by simpa only [Category.assoc] using h)

/-- A test scheme with a refined-cover coordinate has the same recovery formula. -/
theorem fppfRefinementComparison_local (a : U ⟶ V) (b : U ⟶ S)
    (w : a ≫ (q ≫ p) = b ≫ p) :
    (Langlands.GroupScheme.baseChange b).map (D.fppfRefinementComparison q s).hom =
      (squareComparison p b (q ≫ p) a w.symm s.obj).hom ≫
      (Langlands.GroupScheme.baseChange a).map s.iso.hom ≫
      (pullbackComparison q a (a ≫ q) rfl G).hom ≫
      (D.transition (a ≫ q) b (by simpa only [Category.assoc] using w)).hom :=
  D.fppfRefinementComparison_restrict q s (pullback.lift a b w) b a
    (by simp only [pullback.lift_snd]) (by simp only [pullback.lift_fst])

/-- With a common refined coordinate, the recovered comparison respects transitions. -/
theorem fppfRefinementComparison_transition (a : U ⟶ V) (f g : U ⟶ S)
    (h : f ≫ p = g ≫ p) (w : a ≫ (q ≫ p) = f ≫ p) :
    (Langlands.GroupScheme.baseChange f).map (D.fppfRefinementComparison q s).hom ≫
        (D.transition f g h).hom =
      ((canonicalDatum p s.obj).transition f g h).hom ≫
        (Langlands.GroupScheme.baseChange g).map (D.fppfRefinementComparison q s).hom := by
  rw [D.fppfRefinementComparison_local q s a f w,
    D.fppfRefinementComparison_local q s a g (w.trans h)]
  simp only [Category.assoc]
  rw [D.transition_comp (a ≫ q) f g
    (by simpa only [Category.assoc] using w) h,
    ← Category.assoc ((canonicalDatum p s.obj).transition f g h).hom
      (squareComparison p g (q ≫ p) a (w.trans h).symm s.obj).hom,
    canonicalDatum_transition_squareComparison p (q ≫ p) f g h a w.symm s.obj]

/-- The descended comparison respects the original datum over its original base. -/
theorem fppfRefinementComparison_compatible :
    Compatible (canonicalDatum p s.obj) D (D.fppfRefinementComparison q s).hom := by
  let z := pullback.snd (q ≫ p) (fst p ≫ p)
  let a := pullback.fst (q ≫ p) (fst p ≫ p)
  let f := z ≫ fst p
  let g := z ≫ snd p
  have hfg : f ≫ p = g ≫ p := by
    simp only [f, g, Category.assoc, pullback.condition]
  have ha : a ≫ (q ≫ p) = f ≫ p := by
    simpa only [a, f, Category.assoc] using
      (pullback.condition (f := q ≫ p) (g := fst p ≫ p))
  have h := D.fppfRefinementComparison_transition q s a f g hfg ha
  have hc : pullHom z rfl rfl
      ((Langlands.GroupScheme.baseChange (fst p)).map (D.fppfRefinementComparison q s).hom ≫
        D.overlap.hom) =
      pullHom z rfl rfl
        ((canonicalOverlap p s.obj).hom ≫
          (Langlands.GroupScheme.baseChange (snd p)).map
            (D.fppfRefinementComparison q s).hom) := by
    rw [pullHom_comp z rfl rfl rfl, pullHom_comp z rfl rfl rfl,
      pullHom_map, pullHom_map, D.pullHom_overlap]
    change _ = pullHom z rfl rfl (canonicalDatum p s.obj).overlap.hom ≫ _
    rw [(canonicalDatum p s.obj).pullHom_overlap]
    exact h
  change (Langlands.GroupScheme.baseChange (fst p)).map (D.fppfRefinementComparison q s).hom ≫
      D.overlap.hom =
    (canonicalOverlap p s.obj).hom ≫
      (Langlands.GroupScheme.baseChange (snd p)).map (D.fppfRefinementComparison q s).hom
  apply (Langlands.GroupScheme.baseChange z).map_injective
  apply (cancel_epi
    (pullbackComparison (fst p) z f rfl
      ((Langlands.GroupScheme.baseChange p).obj s.obj)).inv).mp
  apply (cancel_mono (pullbackComparison (snd p) z g rfl G).hom).mp
  exact hc

/-- Recover a solution on the original cover from a solution on an fppf refinement. -/
def fppfSolutionOfRefinement : Solution D where
  obj := s.obj
  iso := D.fppfRefinementComparison q s
  compatible := D.fppfRefinementComparison_compatible q s

end Datum
end Langlands.GroupScheme.Descent
