import Langlands.GroupScheme.Descent.PullHomCoherence

/-! # Reindexing actual group-scheme Čech data -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent

variable {B S T U V : Scheme.{u}}

@[reassoc] private theorem map_fst (a : U ⟶ T)
    {G H : GroupScheme T} (f : G ⟶ H) :
    ((baseChange a).map f).hom.hom.left ≫ pullback.fst H.X.hom a =
      pullback.fst G.X.hom a ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- The two ways of removing a repeated base change have the same actual projection. -/
theorem pullbackComparison_assoc (q : V ⟶ S) (a : U ⟶ T)
    (f : T ⟶ V) (r : U ⟶ V) (hf : a ≫ f = r) (G : GroupScheme S) :
    (baseChange a).map (pullbackComparison q f (f ≫ q) rfl G).hom ≫
        (pullbackComparison (f ≫ q) a (r ≫ q)
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) hf)) G).hom =
      (pullbackComparison f a r hf ((baseChange q).obj G)).hom ≫
        (pullbackComparison q r (r ≫ q) rfl G).hom := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      pullbackComparison_hom_fst, pullbackComparison_hom_fst_assoc, map_fst_assoc]
  · exact (Over.w _).trans (Over.w _).symm

/-- Change the coordinate base of a comparison between two direct pullbacks. -/
def reindexHom (q : V ⟶ S) (f g : T ⟶ V) {G H : GroupScheme S}
    (e : (baseChange (f ≫ q)).obj G ⟶ (baseChange (g ≫ q)).obj H) :
    (baseChange f).obj ((baseChange q).obj G) ⟶
      (baseChange g).obj ((baseChange q).obj H) :=
  (pullbackComparison q f (f ≫ q) rfl G).hom ≫ e ≫
    (pullbackComparison q g (g ≫ q) rfl H).inv

/-- The same change of coordinate base for actual isomorphisms. -/
def reindexIso (q : V ⟶ S) (f g : T ⟶ V) {G H : GroupScheme S}
    (e : (baseChange (f ≫ q)).obj G ≅ (baseChange (g ≫ q)).obj H) :
    (baseChange f).obj ((baseChange q).obj G) ≅
      (baseChange g).obj ((baseChange q).obj H) :=
  pullbackComparison q f (f ≫ q) rfl G ≪≫ e ≪≫
    (pullbackComparison q g (g ≫ q) rfl H).symm

@[simp] theorem reindexIso_hom (q : V ⟶ S) (f g : T ⟶ V)
    {G H : GroupScheme S}
    (e : (baseChange (f ≫ q)).obj G ≅ (baseChange (g ≫ q)).obj H) :
    (reindexIso q f g e).hom = reindexHom q f g e.hom := rfl

/-- Changing the coordinate base preserves composition. -/
theorem reindexHom_comp (q : V ⟶ S) (f g h : T ⟶ V)
    {G H I : GroupScheme S}
    (e : (baseChange (f ≫ q)).obj G ⟶ (baseChange (g ≫ q)).obj H)
    (d : (baseChange (g ≫ q)).obj H ⟶ (baseChange (h ≫ q)).obj I) :
    reindexHom q f h (e ≫ d) = reindexHom q f g e ≫ reindexHom q g h d := by
  simp [reindexHom]

/-- Reindexing a comparison commutes with every further actual pullback. -/
theorem pullHom_reindexHom (q : V ⟶ S) (a : U ⟶ T)
    {f g : T ⟶ V} {r s : U ⟶ V}
    (hf : a ≫ f = r) (hg : a ≫ g = s) {G H : GroupScheme S}
    (e : (baseChange (f ≫ q)).obj G ⟶ (baseChange (g ≫ q)).obj H) :
    pullHom a hf hg (reindexHom q f g e) =
      reindexHom q r s (pullHom a
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) hf))
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) hg)) e) := by
  let cf := pullbackComparison q f (f ≫ q) rfl G
  let cg := pullbackComparison q g (g ≫ q) rfl H
  let cr := pullbackComparison q r (r ≫ q) rfl G
  let cs := pullbackComparison q s (s ≫ q) rfl H
  let af := pullbackComparison f a r hf ((baseChange q).obj G)
  let ag := pullbackComparison g a s hg ((baseChange q).obj H)
  let bf := pullbackComparison (f ≫ q) a (r ≫ q)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) hf)) G
  let bg := pullbackComparison (g ≫ q) a (s ≫ q)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) hg)) H
  have hsrc : af.inv ≫ (baseChange a).map cf.hom = cr.hom ≫ bf.inv := by
    apply (cancel_mono bf.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [pullbackComparison_assoc]
    exact Iso.inv_hom_id_assoc af cr.hom
  have htgt : (baseChange a).map cg.inv ≫ ag.hom = bg.hom ≫ cs.inv := by
    apply (cancel_epi ((baseChange a).map cg.hom)).mp
    rw [← Category.assoc, Iso.map_hom_inv_id, Category.id_comp,
      ← Category.assoc, pullbackComparison_assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  change af.inv ≫ (baseChange a).map (cf.hom ≫ e ≫ cg.inv) ≫ ag.hom =
    cr.hom ≫ (bf.inv ≫ (baseChange a).map e ≫ bg.hom) ≫ cs.inv
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc af.inv ((baseChange a).map cf.hom), hsrc, htgt]
  simp only [Category.assoc]

namespace Datum

variable {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G)

/-- The actual transition isomorphism along any two maps with equal base composite. -/
def transition (f g : T ⟶ S) (h : f ≫ p = g ≫ p) :
    (baseChange f).obj G ≅ (baseChange g).obj G :=
  pullIso (pullback.lift f g h) (by simp) (by simp) D.overlap

/-- Transition isomorphisms commute with further actual pullback. -/
theorem pullHom_transition (a : U ⟶ T) (f g : T ⟶ S)
    (h : f ≫ p = g ≫ p) (r s : U ⟶ S) (hf : a ≫ f = r) (hg : a ≫ g = s) :
    pullHom a hf hg (D.transition f g h).hom =
      (D.transition r s (by rw [← hf, ← hg, Category.assoc, Category.assoc, h])).hom := by
  simp only [transition, pullIso_hom, pullHom_pullHom]
  congr 1
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst,
    pullback.lift_snd, hf, hg]

/-- The original triple-overlap cocycle gives composition on every test scheme. -/
theorem transition_comp (f g h : T ⟶ S)
    (hfg : f ≫ p = g ≫ p) (hgh : g ≫ p = h ≫ p) :
    (D.transition f g hfg).hom ≫ (D.transition g h hgh).hom =
      (D.transition f h (hfg.trans hgh)).hom := by
  let a : T ⟶ Triple p := pullback.lift
    (pullback.lift f g hfg) (pullback.lift g h hgh) (by simp)
  have ha₁ : a ≫ p1 p = f := by simp [a, p1]
  have ha₂ : a ≫ p2 p = g := by simp [a, p2]
  have ha₃ : a ≫ p3 p = h := by simp [a, p3]
  have ha₁₃ : a ≫ p13 p = pullback.lift f h (hfg.trans hgh) := by
    apply pullback.hom_ext <;> simp [ha₁, ha₃]
  have hc := congrArg (pullHom a ha₁ ha₃) D.cocycle
  rw [pullHom_comp a ha₁ ha₂ ha₃] at hc
  simpa only [pullIso_hom, pullHom_pullHom, a, p12, p23,
    pullback.lift_fst, pullback.lift_snd, ha₁₃, transition] using hc

end Datum
end Langlands.GroupScheme.Descent
