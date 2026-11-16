import Langlands.GroupScheme.Descent.SolutionRefinement

/-! # Canonical solutions on a datum's own covering scheme -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent

variable {B S T U W : Scheme.{u}}

/-- A canonical overlap is the comparison around its defining pullback square. -/
theorem canonicalOverlap_eq_squareComparison (r : W ⟶ S) (G : GroupScheme S) :
    canonicalOverlap r G =
      squareComparison r (fst r) r (snd r) pullback.condition G := by
  apply Iso.ext
  apply hom_ext_pullback_tower r (snd r) G
  rw [canonicalOverlap_fst, squareComparison_hom_fst_fst]

namespace Datum

variable {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G)

/-- Direct pullback comparisons turn a pulled transition into the transition of the endpoints. -/
theorem map_transition (k : U ⟶ T) (f g : T ⟶ S)
    (h : f ≫ p = g ≫ p) (a b : U ⟶ S) (ha : k ≫ f = a) (hb : k ≫ g = b) :
    (Langlands.GroupScheme.baseChange k).map (D.transition f g h).hom ≫
        (pullbackComparison g k b hb G).hom =
      (pullbackComparison f k a ha G).hom ≫
        (D.transition a b
          (by rw [← ha, ← hb, Category.assoc, Category.assoc, h])).hom := by
  apply (cancel_epi (pullbackComparison f k a ha G).inv).mp
  simpa only [pullHom, Category.assoc, Iso.inv_hom_id_assoc] using
    D.pullHom_transition k f g h a b ha hb

/-- Transition to the cover coordinate respects its canonical datum. -/
theorem transition_canonicalCompatible (r a : W ⟶ S) (w : a ≫ p = r ≫ p) :
    Compatible (D.reindex r a p w) (canonicalDatum r G)
      (D.transition a r w).hom := by
  change (Langlands.GroupScheme.baseChange (fst r)).map (D.transition a r w).hom ≫
      (canonicalOverlap r G).hom =
    (D.reindexOverlap r a p w).hom ≫
      (Langlands.GroupScheme.baseChange (snd r)).map (D.transition a r w).hom
  apply (cancel_mono
    (pullbackComparison r (snd r) (snd r ≫ r) rfl G).hom).mp
  rw [canonicalOverlap_eq_squareComparison]
  simp only [squareComparison, Iso.trans_hom, Iso.symm_hom,
    reindexOverlap, reindexIso_hom, reindexHom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [D.map_transition (fst r) a r w (fst r ≫ a) (snd r ≫ r) rfl pullback.condition,
    D.map_transition (snd r) a r w (snd r ≫ a) (snd r ≫ r) rfl rfl]
  simp only [Iso.inv_hom_id_assoc]
  have h₁ : (fst r ≫ a) ≫ p = (snd r ≫ a) ≫ p := by
    simpa only [Category.assoc, w] using
      congrArg (· ≫ p) (pullback.condition (f := r) (g := r))
  have h₂ : (snd r ≫ a) ≫ p = (snd r ≫ r) ≫ p := by
    simp only [Category.assoc, w]
  exact congrArg ((pullbackComparison a (fst r) (fst r ≫ a) rfl G).hom ≫ ·)
    (D.transition_comp (fst r ≫ a) (snd r ≫ a) (snd r ≫ r) h₁ h₂).symm

/-- A datum restricted to a map into its cover has the original group as a solution. -/
def transitionSolution (r a : W ⟶ S) (w : a ≫ p = r ≫ p) :
    Solution (D.reindex r a p w) where
  obj := G
  iso := (D.transition a r w).symm
  compatible := (D.transition_canonicalCompatible r a w).inv _

end Datum
end Langlands.GroupScheme.Descent
