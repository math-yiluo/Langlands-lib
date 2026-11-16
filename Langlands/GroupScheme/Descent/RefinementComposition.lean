import Langlands.GroupScheme.Descent.Refinement

/-! # Composition of restrictions of actual descent data -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent

variable {B S C V E W T : Scheme.{u}}

namespace Datum

variable {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G)

/-- The overlap formula permits explicitly chosen representatives of its endpoints. -/
theorem reindexOverlap_eq (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w : q ≫ p = t ≫ b) (a d : Overlap t ⟶ S)
    (ha : fst t ≫ q = a) (hd : snd t ≫ q = d) :
    D.reindexOverlap t q b w =
      pullbackComparison q (fst t) a ha G ≪≫
        D.transition a d (by
          simpa only [← ha, ← hd, Category.assoc, w] using
            congrArg (· ≫ b) (pullback.condition (f := t) (g := t))) ≪≫
          (pullbackComparison q (snd t) d hd G).symm := by
  subst a
  subst d
  rfl

/-- Composing commuting squares again gives a commuting square. -/
theorem reindex_comp_condition (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w₁ : q ≫ p = t ≫ b) (r : W ⟶ E) (v : W ⟶ V) (c : E ⟶ C)
    (w₂ : v ≫ t = r ≫ c) : (v ≫ q) ≫ p = r ≫ (c ≫ b) := by
  simpa only [Category.assoc, w₁] using congrArg (· ≫ b) w₂

/-- The actual associativity comparison respects twice-restricted descent data. -/
theorem reindex_comp_compatible (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w₁ : q ≫ p = t ≫ b) (r : W ⟶ E) (v : W ⟶ V) (c : E ⟶ C)
    (w₂ : v ≫ t = r ≫ c) :
    Compatible ((D.reindex t q b w₁).reindex r v c w₂)
      (D.reindex r (v ≫ q) (c ≫ b) (reindex_comp_condition t q b w₁ r v c w₂))
      (pullbackComparison q v (v ≫ q) rfl G).hom := by
  change (Langlands.GroupScheme.baseChange (fst r)).map
      (pullbackComparison q v (v ≫ q) rfl G).hom ≫
        (D.reindexOverlap r (v ≫ q) (c ≫ b)
          (reindex_comp_condition t q b w₁ r v c w₂)).hom =
    ((D.reindex t q b w₁).reindexOverlap r v c w₂).hom ≫
      (Langlands.GroupScheme.baseChange (snd r)).map
        (pullbackComparison q v (v ≫ q) rfl G).hom
  rw [D.reindexOverlap_eq r (v ≫ q) (c ≫ b)
    (reindex_comp_condition t q b w₁ r v c w₂)
    ((fst r ≫ v) ≫ q) ((snd r ≫ v) ≫ q)
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm]
  apply (cancel_mono (pullbackComparison (v ≫ q) (snd r)
    ((snd r ≫ v) ≫ q) (Category.assoc _ _ _).symm G).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, reindexOverlap, reindexIso_hom,
    transition_reindex, reindexHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc _ (pullbackComparison (v ≫ q) (fst r)
    ((fst r ≫ v) ≫ q) (Category.assoc _ _ _).symm G).hom,
    pullbackComparison_assoc q (fst r) v (fst r ≫ v) rfl G,
    pullbackComparison_assoc q (snd r) v (snd r ≫ v) rfl G]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Collapse a supplied twice-restricted solution along the actual comparison. -/
def collapseReindexSolution (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w₁ : q ≫ p = t ≫ b) (r : W ⟶ E) (v : W ⟶ V) (c : E ⟶ C)
    (w₂ : v ≫ t = r ≫ c)
    (s : Solution ((D.reindex t q b w₁).reindex r v c w₂)) :
    Solution (D.reindex r (v ≫ q) (c ≫ b)
      (reindex_comp_condition t q b w₁ r v c w₂)) :=
  s.mapIso (pullbackComparison q v (v ≫ q) rfl G)
    (D.reindex_comp_compatible t q b w₁ r v c w₂)

end Datum
end Langlands.GroupScheme.Descent
