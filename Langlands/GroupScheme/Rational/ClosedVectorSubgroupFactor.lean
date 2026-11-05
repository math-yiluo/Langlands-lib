import Langlands.GroupScheme.Rational.ClosedVectorSubgroupInduction
import Langlands.GroupScheme.Rational.ClosedVectorSubgroupRelation
import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.Unipotent.PolynomialKernelAmbientCapture

/-! # Capturing vector factors of closed vector subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClosedVectorSubgroup

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

variable {k : Type u} [Field k]

/-- The additive-row adapter for an arbitrary affine source. -/
theorem exists_annihilating_polynomialRow_of_affine
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffine H.X.left]
    {n : ℕ} (i : H ⟶ VectorGroup.groupScheme (CommRingCat.of k) n)
    (hi : IsClosedSubgroup i) (hproper : ¬ IsIso i) :
    ∃ (f : Fin n → Polynomial k)
      (hf : ∀ j, Unipotent.OneDimensional.IsAdditive (f j)),
      (∃ j, f j ≠ 0) ∧ i ≫ Unipotent.polynomialRow f hf = 0 := by
  let e := AffineCoordinates.groupSchemeIso H
  let q := e.hom ≫ i
  let : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion q.hom.hom.left := by
    change IsClosedImmersion (e.hom.hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  have hq : ¬ IsIso q := by
    intro h
    have heq : i = e.inv ≫ q := by simp [q]
    apply hproper
    rw [heq]
    infer_instance
  obtain ⟨f, hf, hne, hz⟩ :=
    exists_annihilating_polynomialRow (AffineCoordinates.corepresentation H) q hq
  refine ⟨f, hf, hne, ?_⟩
  have heq : i = e.inv ≫ q := by simp [q]
  rw [heq, Category.assoc, hz, comp_zero]


/-- A proper closed vector subgroup admits a strictly smaller ambient vector
retract capturing its pointed affine-line maps over the separable closure. -/
theorem exists_lowering_separableClosure
    (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k)))
    (i : H ⟶ VectorGroup.groupScheme (CommRingCat.of k) n)
    (hi : IsClosedSubgroup i) (hproper : ¬ IsIso i) :
    ∃ (r : ℕ) (s : VectorGroup.groupScheme (CommRingCat.of k) r ⟶
        VectorGroup.groupScheme (CommRingCat.of k) n)
      (t : VectorGroup.groupScheme (CommRingCat.of k) n ⟶
        VectorGroup.groupScheme (CommRingCat.of k) r),
      r < n ∧ s ≫ t = 𝟙 _ ∧
        ∀ a : AffineLine.scheme (Spec (CommRingCat.of (SeparableClosure k))) ⟶
            ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj H).X,
          AffineLine.zeroSection (Spec (CommRingCat.of (SeparableClosure k))) ≫ a = 1 →
          a ≫ ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map i).hom.hom ∈
            (SubgroupFunctor.range
              ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map s)).carrier _ := by
  let := isAffine_of_closed_into_vector i hi
  obtain ⟨f, hf, ⟨j, hj⟩, hz⟩ := exists_annihilating_polynomialRow_of_affine i hi hproper
  have hf0 : f ≠ 0 := fun h => hj (congrFun h j)
  obtain ⟨r, s, t, hrn, _hs, hst, _hsrow, hcap⟩ :=
    Unipotent.exists_polynomialKernelAmbientCapture n f hf hf0
  refine ⟨r, s, t, hrn, hst, ?_⟩
  intro a ha
  apply hcap (a ≫ _)
  · rw [← Category.assoc, ha, MonObj.one_comp]
  · let F := GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))
    change (a ≫ (F.map i).hom.hom) ≫ (F.map (Unipotent.polynomialRow f hf)).hom.hom = 1
    rw [Category.assoc, ← Grp.comp_hom_hom, ← F.map_comp, hz, Functor.map_zero,
      Grp.zero_hom, Mon.zero_hom, ← Hom.one_def, MonObj.comp_one]

/-- A closed vector subgroup has an actual vector retract capturing all
pointed affine-line maps after the separable closure. -/
theorem exists_capturing_separableClosure
    (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k)))
    (i : H ⟶ VectorGroup.groupScheme (CommRingCat.of k) n)
    (hi : IsClosedSubgroup i) :
    ∃ (r : ℕ) (l : VectorGroup.groupScheme (CommRingCat.of k) r ⟶ H)
      (q : H ⟶ VectorGroup.groupScheme (CommRingCat.of k) r),
      l ≫ q = 𝟙 _ ∧ CapturesPointedAffineLineMaps
        ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map l) := by
  obtain ⟨r, l, t, hsplit, hcap⟩ :=
    exists_capturing_ambientRetraction_of_lowering
      (algebraBaseMap k (SeparableClosure k)) _ _
      (AffineLine.zeroSection (Spec (CommRingCat.of (SeparableClosure k))))
      exists_lowering_separableClosure n H i hi
  exact ⟨r, l, i ≫ t, hsplit, hcap⟩

/-- An actual vector retract with separable-closure pointed-line capture. -/
structure SeparableLineRetraction (H : GroupScheme (Spec (CommRingCat.of k))) where
  dimension : ℕ
  sectionMap : VectorGroup.groupScheme (CommRingCat.of k) dimension ⟶ H
  retraction : H ⟶ VectorGroup.groupScheme (CommRingCat.of k) dimension
  section_comp_retraction : sectionMap ≫ retraction = 𝟙 _
  captures : CapturesPointedAffineLineMaps
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map sectionMap)

/-- Choose the capturing vector retract of a closed vector subgroup. -/
def separableLineRetraction
    (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k)))
    (i : H ⟶ VectorGroup.groupScheme (CommRingCat.of k) n)
    (hi : IsClosedSubgroup i) : SeparableLineRetraction H :=
  Classical.choice (by
    obtain ⟨r, l, q, hs, hc⟩ := exists_capturing_separableClosure n H i hi
    exact ⟨⟨r, l, q, hs, hc⟩⟩)

end Langlands.GroupScheme.ClosedVectorSubgroup
