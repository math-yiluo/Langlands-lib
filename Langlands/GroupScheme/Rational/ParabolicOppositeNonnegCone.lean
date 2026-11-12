import Langlands.GroupScheme.Rational.ParabolicIntrinsicNonnegCone
import Langlands.GroupScheme.Dynamic.OppositeParabolicComparison

/-! # Opposite cones on the same actual Levi split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

open RealTorusSpace

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {q : Q ⟶ G} {lQ : M ⟶ Q} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a) (s : ParabolicRootPresentation q lQ a)

include r in
/-- Negation stability on the ambient maximal split torus descends to the
specified actual Levi split component. -/
theorem neg_mem_componentRelativeRoots (hG : IsConnectedReductive G)
    {β : characterLattice A} (hβ : β ∈ relativeRoots (a ≫ l ≫ p)) :
    -β ∈ relativeRoots (a ≫ l ≫ p) := by
  rw [← r.isCompatible.factor_comp] at hβ ⊢
  exact neg_mem_roots_comp r.isCompatible.maximalSplit.1.1
    r.isCompatible.splitComponent.1.isSplitSubtorus.1 r.data.f r.data.i
    (relativeRootNegation k G hG r.data.T r.data.i r.isCompatible.maximalSplit) hβ

variable [Smooth G.X.hom]

/-- The exact rational intersection and same-Levi hypotheses force opposite
strict and weak signs for all actual split-component roots. -/
theorem opposite_componentRoot_signs (hG : IsConnectedReductive G)
    (hLevi : lQ ≫ q = l ≫ p)
    (hpoints : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) ⊓
        (SubgroupFunctor.range q).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _))) :
    ∀ β ∈ relativeRoots (a ≫ l ≫ p),
      (0 ≤ latticePairing A β s.splitComponentCocharacter ↔
        latticePairing A β r.splitComponentCocharacter ≤ 0) ∧
      (0 < latticePairing A β s.splitComponentCocharacter ↔
        latticePairing A β r.splitComponentCocharacter < 0) := by
  have hsP : SubgroupFunctor.range q = Dynamic.parabolic
      (CommGroupScheme.groupHom s.splitComponentCocharacter ≫ a ≫ l ≫ p) := by
    simpa only [← Category.assoc, hLevi] using s.parabolic_eq_splitComponentCocharacter
  have hsM : SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer
      (CommGroupScheme.groupHom s.splitComponentCocharacter ≫ a ≫ l ≫ p) := by
    simpa only [← Category.assoc, hLevi] using s.levi_eq_splitComponentCocharacter
  apply opposite_root_signs_of_rational_parabolic_inf_eq_centralizer
    r.isCompatible.splitComponent.1.isSplitSubtorus.1 (a ≫ l ≫ p)
    r.splitComponentCocharacter s.splitComponentCocharacter
    (fun _ hβ => r.neg_mem_componentRelativeRoots hG hβ)
  · simpa only [Category.assoc] using
      hsM.symm.trans r.levi_eq_splitComponentCocharacter
  · simpa only [Category.assoc, ← r.parabolic_eq_splitComponentCocharacter,
      ← hsP, ← r.levi_eq_splitComponentCocharacter] using hpoints

/-- Every intrinsic positive root of the second parabolic negates to an
intrinsic positive root of the first, on the same specified split component. -/
theorem neg_mem_intrinsicPositiveRoots_of_opposite (hG : IsConnectedReductive G)
    (hLevi : lQ ≫ q = l ≫ p)
    (hpoints : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) ⊓
        (SubgroupFunctor.range q).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)))
    {β : characterLattice A} (hβ : β ∈ s.intrinsicPositiveRoots) :
    -β ∈ r.intrinsicPositiveRoots := by
  have hβ' : β ∈ relativeRoots (a ≫ l ≫ p) ∧
      0 < latticePairing A β s.splitComponentCocharacter := by
    simpa only [intrinsicPositiveRoots, positiveRelativeRoots, Set.mem_ofPred_eq,
      ← Category.assoc, hLevi] using hβ
  refine ⟨r.neg_mem_componentRelativeRoots hG hβ'.1, ?_⟩
  simpa only [map_neg, LinearMap.neg_apply, neg_pos] using
    ((r.opposite_componentRoot_signs s hG hLevi hpoints β hβ'.1).2.mp hβ'.2)

/-- Negating a vector in the second parabolic cone puts it in the first
parabolic cone under the exact rational opposition hypotheses. -/
theorem neg_mem_nonnegCone_of_opposite (hG : IsConnectedReductive G)
    (hLevi : lQ ≫ q = l ≫ p)
    (hpoints : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) ⊓
        (SubgroupFunctor.range q).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)))
    {x : Vstar A} (hx : x ∈ s.nonnegCone) : -x ∈ r.nonnegCone := by
  classical
  obtain ⟨c, hc, rfl⟩ := (RootCombination.mem_nonneg s.finite_restrictedRoots).mp hx
  rw [← Finset.sum_neg_distrib]
  change ∑ β ∈ s.finite_restrictedRoots.toFinset, -(c β • β) ∈
    RootCombination.nonnegCone r.finite_restrictedRoots
  apply Submodule.sum_mem
  intro β hβ
  obtain ⟨α, hα, hαJ, rfl⟩ := s.mem_restrictedRoots.mp
    (s.finite_restrictedRoots.mem_toFinset.mp hβ)
  have hneg := r.neg_mem_intrinsicPositiveRoots_of_opposite s hG hLevi hpoints
    (s.restrict_mem_intrinsicPositiveRoots hα hαJ)
  have hcone := r.one_tmul_mem_nonnegCone_of_mem_intrinsicPositiveRoots
    (relativeRootNegation k G hG r.data.T r.data.i r.isCompatible.maximalSplit) hneg
  change -(c ((1 : ℝ) ⊗ₜ[ℤ] (s.data.f ≫ α)) •
    (1 : ℝ) ⊗ₜ[ℤ] (s.data.f ≫ α)) ∈ r.nonnegCone
  simpa only [tmul_neg, smul_neg] using r.smul_mem_nonnegCone
    (hc _ (s.finite_restrictedRoots.mem_toFinset.mp hβ)) hcone

/-- The two cones are exact negatives under the rational opposition hypotheses. -/
theorem mem_nonnegCone_iff_neg_mem_of_opposite (hG : IsConnectedReductive G)
    (hLevi : lQ ≫ q = l ≫ p)
    (hpoints : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) ⊓
        (SubgroupFunctor.range q).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)))
    {x : Vstar A} : x ∈ s.nonnegCone ↔ -x ∈ r.nonnegCone := by
  constructor
  · exact r.neg_mem_nonnegCone_of_opposite s hG hLevi hpoints
  · intro hx
    have hpoints' : (SubgroupFunctor.range q).carrier (Over.mk (𝟙 _)) ⊓
        (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) =
        (SubgroupFunctor.range (lQ ≫ q)).carrier (Over.mk (𝟙 _)) := by
      simpa only [inf_comm, hLevi] using hpoints
    simpa only [neg_neg] using
      s.neg_mem_nonnegCone_of_opposite r hG hLevi.symm hpoints' hx

/-- Negation identifies the vectors in the second cone with those in the first. -/
def oppositeNonnegConeEquiv (hG : IsConnectedReductive G)
    (hLevi : lQ ≫ q = l ≫ p)
    (hpoints : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) ⊓
        (SubgroupFunctor.range q).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _))) :
    s.nonnegCone ≃ r.nonnegCone where
  toFun x := ⟨-x.val, r.neg_mem_nonnegCone_of_opposite s hG hLevi hpoints x.property⟩
  invFun x := ⟨-x.val, (r.mem_nonnegCone_iff_neg_mem_of_opposite s hG hLevi hpoints).mpr
    (by simpa only [neg_neg] using x.property)⟩
  left_inv x := Subtype.ext (neg_neg x.val)
  right_inv x := Subtype.ext (neg_neg x.val)

end Langlands.GroupScheme.ParabolicRootPresentation
