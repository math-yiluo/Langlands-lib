import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianWeightPairing
import Langlands.GroupScheme.SimplyConnected.RankOneOuterAHermitianModel

/-! # Exact endpoint marking for rank-one outer type A -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace TypeAHermitianTorusCoordinates

open Matrix

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData G} {n : ℕ} {e : d.Vertex ≃ Fin n}
  (p : TypeAHermitianTorusCoordinates L d e)

/-- Nonsingularity supplies a nonzero entry in every actual Gram row. -/
theorem exists_gram_ne_zero (i : Fin (n + 1)) :
    ∃ j, p.form.gram i j ≠ 0 := by
  classical
  by_contra! hz
  have hinv : (p.form.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L) *
      ((p.form.gram⁻¹ : GeneralLinearGroup (Fin (n + 1)) L) : Matrix _ _ L) = 1 := by
    exact p.form.gram.val_inv
  have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) L => M i i) hinv
  simp [Matrix.mul_apply, hz] at h

/-- Every actual coordinate has an opposite-weight partner. -/
theorem exists_opposite_weight (ν : cocharacterLattice d.splitTorus)
    (i : Fin (n + 1)) :
    ∃ j, latticePairing d.splitTorus (p.weights i) ν +
      latticePairing d.splitTorus (p.weights j) ν = 0 := by
  obtain ⟨j, hj⟩ := p.exists_gram_ne_zero i
  refine ⟨j, ?_⟩
  by_contra h
  exact hj (p.gram_eq_zero_of_weight_sum_ne ν i j h)

/-- A distinguished root forces the greatest coordinate weight to be positive. -/
theorem first_weight_pos_of_distinguished (a : d.distinguishedVertices) :
    0 < d.weightValues p.weights 0 := by
  have hanti := d.weightValues_antitone e p.weights p.root_coordinates
  let j := e a.val
  have hstep := d.simpleRestriction_pairing_pos a.val a.property
  have heq : e.symm j = a.val := e.symm_apply_apply a.val
  rw [← heq, ← d.weightValues_sub e p.weights p.root_coordinates j] at hstep
  by_contra! htop
  have hnonpos (k : Fin (n + 1)) : d.weightValues p.weights k ≤ 0 :=
    le_trans (hanti (Fin.zero_le k)) htop
  have hneg : d.weightValues p.weights j.succ < 0 := by
    have := hnonpos j.castSucc
    omega
  obtain ⟨k, hk⟩ := p.exists_opposite_weight d.positiveCocharacter j.succ
  change d.weightValues p.weights j.succ + d.weightValues p.weights k = 0 at hk
  have := hnonpos k
  omega

include p in
/-- At split rank one the first numbered root is distinguished. -/
theorem first_mem_distinguishedVertices (hrank : splitRank G = 1) (hn : 0 < n) :
    e.symm ⟨0, hn⟩ ∈ d.distinguishedVertices := by
  classical
  let j : Fin n := ⟨0, hn⟩
  have hpos := p.first_weight_pos_of_distinguished (d.rankOneDistinguishedVertex hrank)
  by_contra hfirst
  have hzero : d.rootRestriction (e.symm j).val = 0 := by
    simpa only [TitsIndexData.distinguishedVertices, TitsIndexData.zeroVertices,
      Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using hfirst
  have hsub := d.weightValues_sub e p.weights p.root_coordinates j
  rw [hzero, map_zero, LinearMap.zero_apply] at hsub
  have hpos' : 0 < latticePairing d.splitTorus (p.weights j.succ) d.positiveCocharacter := by
    change 0 < d.weightValues p.weights j.succ
    change d.weightValues p.weights 0 - d.weightValues p.weights j.succ = 0 at hsub
    omega
  have hbound := p.two_le_splitRank_of_positive_pair d.positiveCocharacter 0 j.succ
    (by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega) hpos hpos'
  rw [hrank] at hbound
  norm_num at hbound

end TypeAHermitianTorusCoordinates

namespace TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) {n : ℕ}

/-- A first endpoint and the full reversal star image identify every marked vertex. -/
theorem mem_distinguishedVertices_iff_endpoints (hrank : splitRank G = 1)
    (e : d.Vertex ≃ Fin n) (hstar : d.StarImagePair e Fin.revPerm)
    (hn : 0 < n) (hfirst : e.symm ⟨0, hn⟩ ∈ d.distinguishedVertices)
    (a : d.Vertex) :
    a ∈ d.distinguishedVertices ↔ (e a).val = 0 ∨ (e a).val + 1 = n := by
  let first : d.distinguishedVertices := ⟨e.symm ⟨0, hn⟩, hfirst⟩
  have horbit : a ∈ d.distinguishedVertices ↔
      ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ first.val = a := by
    constructor
    · intro ha
      exact d.exists_star_eq_of_rank_one hrank first ⟨a, ha⟩
    · rintro ⟨σ, rfl⟩
      change d.star σ first.val ∉ d.zeroVertices
      exact fun hz => first.property ((titsIndexStarInvariant K G d σ _).mp hz)
  have hf : e first.val = ⟨0, hn⟩ := e.apply_symm_apply _
  rw [horbit]
  constructor
  · rintro ⟨σ, rfl⟩
    rcases hstar.2.1 σ with hid | hrev
    · left
      rw [hid first.val, hf]
    · right
      rw [hrev first.val, hf]
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
  · intro ha
    rcases ha with ha | ha
    · refine ⟨1, ?_⟩
      rw [d.star_one]
      apply e.injective
      rw [hf]
      exact Fin.ext ha.symm
    · obtain ⟨σ, hσ⟩ := hstar.2.2
      refine ⟨σ, ?_⟩
      apply e.injective
      rw [hσ, hf]
      apply Fin.ext
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The exact local rank-one outer-A alternative, including full star action. -/
theorem hasRankOneOuterAIndex_of_outer_type_A
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hnot : ¬ d.StarIsTrivial) (hrank : splitRank G = 1) :
    d.HasRankOneOuterAIndex n := by
  classical
  have hstar := d.starImagePair_of_A e hA hnot
  let := hstar.isQuadraticExtension
  let := hstar.isGalois
  let p := d.hermitianTorusCoordinatesOfUnitarySplitting e hstar
    (Algebra.CentralSimple.unitaryDivisionSplitting K (localUnitaryDivisionCommutative K))
    hsc haas hA
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hstar.two_le
  have hfirst := p.first_mem_distinguishedVertices hrank hn
  exact ⟨d.rank_one_outer_A_rank_bounds hsc haas e hA hnot hrank,
    e, ⟨hA, d.mem_distinguishedVertices_iff_endpoints hrank e hstar hn hfirst⟩, hstar⟩

/-- Choose a numbering with the proved exact outer-A marking and full star action. -/
def localOuterARankOneNumbering
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hnot : ¬ d.StarIsTrivial) (hrank : splitRank G = 1) :
    {f : d.Vertex ≃ Fin n //
      d.IsNumberingOf (CartanMatrix.A n) (fun i => i.val = 0 ∨ i.val + 1 = n) f ∧
        d.StarImagePair f Fin.revPerm} :=
  ⟨Classical.choose (d.hasRankOneOuterAIndex_of_outer_type_A hsc haas e hA hnot hrank).2,
    Classical.choose_spec (d.hasRankOneOuterAIndex_of_outer_type_A hsc haas e hA hnot hrank).2⟩

end TitsIndexData

end Langlands.GroupScheme
