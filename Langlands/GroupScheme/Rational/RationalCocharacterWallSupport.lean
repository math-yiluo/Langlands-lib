import Langlands.GroupScheme.Rational.RationalCocharacterRealization
import Langlands.GroupScheme.Rational.RootOrthogonalCentralizer
import Langlands.GroupScheme.Rational.RelativeRankOneParabolicMaximality
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry

/-! # Actual root support at a rational chamber wall -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan
open Langlands.LinearAlgebra.FiniteHyperplaneSegment
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RationalCocharacter

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- The actual finite root arrangement on rational cocharacter directions. -/
abbrev rootForms (i : A.toGrp ⟶ G) :=
  fun α : relativeRoots i => rootForm (α : characterLattice A)

/-- A rational wall direction with regular endpoints, opposite signs on its
zero roots, equal signs elsewhere, and proportional vanishing root forms. -/
structure IsWallDirection (i : A.toGrp ⟶ G) (x y w : Space A) : Prop where
  regular : Regular (rootForms i) x
  regular' : Regular (rootForms i) y
  root : ∃ α ∈ relativeRoots i, w (toRat α) = 0
  opposite : ∀ α ∈ relativeRoots i, w (toRat α) = 0 →
    x (toRat α) * y (toRat α) < 0
  same : ∀ α ∈ relativeRoots i, w (toRat α) ≠ 0 →
    0 < x (toRat α) * w (toRat α) ∧ 0 < y (toRat α) * w (toRat α)
  proportional : ∀ α ∈ relativeRoots i, ∀ β ∈ relativeRoots i,
    w (toRat α) = 0 → w (toRat β) = 0 →
      ∃ c : ℚ, c ≠ 0 ∧ rootForm β = c • rootForm α

/-- The finite-arrangement witness gives a wall direction and retains every
protected nonvanishing form. -/
theorem exists_isWallDirection_of_wallAdjacent {i : A.toGrp ⟶ G}
    {keep : relativeRoots i → Prop} {x y : Space A}
    (h : WallAdjacent (rootForms i) keep x y) :
    ∃ w : Space A, IsWallDirection i x y w ∧
      ∀ α : relativeRoots i, keep α → w (toRat (α : characterLattice A)) ≠ 0 := by
  obtain ⟨hx, hy, w, hw, hopp, hsame, hprop, hkeep⟩ := h
  refine ⟨w, ⟨hx, hy, ?_, ?_, ?_, ?_⟩, hkeep⟩
  · obtain ⟨α, hα⟩ := hw
    exact ⟨α, α.property, hα⟩
  · intro α hα
    exact hopp ⟨α, hα⟩
  · intro α hα
    exact hsame ⟨α, hα⟩
  · intro α hα β hβ
    exact hprop ⟨α, hα⟩ ⟨β, hβ⟩

namespace IsWallDirection

variable {i : A.toGrp ⟶ G} {x y w : Space A} (h : IsWallDirection i x y w)

include h

/-- Reversing the endpoints preserves the wall direction. -/
theorem symm : IsWallDirection i y x w where
  regular := h.regular'
  regular' := h.regular
  root := h.root
  opposite α hα hz := by simpa only [mul_comm] using h.opposite α hα hz
  same α hα hz := (h.same α hα hz).symm
  proportional := h.proportional

/-- An endpoint nonnegative root is nonnegative on the wall. -/
theorem nonnegative_wall {α : characterLattice A} (hα : α ∈ relativeRoots i)
    (hx : 0 ≤ x (toRat α)) : 0 ≤ w (toRat α) := by
  by_cases hz : w (toRat α) = 0
  · exact hz.ge
  have hp := (h.same α hα hz).1
  have hx' : 0 < x (toRat α) :=
    lt_of_le_of_ne hx (Ne.symm (h.regular ⟨α, hα⟩))
  exact (pos_of_mul_pos_right hp hx'.le).le

section Ambient

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- Both endpoint parabolics lie in the wall parabolic on every test scheme. -/
theorem parabolic_le (hA : IsSplitTorus A.toGrp) :
    parabolic hA i x ≤ parabolic hA i w ∧
      parabolic hA i y ≤ parabolic hA i w :=
  ⟨(parabolic_le_iff hA i).2 fun _ hα => h.nonnegative_wall hα,
    (parabolic_le_iff hA i).2 fun _ hα => h.symm.nonnegative_wall hα⟩

end Ambient

section Represented

variable [LocallyOfFiniteType G.X.hom]
  [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
  (r : IntegralRealization w) {j : M ⟶ G}
  (hj : (Dynamic.centralizer (CommGroupScheme.groupHom r.cocharacter ≫ i)).IsRepresentedBy j)
  (iM : A.toGrp ⟶ M) (hiM : iM ≫ j = i)

include hj hiM

omit h in
/-- The wall centralizer has exactly the ambient actual roots vanishing on
the rational wall direction. -/
theorem mem_relativeRoots_iff {α : characterLattice A} :
    α ∈ relativeRoots iM ↔ α ∈ relativeRoots i ∧ w (toRat α) = 0 := by
  constructor
  · intro hα
    exact ⟨relativeRoots_subset_of_factor hj iM hiM hα,
      (r.pairing_eq_zero_iff α).1
        (relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer hj iM hiM
          r.cocharacter le_rfl hα)⟩
  · rintro ⟨hα, hz⟩
    exact mem_relativeRoots_of_pairing_eq_zero i r.cocharacter hj iM hiM
      hα ((r.pairing_eq_zero_iff α).2 hz)

include h

/-- Proportional wall forms give proportional integral root pairings in the
actual wall centralizer, on the original torus. -/
theorem proportional_pairings : HasProportionalRootPairings iM := by
  intro α hα β hβ ν eta
  obtain ⟨hαG, hαw⟩ := (mem_relativeRoots_iff r hj iM hiM).1 hα
  obtain ⟨hβG, hβw⟩ := (mem_relativeRoots_iff r hj iM hiM).1 hβ
  obtain ⟨c, -, hc⟩ := h.proportional α hαG β hβG hαw hβw
  have hν := congrArg (fun f : Module.Dual ℚ (Space A) => f (rationalCocharacterEvaluation ν)) hc
  have heta := congrArg (fun f : Module.Dual ℚ (Space A) => f (rationalCocharacterEvaluation eta)) hc
  simp only [rootForm_apply, rationalCocharacterEvaluation_toRat, LinearMap.smul_apply, smul_eq_mul] at hν heta
  have heq : (latticePairing A α ν : ℚ) * (latticePairing A β eta : ℚ) =
      (latticePairing A β ν : ℚ) * (latticePairing A α eta : ℚ) := by
    rw [hν, heta]
    ring
  exact_mod_cast heq

/-- Endpoint sign reversal identifies the second inner parabolic with the
opposite of the first, using arbitrary positive integral realizations. -/
theorem parabolic_eq_opposite (hA : IsSplitTorus A.toGrp)
    (hM : IsConnectedReductive M) (s : IntegralRealization x) (t : IntegralRealization y) :
    Dynamic.parabolic (CommGroupScheme.groupHom t.cocharacter ≫ iM) =
      Dynamic.parabolic (CommGroupScheme.groupHom (-s.cocharacter) ≫ iM) := by
  let : Smooth M.X.hom := hM.smooth
  let : ConnectedSpace M.X.left := hM.connectedSpace
  have hsign (α : characterLattice A) (hα : α ∈ relativeRoots iM) :
      0 ≤ latticePairing A α t.cocharacter ↔
        0 ≤ latticePairing A α (-s.cocharacter) := by
    obtain ⟨hαG, hαw⟩ := (mem_relativeRoots_iff r hj iM hiM).1 hα
    have hopp := h.opposite α hαG hαw
    rw [t.pairing_nonneg_iff, map_neg, neg_nonneg]
    have hs := s.pairing_nonneg_iff α
    have hspos := s.pairing_pos_iff α
    rcases mul_neg_iff.mp hopp with hp | hp
    · exact iff_of_false (not_le_of_gt hp.2)
        (not_le_of_gt (hspos.mpr hp.1))
    · have hsn : latticePairing A α s.cocharacter < 0 :=
        lt_of_not_ge (fun hn => (not_le_of_gt hp.1) (hs.mp hn))
      exact iff_of_true hp.2.le hsn.le
  apply le_antisymm
  · exact (RelativeRoot.parabolic_le_iff_nonnegative_rootSupport
      dynamicConnected hA iM _ _).2 fun α hα => (hsign α hα).1
  · exact (RelativeRoot.parabolic_le_iff_nonnegative_rootSupport
      dynamicConnected hA iM _ _).2 fun α hα => (hsign α hα).2

/-- The actual inner endpoint parabolic is proper in the wall centralizer. -/
theorem parabolic_ne_top (hM : IsConnectedReductive M) (s : IntegralRealization x) :
    Dynamic.parabolic (CommGroupScheme.groupHom s.cocharacter ≫ iM) ≠ ⊤ := by
  let : Smooth M.X.hom := hM.smooth
  let : ConnectedSpace M.X.left := hM.connectedSpace
  intro htop
  obtain ⟨α, hα, hαw⟩ := h.root
  have hαM : α ∈ relativeRoots iM :=
    (mem_relativeRoots_iff r hj iM hiM).2 ⟨hα, hαw⟩
  have hc : IsCentral (CommGroupScheme.groupHom s.cocharacter ≫ iM) :=
    (isCentral_iff_dynamicCentralizer_eq_top _).2
      ((Dynamic.parabolic_eq_top_iff_centralizer_eq_top
        hM.hasTrivialUnipotentRadical _).1 htop)
  have hz := root_restrict_eq_zero_of_isCentral iM s.cocharacter isSplitTorus_gm hc hαM
  have hzero : latticePairing A α s.cocharacter = 0 := by
    simp only [latticePairing_apply, hz, map_zero]
  exact h.regular ⟨α, hα⟩ ((s.pairing_eq_zero_iff α).1 hzero)

end Represented

end IsWallDirection

end Langlands.GroupScheme.RationalCocharacter
