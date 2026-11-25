/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeSheafBasic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Neighborhoods on which a continuous matrix has constant lattice coset

Source: Bhatt--Scholze, Proposition 6.8.4(6), local constancy of matrix lattices
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The ring of integral coefficients is an open subring of the rational coefficient field.
Source: Bhatt--Scholze, Proposition 6.8.4(6), openness of integral lattices
(auxiliary; not a blueprint node).
Proof: the ball of radius one around zero lies in the integral ring by the absolute-value
characterization. An additive subgroup containing a neighborhood of zero is open. -/
theorem isOpen_latticeCoefficientIntegers (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsOpen (latticeCoefficientIntegers l E :
      Set (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))) := by
  let K := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  apply (latticeCoefficientIntegers l E).toAddSubgroup.isOpen_of_mem_nhds (g := 0)
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : K) zero_lt_one)
  intro x hx
  apply (Padic.mem_coefficientExtensionIntegers l E _).mpr
  change ‖x‖ ≤ 1
  have hx' : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  exact hx'.le

/-- Continuous matrices and their continuous inverses have locally constant integral coset.
Source: Bhatt--Scholze, Proposition 6.8.4(6), local constancy of matrix lattices
(auxiliary; not a blueprint node).
Proof: near x require every entry of g(x) inverse times g(y), and of its inverse,
to lie in the open integral subring. At x these are the entries of the identity.
The finitely many requirements define an open neighborhood. The integral-entry
criterion then identifies the cosets at every point of that neighborhood.
This uses no choice of a basis index and includes rank zero. -/
theorem continuousMatrixCoset_neighborhood
    {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (A : Subring K) (hA : IsOpen (A : Set K)) (n : ℕ)
    {Y : Type v} [TopologicalSpace Y]
    (g : Y → Matrix.GeneralLinearGroup (Fin n) K)
    (hg : ∀ i j, Continuous (fun y ↦ (g y).val i j))
    (hginv : ∀ i j, Continuous (fun y ↦ ((g y)⁻¹).val i j)) (x : Y) :
    ∃ W : TopologicalSpace.Opens Y, x ∈ W ∧
      ∀ y ∈ W, (Quotient.mk _ (g x) : integralMatrixCosets A n) =
        Quotient.mk _ (g y) := by
  classical
  let p := fun y ↦ (g x)⁻¹ * g y
  let q := fun y ↦ (g y)⁻¹ * g x
  have hp (i j : Fin n) : Continuous (fun y ↦ (p y).val i j) := by
    change Continuous (fun y ↦ ∑ k, ((g x)⁻¹).val i k * (g y).val k j)
    exact continuous_finsetSum _ (fun k _ ↦ continuous_const.mul (hg k j))
  have hq (i j : Fin n) : Continuous (fun y ↦ (q y).val i j) := by
    change Continuous (fun y ↦ ∑ k, ((g y)⁻¹).val i k * (g x).val k j)
    exact continuous_finsetSum _ (fun k _ ↦ (hginv i k).mul continuous_const)
  let W : Set Y := ⋂ i : Fin n, ⋂ j : Fin n,
    {y | (p y).val i j ∈ A} ∩ {y | (q y).val i j ∈ A}
  have hW : IsOpen W := isOpen_iInter_of_finite fun i ↦
    isOpen_iInter_of_finite fun j ↦ (hA.preimage (hp i j)).inter (hA.preimage (hq i j))
  refine ⟨⟨W, hW⟩, ?_, ?_⟩
  · change x ∈ W
    simp only [W, Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
    intro i j
    by_cases hij : i = j <;> simp [p, q, hij]
  · intro y hy
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    apply (integralMatrixSubgroup_mem_iff K A n (p y)).mpr
    refine ⟨fun i j ↦ (Set.mem_iInter.mp (Set.mem_iInter.mp hy i) j).1, ?_⟩
    intro i j
    have h := (Set.mem_iInter.mp (Set.mem_iInter.mp hy i) j).2
    change (q y).val i j ∈ A at h
    simpa only [p, q, mul_inv_rev, inv_inv] using h

end AlgebraicGeometry.ProEtale
