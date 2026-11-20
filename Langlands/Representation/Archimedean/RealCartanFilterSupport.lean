import Langlands.Representation.Archimedean.RealCartanActiveBlocks
import Langlands.Representation.Archimedean.RealStandardCompactTestTrace

/-! # Support of the compact Fourier projection at a real Cartan -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean.RealCartanFilterSupport

open Langlands.LocalFactor.Archimedean GramFormula PrincipalSeriesExtension
  RealInducedBlockBound RealInducedStandardBound
  RealStandardCompactAverage RealCartanCompactSupport RealCartanActiveBlocks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "Mat" k:max => Matrix (Fin k) (Fin k) ℝ
local notation "K" k:max => Matrix.unitaryGroup (Fin k) ℝ
local notation "G" k:max => Langlands.GeneralLinear k ℝ

variable {n : ℕ}

/-- The normalized finite low-mode projection at one rotation slot. -/
def lowProjection (s : Slot n) : Module.End ℂ C(G n, ℂ) :=
  (2 * (Real.pi : ℂ))⁻¹ • ∑ j ∈ lowModes s.M, coefficientMap s.p j

theorem lowProjection_apply (s : Slot n) (f : C(G n, ℂ)) (x : G n) :
    lowProjection s f x = (2 * (Real.pi : ℂ))⁻¹ *
      ∑ j ∈ lowModes s.M, blockFourierCoefficient n s.p j f x := by
  let E : C(G n, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ x
  change E (lowProjection s f) = _
  simp only [lowProjection, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rfl

/-- Compose the low-mode projections at all selected slots. -/
def lowProjections (S : List (Slot n)) : Module.End ℂ C(G n, ℂ) :=
  S.foldr (fun s A => (lowProjection s).comp A) LinearMap.id

@[simp]
theorem lowProjections_nil (f : C(G n, ℂ)) : lowProjections [] f = f := rfl

@[simp]
theorem lowProjections_cons (s : Slot n) (S : List (Slot n)) (f : C(G n, ℂ)) :
    lowProjections (s :: S) f = lowProjection s (lowProjections S f) := rfl

private theorem highModesList_eq_low_of_sublist (f : C(G n, ℂ)) (S : List (Slot n))
    (ℓ : C(G n, ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ T : List (Slot n), List.Sublist T S → T.length < S.length → ℓ (lowProjections T f) = 0) :
    ℓ (highModesList S f) = (-1 : ℂ) ^ S.length * ℓ (lowProjections S f) := by
  induction S generalizing ℓ with
  | nil => simp
  | cons s S ih =>
    have htail (T : List (Slot n)) (hT : List.Sublist T S) : ℓ (lowProjections T f) = 0 :=
      h T (hT.cons s) (by simpa using Nat.lt_succ_of_le hT.length_le)
    have hhead (T : List (Slot n)) (hT : List.Sublist T S) (hlt : T.length < S.length) :
        (ℓ.comp (lowProjection s)) (lowProjections T f) = 0 :=
      h (s :: T) (hT.cons_cons s) (by simpa using hlt)
    have hzero : ℓ (highModesList S f) = 0 := by
      rw [ih ℓ (fun T hT _ => htail T hT), htail S (List.Sublist.refl S), mul_zero]
    rw [highModesList_cons, show highModes s.p s.M = LinearMap.id - lowProjection s from rfl,
      LinearMap.sub_apply, LinearMap.id_apply, map_sub, hzero]
    change 0 - (ℓ.comp (lowProjection s)) (highModesList S f) = _
    rw [ih _ hhead, zero_sub, List.length_cons, lowProjections_cons,
      LinearMap.comp_apply, pow_succ]
    ring

private def blocksOfSlots (S : List (Slot n)) (hS : S.Pairwise Slot.Disjoint) : ActiveBlocks n where
  starts := (S.map Slot.p).toFinset
  next_lt := by
    intro p hp
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    exact s.hp
  disjoint := by
    intro p hp hsucc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    obtain ⟨t, ht, hst⟩ := List.mem_map.mp (List.mem_toFinset.mp hsucc)
    have hsymm : Std.Symm (Slot.Disjoint (N := n)) := ⟨fun _ _ h => h.symm⟩
    have hne : s ≠ t := by
      intro he
      rw [he] at hst
      omega
    have hd := hS.forall hs ht hne
    unfold Slot.Disjoint at hd
    omega

private theorem starts_card (S : List (Slot n)) (hS : S.Pairwise Slot.Disjoint) :
    (blocksOfSlots S hS).starts.card = S.length := by
  have hnodup : (S.map Slot.p).Nodup := by
    change (S.map Slot.p).Pairwise (· ≠ ·)
    rw [List.pairwise_map]
    refine hS.imp ?_
    intro s t hst
    unfold Slot.Disjoint at hst
    omega
  rw [blocksOfSlots, List.toFinset_card_of_nodup hnodup, List.length_map]

private theorem signFilters_preserve_vanishing (A : ActiveBlocks n) (ds : List RealBlock)
    (I : List (Fin n)) (f : C(G n, ℂ)) (x : K n)
    (h : ∀ u ∈ A.compactSubgroup, f (Unitary.toUnits (u * x)) = 0) :
    ∀ u ∈ A.compactSubgroup, signFilters ds I f (Unitary.toUnits (u * x)) = 0 := by
  induction I with
  | nil => exact h
  | cons i I ih =>
    intro u hu
    have hσ := ih (signReflection n i * u)
      (A.compactSubgroup.mul_mem (A.signReflection_mem i) hu)
    rw [signFilters_cons, signFilter_apply, ih u hu, ← map_mul, ← mul_assoc,
      hσ, mul_zero, add_zero, mul_zero]

private theorem lowProjections_preserve_vanishing (A : ActiveBlocks n) (S : List (Slot n))
    (hS : ∀ s ∈ S, s.p ∈ A.starts) (f : C(G n, ℂ)) (x : K n)
    (h : ∀ u ∈ A.compactSubgroup, f (Unitary.toUnits (u * x)) = 0) :
    ∀ u ∈ A.compactSubgroup, lowProjections S f (Unitary.toUnits (u * x)) = 0 := by
  induction S with
  | nil => exact h
  | cons s S ih =>
    intro u hu
    have hs := hS s List.mem_cons_self
    have htail := ih fun t ht => hS t (List.mem_cons_of_mem s ht)
    rw [lowProjections_cons, lowProjection_apply]
    suffices he : (∑ j ∈ lowModes s.M, blockFourierCoefficient n s.p j (lowProjections S f)
        (Unitary.toUnits (u * x))) = 0 by rw [he, mul_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold blockFourierCoefficient
    have hθ (θ : ℝ) : lowProjections S f (blockRotation n s.p θ * Unitary.toUnits (u * x)) = 0 := by
      have heq : blockRotation n s.p θ * Unitary.toUnits (u * x) =
          Unitary.toUnits ((ActiveBlocks.rotation n s.p θ * u) * x) := by
        simp only [map_mul, ActiveBlocks.toUnits_rotation, mul_assoc]
      rw [heq]
      exact htail _ (A.compactSubgroup.mul_mem (A.rotation_mem s.p hs θ) hu)
    simp_rw [hθ, zero_mul, intervalIntegral.integral_zero]

private theorem signedOrthogonalPart_toUnits (u : K n) : signedOrthogonalPart (Unitary.toUnits u) = u := by
  apply Subtype.ext
  change signedOrthogonal (u : Mat n) = (u : Mat n)
  have hm : (u : Mat n) * (u : Mat n)ᵀ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mem_unitaryGroup_iff.mp u.2)
  have h := signedOrthogonal_mul (b := (1 : Mat n)) (κ := (u : Mat n))
    Matrix.blockTriangular_one (fun _ => by simp) hm
  simpa [signReal] using h

private theorem lowProjections_column_eq_zero (ds : List RealBlock) (g : G n)
    (S : List (Slot n)) (hS : S.Pairwise Slot.Disjoint)
    (φ : C(K n, ℂ)) (y : K n)
    (h : ∀ u ∈ (blocksOfSlots S hS).compactSubgroup, φ (compactArgument g y u) = 0) :
    lowProjections S (signFilters ds (List.ofFn id) (continuousColumn φ y))
      (Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))) = 0 := by
  let A := blocksOfSlots S hS
  let x := signedOrthogonalPart (Unitary.toUnits y * g)
  have hstart (s : Slot n) (hs : s ∈ S) : s.p ∈ A.starts :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨s, hs, rfl⟩)
  have hcol (u : K n) (hu : u ∈ A.compactSubgroup) :
      continuousColumn φ y (Unitary.toUnits (u * x)) = 0 := by
    rw [continuousColumn_apply, signedOrthogonalPart_toUnits, _root_.mul_inv_rev]
    exact h u hu
  have hzero := lowProjections_preserve_vanishing A S hstart _ x
    (signFilters_preserve_vanishing A ds (List.ofFn id) _ x hcol) 1
      A.compactSubgroup.one_mem
  simpa only [one_mul] using hzero

/-- The compact column integral with the low projection in every rotation slot. -/
def compactLowTrace (μ : Measure (K n)) (ds : List RealBlock) (g : G n) (φ : C(K n, ℂ)) : ℂ :=
  ∫ y, extension (shiftedExponent n (realPositionExponent ds)) 1 (Unitary.toUnits y * g) *
    lowProjections (slots ds n) (signFilters ds (List.ofFn id) (continuousColumn φ y))
      (Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))) ∂μ

/-- At or above the largest Cartan rank of the list, sufficiently concentrated
tests retain only the full low projection. Above that rank even this term
vanishes. -/
def RealCartanFilterSupportStatement (α : Type*) : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (a : Fin n → α) (d : α → ℝ) (g : G n),
    let C := (g : Mat n)
    let r := Nat.card (PairBlock a)
    Function.Surjective a →
    (∀ ⦃i j k⦄, i ≠ j → a i = a j → a k = a i → k = i ∨ k = j) →
    (∀ ⦃i j⦄, a i ≠ a j → C i j = 0) →
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j = - C j i) →
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j ≠ 0) →
    C * Cᵀ = diagonal (d ∘ a) → Function.Injective d → C * Cᵀ = Cᵀ * C →
    (slots ds n).length ≤ r →
    ∃ U : Set (K n), IsOpen U ∧ 1 ∈ U ∧
      ∀ (μ : Measure (K n)) (φ : C(K n, ℂ)), Function.support φ ⊆ U →
        compactTestTrace μ ds g φ = (-1 : ℂ) ^ (slots ds n).length * compactLowTrace μ ds g φ ∧
        ((slots ds n).length < r → compactTestTrace μ ds g φ = 0)

set_option maxHeartbeats 500000 in
theorem realCartanFilterSupport {α : Type*} : RealCartanFilterSupportStatement α := by
  intro n ds a d g C r ha hsize hzero hskew hpair hgram hd hnormal hcount
  classical
  let S := slots ds n
  have hS : S.Pairwise Slot.Disjoint := pairwise_slots ds n
  let subsets := S.sublists.toFinset.filter fun T => T.length < r
  have huniv (T : ↥subsets) :
      ∃ U : Set (K n), IsOpen U ∧ 1 ∈ U ∧
        ∀ φ : C(K n, ℂ), Function.support φ ⊆ U →
          ∀ y : K n, lowProjections T.val (signFilters ds (List.ofFn id) (continuousColumn φ y))
            (Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))) = 0 := by
    have hT := Finset.mem_filter.mp T.2
    have hs : List.Sublist T.val S := List.mem_sublists.mp (List.mem_toFinset.mp hT.1)
    have hp := hS.sublist hs
    have hlt : (blocksOfSlots T.val hp).starts.card < r := by
      rw [starts_card]
      exact hT.2
    obtain ⟨U, hU, hOne, hvan⟩ := realCartanActiveBlocksSupport n (blocksOfSlots T.val hp)
      a d g ha hsize hzero hskew hpair hgram hd hnormal hlt
    exact ⟨U, hU, hOne, fun φ hφ y =>
      lowProjections_column_eq_zero ds g T.val hp φ y (fun u hu => hvan φ hφ y u hu)⟩
  choose U hU hOne hz using huniv
  let V := ⋂ T : ↥subsets, U T
  refine ⟨V, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hOne, fun μ φ hφ => ?_⟩
  have hterm (T : List (Slot n)) (hs : List.Sublist T S) (hlt : T.length < r) (y : K n) :
      lowProjections T (signFilters ds (List.ofFn id) (continuousColumn φ y))
        (Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))) = 0 := by
    have hm : T ∈ subsets :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_sublists.mpr hs), hlt⟩
    exact hz ⟨T, hm⟩ φ (hφ.trans (Set.iInter_subset U ⟨T, hm⟩)) y
  have hfun (y : K n) :
      highModesList S (signFilters ds (List.ofFn id) (continuousColumn φ y))
        (Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))) =
      (-1 : ℂ) ^ S.length * lowProjections S (signFilters ds (List.ofFn id) (continuousColumn φ y))
        (Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))) :=
    highModesList_eq_low_of_sublist _ S (ContinuousMap.evalCLM ℂ _).toLinearMap
      (fun T hs hl => hterm T hs (hl.trans_le hcount) y)
  have hEq : compactTestTrace μ ds g φ = (-1 : ℂ) ^ S.length * compactLowTrace μ ds g φ := by
    rw [compactTestTrace_apply, compactLowTrace, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    let x := Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))
    let F := signFilters ds (List.ofFn id) (continuousColumn φ y)
    let W := extension (shiftedExponent n (realPositionExponent ds)) 1 (Unitary.toUnits y * g)
    change W * highModesList S F x = (-1 : ℂ) ^ S.length * (W * lowProjections S F x)
    rw [show highModesList S F x = (-1 : ℂ) ^ S.length * lowProjections S F x from hfun y]
    ring
  refine ⟨hEq, fun hlt => ?_⟩
  have hlow : compactLowTrace μ ds g φ = 0 := by
    unfold compactLowTrace
    calc
      _ = ∫ _ : K n, (0 : ℂ) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        change _ * lowProjections S (signFilters ds (List.ofFn id) (continuousColumn φ y))
          (Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))) = 0
        rw [hterm S (List.Sublist.refl S) hlt y, mul_zero]
      _ = 0 := by simp
  rw [hEq, hlow, mul_zero]

end Langlands.Archimedean.RealCartanFilterSupport
