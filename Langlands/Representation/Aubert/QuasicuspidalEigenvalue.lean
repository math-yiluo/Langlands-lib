import Langlands.Representation.Aubert.InductionCommutationProof
import Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetProof
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.Representation.Smooth.IrreducibleGrothendieckProof

/-! Quasicuspidal classes and their induced classes are Aubert eigenvectors. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric Parabolic SmoothRep CuspidalSupport
open CuspidalSupport.MinimalRefinedJacquet

universe uF uV

section Geometry

variable {R : Type uF} [Field R] {n : ℕ} (B : BlockShape n)

/-- The refinement with one inner block per outer block is the whole parabolic. -/
theorem wholeRefinement_refinedParabolic_eq_top :
    refinedParabolic R B (wholeRefinement B) = ⊤ := by
  apply top_unique
  intro g _
  rw [mem_refinedParabolic]
  intro i
  rw [(wholeRefinement B i).singleBlock_parabolic_eq_top rfl R]
  trivial

private theorem blockShape_eq_of_length_size {m : ℕ} {A C : BlockShape m}
    (hl : A.length = C.length)
    (hs : ∀ i, A.size i = C.size (Fin.cast hl i)) : A = C := by
  rcases A with ⟨l, s, hp, ht⟩
  rcases C with ⟨l', s', hp', ht'⟩
  dsimp only at hl hs
  subst hl
  have he : s = s' := funext hs
  subst he
  rfl

/-- There is only one refinement whose parabolic is the whole product Levi. -/
theorem eq_wholeRefinement_of_refinedParabolic_eq_top (S : BlockRefinement B)
    (hS : refinedParabolic R B S = ⊤) : S = wholeRefinement B := by
  have hfull := refinedLevi_eq_top_of_refinedParabolic_eq_top B S hS
  funext i
  have hsub := block_indices_subsingleton_of_parabolic_eq_top (S i)
    (innerParabolic_eq_top_of_full B S hfull i)
  have hle : (S i).length ≤ 1 := by
    simpa using (Fintype.card_le_one_iff_subsingleton.mpr hsub)
  have hne : (S i).length ≠ 0 := by
    intro hz
    have : IsEmpty (Fin (S i).length) := hz ▸ inferInstance
    have hs := (S i).sum_eq
    have hzero : B.size i = 0 := by simpa using hs.symm
    exact (Nat.ne_of_gt (B.positive i)) hzero
  have hl : (S i).length = 1 := by omega
  apply blockShape_eq_of_length_size hl
  intro j
  exact (S i).singleBlock_size hl j

/-- The surviving refinement has precisely the sign of the quasicuspidal support. -/
theorem refinementSignExponent_wholeRefinement :
    refinementSignExponent B (wholeRefinement B) = n - B.length := by
  rw [refinementSignExponent_eq]
  simp only [wholeRefinement, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

end Geometry

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n)

/-- Evaluation and the trivial coinvariant quotient identify the actual
whole-refinement induction-after-Jacquet object with its input. -/
def wholeRefinementInductionJacquetEquiv :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier),
      ((T.normalizedRefinedInductionFunctor B (wholeRefinement B)).obj
        ((T.normalizedRefinedJacquetFunctor B (wholeRefinement B)).obj A)).representation.Equiv
          A.representation := by
  letI := T.topology
  intro A
  have hfull : refinedLevi F.Carrier B (wholeRefinement B) = ⊤ :=
    refinedLevi_eq_top_of_refinedParabolic_eq_top B _
      (wholeRefinement_refinedParabolic_eq_top (R := F.Carrier) B)
  exact fullRefinedInductionEquiv T B (wholeRefinement B) hfull
    ((T.normalizedRefinedJacquetFunctor B (wholeRefinement B)).obj A).representation
    A.representation (fullRefinedJacquetEquiv T B _ hfull A.representation) A.isSmooth

set_option maxHeartbeats 1200000 in
/-- The actual full-refinement induction-after-Jacquet map is the identity. -/
theorem refinedInductionJacquetK0_wholeRefinement :
    letI := T.topology
    (normalizedRefinedInductionK0.{uF, uV} F T B (wholeRefinement B)).comp
        (normalizedRefinedJacquetK0.{uF, uV} F T B (wholeRefinement B)) =
      LinearMap.id := by
  let := T.topology
  apply FiniteLengthGrothendieckGroup.hom_ext_object
  intro A
  change normalizedRefinedInductionK0 F T B (wholeRefinement B)
      (normalizedRefinedJacquetK0 F T B (wholeRefinement B)
        (B.finiteLengthClass F.Carrier A.val A.property)) =
    B.finiteLengthClass F.Carrier A.val A.property
  have h := normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T
  have hJ := h.2.1 n B (wholeRefinement B) A.val A.property
  have hI := h.1 n B (wholeRefinement B) _ hJ
  rw [normalizedRefinedJacquetK0_finiteLengthClass F T B _ A.val A.property hJ,
    normalizedRefinedInductionK0_finiteLengthClass F T B _ _ hJ hI]
  exact FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv hI A.property
    (wholeRefinementInductionJacquetEquiv F T B A.val)

/-- A proper refined Jacquet map kills a finite-length quasicuspidal class. -/
theorem normalizedRefinedJacquetK0_quasicuspidal (S : BlockRefinement B) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier))
      (hA : A.HasFiniteLength),
      IsLeviQuasicuspidal B A.representation →
      refinedParabolic F.Carrier B S ≠ ⊤ →
      normalizedRefinedJacquetK0.{uF, uV} F T B S
        (B.finiteLengthClass F.Carrier A hA) = 0 := by
  let := T.topology
  intro A hA hqc hS
  have hJ := (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).2.1
    n B S A hA
  rw [normalizedRefinedJacquetK0_finiteLengthClass F T B S A hA hJ]
  have : Subsingleton ((T.normalizedRefinedJacquetFunctor B S).obj A).obj := hqc S hS
  exact IrreducibleGrothendieckProof.ofRepresentation_eq_zero_of_subsingleton _ _

/-- Only the whole refinement survives on a finite-length quasicuspidal class. -/
theorem alternatingOperatorOnLevi_quasicuspidal :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier))
      (hA : A.HasFiniteLength),
      IsLeviQuasicuspidal B A.representation →
      alternatingOperatorOnLevi.{uF, uV} F T B
          (B.finiteLengthClass F.Carrier A hA) =
        ((-1 : ℤ) ^ (n - B.length)) • B.finiteLengthClass F.Carrier A hA := by
  let := T.topology
  intro A hA hqc
  classical
  let : Fintype (BlockRefinement B) := Fintype.ofFinite _
  rw [alternatingOperatorOnLevi_apply]
  rw [Finset.sum_eq_single (wholeRefinement B)]
  · rw [refinementSignExponent_wholeRefinement]
    have he := LinearMap.congr_fun
      (refinedInductionJacquetK0_wholeRefinement.{uF, uV} F T B)
      (B.finiteLengthClass F.Carrier A hA)
    change normalizedRefinedInductionK0 F T B (wholeRefinement B)
      (normalizedRefinedJacquetK0 F T B (wholeRefinement B)
        (B.finiteLengthClass F.Carrier A hA)) = B.finiteLengthClass F.Carrier A hA at he
    rw [he]
  · intro S _ hS
    have hproper : refinedParabolic F.Carrier B S ≠ ⊤ := by
      intro hfull
      exact hS (eq_wholeRefinement_of_refinedParabolic_eq_top B S hfull)
    rw [normalizedRefinedJacquetK0_quasicuspidal F T B S A hA hqc hproper,
      map_zero, smul_zero]
  · simp

/-- Induction commutation gives the same eigenvalue on the induced exact class. -/
theorem alternatingOperator_normalizedInductionK0_quasicuspidal :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier))
      (hA : A.HasFiniteLength),
      IsLeviQuasicuspidal B A.representation →
      alternatingOperator.{uF, uV} F T n
          (normalizedInductionK0.{uF, uV} F T B (B.finiteLengthClass F.Carrier A hA)) =
        ((-1 : ℤ) ^ (n - B.length)) •
          normalizedInductionK0.{uF, uV} F T B (B.finiteLengthClass F.Carrier A hA) := by
  let := T.topology
  intro A hA hqc
  have h := LinearMap.congr_fun (inductionCommutation.{uF, uV} F T n B)
    (B.finiteLengthClass F.Carrier A hA)
  change alternatingOperator F T n
      (normalizedInductionK0 F T B (B.finiteLengthClass F.Carrier A hA)) =
    normalizedInductionK0 F T B
      (alternatingOperatorOnLevi F T B (B.finiteLengthClass F.Carrier A hA)) at h
  rw [alternatingOperatorOnLevi_quasicuspidal F T B A hA hqc, map_smul] at h
  exact h

end Langlands.Aubert
