import Langlands.Representation.Aubert.CorrectedOrbitVanishing
import Langlands.Representation.Aubert.WholeTargetBooleanInterval

/-! Actual corrected support activity and the whole-target Boolean interval. -/

noncomputable section

namespace Langlands.Aubert.Support

open GeneralLinear Geometric

variable {n : ℕ}

/-- Reversing a double-coset representative exchanges its source and target
increasing-block conditions. -/
theorem isMinimalRepresentative_symm_iff (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) :
    IsMinimalRepresentative C B w.symm ↔ IsMinimalRepresentative B C w := by
  simp only [IsMinimalRepresentative, Equiv.symm_symm, and_comm]

/-- On a full length tail, actual core membership is precisely minimality. -/
theorem mem_weylSupport_iff_minimal_of_length_tail
    (B C : BlockShape n) (θ : Set (Equiv.Perm (Fin n)))
    (w : Equiv.Perm (Fin n)) (hwθ : w ∈ θ)
    (hTail : ∀ v ∈ θ \ {w}, inversionLength w ≤ inversionLength v)
    (hAbove : ∀ v, inversionLength w < inversionLength v → v ∈ θ) :
    w ∈ weylSupport B C θ ↔ IsMinimalRepresentative B C w :=
  (twoSidedCore_diff_singleton_ne_iff (blockWeyl C) (blockWeyl B) θ w).symm.trans
    (singleton_drop_iff_minimal_of_length_tail B C θ w hwθ hTail hAbove)

/-- Upper closure after removing a point forces that point to have no larger
length than any remaining point. -/
theorem length_le_of_upper_singleton_tail
    (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
    (hLower : ∀ v ∈ θ \ {w}, ∀ z,
      inversionLength v < inversionLength z → z ∈ θ \ {w}) :
    ∀ v ∈ θ \ {w}, inversionLength w ≤ inversionLength v := by
  intro v hv
  by_contra hle
  exact (hLower v hv w (by omega)).2 rfl

/-- The actual upper-support hypotheses already supply the full length tail
needed for the core-membership criterion. -/
theorem mem_weylSupport_iff_minimal_of_upper_singleton
    (B C : BlockShape n) (θ : Set (Equiv.Perm (Fin n)))
    (w : Equiv.Perm (Fin n)) (hwθ : w ∈ θ)
    (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
    (hLower : ∀ v ∈ θ \ {w}, ∀ z,
      inversionLength v < inversionLength z → z ∈ θ \ {w}) :
    w ∈ weylSupport B C θ ↔ IsMinimalRepresentative B C w :=
  mem_weylSupport_iff_minimal_of_length_tail B C θ w hwθ
    (length_le_of_upper_singleton_tail θ w hLower) (hθ w hwθ)

/-- The whole-target part of an actual singleton support step is exactly the
Boolean interval, including the fixed conditions on the inverse permutation. -/
theorem weylSupport_wholeTarget_iff_interval
    (B C : BlockShape n) (θ : Set (Equiv.Perm (Fin n)))
    (w : Equiv.Perm (Fin n)) (hwθ : w ∈ θ)
    (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
    (hLower : ∀ v ∈ θ \ {w}, ∀ z,
      inversionLength v < inversionLength z → z ∈ θ \ {w}) :
    (w ∈ weylSupport B C θ ∧
      blockWeyl C ⊓ (blockWeyl B).comap (MulAut.conj w⁻¹).toMonoidHom = blockWeyl C) ↔
      TypeASolomon.SourceIncreasing C w.symm ∧
        WholeTarget.BlockEdgeAdjacent C w.symm ∧
        CutComplex.BooleanInterval.Active (permutationDescents w)
          (WholeTarget.allowedCuts C w.symm) B.cuts := by
  rw [mem_weylSupport_iff_minimal_of_upper_singleton B C θ w hwθ hθ hLower,
    ← isMinimalRepresentative_symm_iff B C w]
  simpa only [Equiv.symm_symm, Equiv.Perm.inv_def] using
    WholeTarget.wholeTarget_iff_interval B C w.symm

/-- Under the fixed inverse-permutation conditions, interval membership
supplies both actual core activity and the whole target intersection. -/
theorem weylSupport_wholeTarget_iff_active
    (B C : BlockShape n) (θ : Set (Equiv.Perm (Fin n)))
    (w : Equiv.Perm (Fin n)) (hwθ : w ∈ θ)
    (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
    (hLower : ∀ v ∈ θ \ {w}, ∀ z,
      inversionLength v < inversionLength z → z ∈ θ \ {w})
    (hinc : TypeASolomon.SourceIncreasing C w.symm)
    (hadj : WholeTarget.BlockEdgeAdjacent C w.symm) :
    (w ∈ weylSupport B C θ ∧
      blockWeyl C ⊓ (blockWeyl B).comap (MulAut.conj w⁻¹).toMonoidHom = blockWeyl C) ↔
      CutComplex.BooleanInterval.Active (permutationDescents w)
        (WholeTarget.allowedCuts C w.symm) B.cuts := by
  rw [weylSupport_wholeTarget_iff_interval B C θ w hwθ hθ hLower]
  exact ⟨fun h => h.2.2, fun h => ⟨hinc, hadj, h⟩⟩

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (A : letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
  (B C : BlockShape n) (θ : Set (Equiv.Perm (Fin n)))
  (w : Equiv.Perm (Fin n))
  (hbound : letI := T.topology
    CuspidalSupport.HasJacquetBlockBound F T C A)
  (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
  (hLower : ∀ v ∈ θ \ {w}, ∀ z,
    inversionLength v < inversionLength z → z ∈ θ \ {w})

include hbound hθ hLower

/-- Failure of any whole-target interval condition kills the genuine graded
quotient. No nonzero coefficient assumption is needed. -/
theorem cutSupportQuotient_subsingleton_of_not_wholeTarget_interval
    (hnot : ¬ (TypeASolomon.SourceIncreasing C w.symm ∧
      WholeTarget.BlockEdgeAdjacent C w.symm ∧
      CutComplex.BooleanInterval.Active (permutationDescents w)
        (WholeTarget.allowedCuts C w.symm) B.cuts)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    Subsingleton (cutSupportQuotient T A C B (θ \ {w}) θ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  by_cases hw : w ∈ weylSupport B C θ
  · have hwθ : w ∈ θ := twoSidedCore_subset _ _ θ hw
    have hmin := (mem_weylSupport_iff_minimal_of_upper_singleton
      B C θ w hwθ hθ hLower).mp hw
    have hW : blockWeyl C ⊓ (blockWeyl B).comap
        (MulAut.conj w⁻¹).toMonoidHom ≠ blockWeyl C := by
      intro hW
      exact hnot ((weylSupport_wholeTarget_iff_interval
        B C θ w hwθ hθ hLower).mp ⟨hw, hW⟩)
    exact cutSupportQuotient_subsingleton_of_not_wholeTarget.{uF,uV}
      T A B C w hbound hmin.1 hW θ hθ hLower hw
  · exact cutSupportQuotient_subsingleton_of_not_active.{uF,max uF uV} T A B C θ w hw

/-- Outside the Boolean interval, the actual graded quotient is zero even if
the fixed inverse-permutation conditions have not been supplied. -/
theorem cutSupportQuotient_subsingleton_of_not_active_interval
    (hnot : ¬ CutComplex.BooleanInterval.Active (permutationDescents w)
      (WholeTarget.allowedCuts C w.symm) B.cuts) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    Subsingleton (cutSupportQuotient T A C B (θ \ {w}) θ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  have hnot' : ¬ (TypeASolomon.SourceIncreasing C w.symm ∧
      WholeTarget.BlockEdgeAdjacent C w.symm ∧
      CutComplex.BooleanInterval.Active (permutationDescents w)
        (WholeTarget.allowedCuts C w.symm) B.cuts) := fun h => hnot h.2.2
  exact cutSupportQuotient_subsingleton_of_not_wholeTarget_interval.{uF,uV}
    T A B C θ w hbound hθ hLower hnot'

/-- A canonical zero-module comparison whenever the whole-target interval
conditions fail. -/
def cutSupportQuotientZeroEquiv_of_not_wholeTarget_interval
    (hnot : ¬ (TypeASolomon.SourceIncreasing C w.symm ∧
      WholeTarget.BlockEdgeAdjacent C w.symm ∧
      CutComplex.BooleanInterval.Active (permutationDescents w)
        (WholeTarget.allowedCuts C w.symm) B.cuts)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    cutSupportQuotient T A C B (θ \ {w}) θ ≃ₗ[ℂ] (Fin 0 → ℂ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := cutSupportQuotient_subsingleton_of_not_wholeTarget_interval.{uF,uV}
    T A B C θ w hbound hθ hLower hnot
  exact LinearEquiv.ofSubsingleton _ _

end Langlands.Aubert.Support
