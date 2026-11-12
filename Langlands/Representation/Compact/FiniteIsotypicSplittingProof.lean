import Langlands.Representation.Compact.CompactIsotypicSplittingProof
import Langlands.Representation.Compact.ProjectorCofan

/-! # The finite compact-isotypic block decomposition -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.7: splitting off finitely many distinct compact classes, with
an actual coproduct and the full subquotient-avoiding complement. -/
theorem finiteIsotypicSplitting : FiniteIsotypicSplittingStatement.{u, v} := by
  classical
  intro G _ _ _ _ _ _ _ _ _ μ _ _ _ S
  constructor
  · intro A
    let p (c : S) := blockProjector μ c.val A
    have hp (c : S) (x : A) : p c (p c x) = p c x :=
      blockProjector_idempotent μ c.val A x
    have ho (c d : S) (hcd : c ≠ d) (x : A) : p c (p d x) = 0 :=
      blockProjector_orthogonal μ (fun h => hcd (Subtype.ext h)) A x
    let hf (x : A) : Function.HasFiniteSupport (fun c : S => p c x) := Set.toFinite _
    let P := pointwiseFiniteSum p hf
    have hPid (x : A) : P (P x) = P x := pointwiseFiniteSum_idempotent p hf hp ho x
    have hPc (c : S) (x : A) : P (p c x) = p c x :=
      pointwiseFiniteSum_component p hf hp ho c x
    have hcP (c : S) (x : A) : p c (P x) = p c x :=
      component_pointwiseFiniteSum p hf hp ho c x
    let e : Option S → A.representation.IntertwiningMap A.representation
      | none => Representation.IntertwiningMap.id _ - P
      | some c => p c
    have hid (i : Option S) (x : A) : e i (e i x) = e i x := by
      cases i with
      | none =>
        change (x - P x) - P (x - P x) = x - P x
        rw [map_sub, hPid, sub_self, sub_zero]
      | some c => exact hp c x
    have horth (i j : Option S) (hij : i ≠ j) (x : A) : e i (e j x) = 0 := by
      cases i with
      | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some d =>
          change p d x - P (p d x) = 0
          rw [hPc, sub_self]
      | some c =>
        cases j with
        | none =>
          change p c (x - P x) = 0
          rw [map_sub, hcP, sub_self]
        | some d => exact ho c d (fun h => hij (congrArg some h)) x
    have hsum (x : A) : (∑ᶠ i, e i x) = x := by
      rw [finsum_option (show Function.HasFiniteSupport (fun c : S => e (some c) x) from
        Set.toFinite _)]
      change (x - P x) + P x = x
      exact sub_add_cancel x (P x)
    refine ⟨(fun i => SmoothRep.subrepresentation A (e i).range),
      (fun i => SmoothRep.subtype A (e i).range), ?_,
      ⟨SmoothRep.projectorRangeCofanIsColimit A e (fun _ => Set.toFinite _) hid horth hsum⟩⟩
    intro i
    cases i with
    | none =>
      change avoidingPart G (S : Set (CompactCoefficientClass.{u, v} G))
        (SmoothRep.subrepresentation A (e none).range)
      apply (avoidingPart_iff_blockProjector_zero μ _ _).mpr
      intro c hc x
      apply SmoothRep.subtype_injective A (e none).range
      rw [← blockProjector_natural μ c (SmoothRep.subtype A (e none).range), map_zero]
      obtain ⟨y, hy⟩ := x.property
      change blockProjector μ c A x.val = 0
      rw [← hy]
      exact horth (some ⟨c, hc⟩) none (by simp) y
    | some c => exact isotypicPart_blockProjector_range μ c.val A
  · intro i j hij A B hA hB f
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some d =>
        exact hom_eq_zero_of_blockProjector_zero_fixed μ d.val
          ((avoidingPart_iff_blockProjector_zero μ _ A).mp hA d.val d.property)
          ((isotypicPart_iff_blockProjector_fixed μ d.val B).mp hB) f
    | some c =>
      cases j with
      | none =>
        exact hom_eq_zero_of_blockProjector_fixed_zero μ c.val
          ((isotypicPart_iff_blockProjector_fixed μ c.val A).mp hA)
          ((avoidingPart_iff_blockProjector_zero μ _ B).mp hB c.val c.property) f
      | some d =>
        exact hom_eq_zero_of_isotypicPart_ne μ
          (fun h => hij (congrArg some (Subtype.ext h))) hA hB f

end Langlands.Renard.CompactRepresentation
