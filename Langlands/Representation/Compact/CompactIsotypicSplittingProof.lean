import Langlands.Representation.Compact.CompactIsotypicBlocks

/-! # Splitting off one compact irreducible class -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MeasureTheory

namespace Langlands.Renard.CompactRepresentation

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant]

/-- The actual range of the class projector is an object of the stated isotypic part. -/
theorem isotypicPart_blockProjector_range (c : CompactCoefficientClass.{u, v} G)
    (A : SmoothRep.{0, u, v} ℂ G) :
    isotypicPart G c (SmoothRep.subrepresentation A (blockProjector μ c A).range) := by
  apply (isotypicPart_iff_blockProjector_fixed μ c _).mpr
  intro x
  apply SmoothRep.subtype_injective A (blockProjector μ c A).range
  rw [← blockProjector_natural μ c (SmoothRep.subtype A (blockProjector μ c A).range)]
  obtain ⟨y, hy⟩ := x.property
  change blockProjector μ c A x.val = x.val
  rw [← hy]
  exact blockProjector_idempotent μ c A y

omit [SigmaCompactSpace G] [μ.Regular] [μ.IsMulRightInvariant] in
/-- Hom vanishing from a projector-fixed object to a projector-zero object. -/
theorem hom_eq_zero_of_blockProjector_fixed_zero (c : CompactCoefficientClass.{u, v} G)
    {A B : SmoothRep.{0, u, v} ℂ G}
    (hA : ∀ x : A, blockProjector μ c A x = x)
    (hB : ∀ x : B, blockProjector μ c B x = 0) (f : A ⟶ B) : f = 0 := by
  ext x
  change SmoothRep.hom f x = 0
  rw [← hA x, ← blockProjector_natural μ c f, hB]

omit [SigmaCompactSpace G] [μ.Regular] [μ.IsMulRightInvariant] in
/-- Hom vanishing in the reverse direction. -/
theorem hom_eq_zero_of_blockProjector_zero_fixed (c : CompactCoefficientClass.{u, v} G)
    {A B : SmoothRep.{0, u, v} ℂ G}
    (hA : ∀ x : A, blockProjector μ c A x = 0)
    (hB : ∀ x : B, blockProjector μ c B x = x) (f : A ⟶ B) : f = 0 := by
  ext x
  change SmoothRep.hom f x = 0
  rw [← hB (SmoothRep.hom f x), blockProjector_natural μ c f, hA, map_zero]

include μ in
/-- Distinct isotypic objects have zero Hom groups. -/
theorem hom_eq_zero_of_isotypicPart_ne {c d : CompactCoefficientClass.{u, v} G}
    (hcd : c ≠ d) {A B : SmoothRep.{0, u, v} ℂ G}
    (hA : isotypicPart G c A) (hB : isotypicPart G d B) (f : A ⟶ B) : f = 0 := by
  apply hom_eq_zero_of_blockProjector_fixed_zero μ c
    ((isotypicPart_iff_blockProjector_fixed μ c A).mp hA) _ f
  intro x
  rw [← (isotypicPart_iff_blockProjector_fixed μ d B).mp hB x]
  exact blockProjector_orthogonal μ hcd B x

/-- Renard IV.1.7: the ambient smooth category splits along one compact class. -/
theorem isotypicSplitting : IsotypicSplittingStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ _ μ _ _ _ c
  constructor
  · intro A
    let p := blockProjector μ c A
    refine ⟨SmoothRep.idempotentComponents A p, (SmoothRep.idempotentCofan A p).inj,
      ?_, ⟨SmoothRep.idempotentCofanIsColimit A p (blockProjector_idempotent μ c A)⟩⟩
    intro b
    cases b
    · change avoidingPart G {c} (SmoothRep.subrepresentation A p.ker)
      apply (avoidingPart_iff_blockProjector_zero μ {c} _).mpr
      intro d hd x
      have hdc : d = c := Set.mem_singleton_iff.mp hd
      subst d
      apply SmoothRep.subtype_injective A p.ker
      rw [← blockProjector_natural μ c (SmoothRep.subtype A p.ker), map_zero]
      exact x.property
    · exact isotypicPart_blockProjector_range μ c A
  · intro b d hbd A B hA hB f
    cases b <;> cases d
    · exact (hbd rfl).elim
    · exact hom_eq_zero_of_blockProjector_zero_fixed μ c
        ((avoidingPart_iff_blockProjector_zero μ {c} A).mp hA c (Set.mem_singleton c))
        ((isotypicPart_iff_blockProjector_fixed μ c B).mp hB) f
    · exact hom_eq_zero_of_blockProjector_fixed_zero μ c
        ((isotypicPart_iff_blockProjector_fixed μ c A).mp hA)
        ((avoidingPart_iff_blockProjector_zero μ {c} B).mp hB c (Set.mem_singleton c)) f
    · exact (hbd rfl).elim

end Langlands.Renard.CompactRepresentation
