import Langlands.Algebra.NondegeneratePartRangeExactnessStatements

/-!
# Exactness of original intertwiners on their nondegenerate parts

The actual range of a restricted original map is its ambient range intersected
with the nondegenerate part. Idempotents adjust ambient preimages directly.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uL uM uN

namespace NonUnitalModuleHom

variable {A : Type uA} [NonUnitalRing A]
  {L : Type uL} [AddCommGroup L] [NonUnitalModule A L]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]

/-- Any ambient preimage of a nondegenerate vector can be adjusted by a fixer. -/
@[simp] theorem mem_range_restrictNondegeneratePart_iff (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A L M) (m : nondegeneratePart hA M) :
    m ∈ (f.restrictNondegeneratePart hA).rangeSubmodule ↔
      m.val ∈ f.rangeSubmodule := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l.val, congrArg Subtype.val hl⟩
  · rintro ⟨l, hl⟩
    change f l = m.val at hl
    obtain ⟨e, he⟩ := m.property
    refine ⟨⟨(e : A) • l, ?_⟩, ?_⟩
    · exact ⟨e, by rw [← mul_smul, e.property.eq]⟩
    · apply Subtype.ext
      change f ((e : A) • l) = m.val
      rw [f.map_smul, hl, he]

/-- Vanishing of a restricted map is precisely ambient vanishing. -/
@[simp] theorem mem_kernel_restrictNondegeneratePart_iff (hA : IsIdempotented A)
    (g : NonUnitalModuleHom A M N) (m : nondegeneratePart hA M) :
    m ∈ (g.restrictNondegeneratePart hA).kernelSubmodule ↔
      m.val ∈ g.kernelSubmodule := by
  constructor
  · intro hm
    exact congrArg Subtype.val hm
  · intro hm
    exact Subtype.ext hm

/-- Original range-kernel exactness passes to the actual restrictions. -/
theorem range_restrictNondegeneratePart_eq_kernel (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A L M) (g : NonUnitalModuleHom A M N)
    (h : f.rangeSubmodule = g.kernelSubmodule) :
    (f.restrictNondegeneratePart hA).rangeSubmodule =
      (g.restrictNondegeneratePart hA).kernelSubmodule := by
  apply SetLike.ext
  intro m
  rw [mem_range_restrictNondegeneratePart_iff,
    mem_kernel_restrictNondegeneratePart_iff, h]

/-- Surjective original maps remain surjective on the actual parts. -/
theorem restrictNondegeneratePart_surjective (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A L M) (hf : Function.Surjective f) :
    Function.Surjective (f.restrictNondegeneratePart hA) := by
  intro m
  exact (mem_range_restrictNondegeneratePart_iff hA f m).2 (hf m.val)

/-- Injective original maps remain injective on the actual parts. -/
theorem restrictNondegeneratePart_injective (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A L M) (hf : Function.Injective f) :
    Function.Injective (f.restrictNondegeneratePart hA) := by
  intro l l' h
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val h

end NonUnitalModuleHom

/-- The complete closed range-kernel exactness proposition. -/
theorem nondegeneratePartRangeExactnessStatement :
    NondegeneratePartRangeExactnessStatement.{uA, uL, uM, uN} := by
  intro A _ hA L M N _ _ _ _ _ _ f g h
  exact NonUnitalModuleHom.range_restrictNondegeneratePart_eq_kernel hA f g h

/-! Complete unapplied interfaces with independent carrier universes. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {L : Type uL} → [AddCommGroup L] → [NonUnitalModule A L] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) →
    (f : NonUnitalModuleHom A L M) → (g : NonUnitalModuleHom A M N) →
    f.rangeSubmodule = g.kernelSubmodule →
      (f.restrictNondegeneratePart hA).rangeSubmodule =
        (g.restrictNondegeneratePart hA).kernelSubmodule :=
  @NonUnitalModuleHom.range_restrictNondegeneratePart_eq_kernel.{uA, uL, uM, uN}

example : NondegeneratePartRangeExactnessStatement.{uA, uL, uM, uN} :=
  nondegeneratePartRangeExactnessStatement.{uA, uL, uM, uN}

example : NondegeneratePartRangeExactnessStatement.{0, 1, 0, 1} :=
  nondegeneratePartRangeExactnessStatement.{0, 1, 0, 1}

example : NondegeneratePartRangeExactnessStatement.{1, 0, 1, 0} :=
  nondegeneratePartRangeExactnessStatement.{1, 0, 1, 0}

end Langlands.Algebra
