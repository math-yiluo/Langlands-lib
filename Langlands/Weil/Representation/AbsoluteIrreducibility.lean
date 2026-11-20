import Langlands.LinearAlgebra.IrreducibleRepresentationSpan
import Langlands.Weil.Representation.CoefficientExtension
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-! # Absolute irreducibility under scalar extension -/

noncomputable section

open scoped TensorProduct MonoidAlgebra

universe uk uc ue ug uv

namespace Langlands.FiniteRepresentation

variable {k : Type uk} [Field k] {G : Type ug} [Monoid G]

/-- An action is absolutely irreducible if it is irreducible after scalar extension
through the canonical map to the algebraic closure of the coefficient field. -/
def IsAbsolutelyIrreducible (A : FiniteRepresentation.{uk, ug, uv} k G) : Prop :=
  Representation.IsIrreducible (A.extendCoefficients (AlgebraicClosure k)).representation

private theorem span_eq_top_extendCoefficients_iff
    (E : Type ue) [Field E] [Algebra k E] (A : FiniteRepresentation.{uk, ug, uv} k G) :
    Submodule.span E (Set.range (A.extendCoefficients E).representation) = ⊤ ↔
      Submodule.span k (Set.range A.representation) = ⊤ := by
  let h := TensorProduct.isBaseChange k A E
  let e : E ⊗[k] Module.End k A ≃ₗ[E] Module.End E (E ⊗[k] A) := h.end.equiv
  have he (f : Module.End k A) : e ((1 : E) ⊗ₜ[k] f) = f.baseChange E := by
    change h.end.equiv ((1 : E) ⊗ₜ[k] f) = _
    rw [IsBaseChange.equiv_tmul, one_smul]
    apply h.algHom_ext
    intro x
    rw [IsBaseChange.endHom_comp_apply]
    rfl
  have hmap : ((Submodule.span k (Set.range A.representation)).baseChange E).map e.toLinearMap =
      Submodule.span E (Set.range (A.extendCoefficients E).representation) := by
    rw [Submodule.baseChange_span, Submodule.map_span, Set.image_image, ← Set.range_comp]
    refine congrArg (Submodule.span E) ?_
    exact congrArg Set.range (funext fun g => he (A.representation g))
  constructor
  · intro hs
    apply Submodule.baseChange_injective (A := E)
    rw [Submodule.baseChange_top]
    exact Submodule.map_eq_top_iff.mp (hmap.trans hs)
  · intro hs
    rw [← hmap, hs, Submodule.baseChange_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]

private theorem irreducible_of_full_span (A : FiniteRepresentation.{uk, ug, uv} k G)
    [Nontrivial A] (h : Submodule.span k (Set.range A.representation) = ⊤) :
    Representation.IsIrreducible A.representation := by
  have : Nontrivial (Subrepresentation A.representation) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => or_iff_not_imp_left.mpr fun hS => ?_⟩
  have hS' : S.toSubmodule ≠ ⊥ := fun e => hS (Subrepresentation.toSubmodule_injective e)
  obtain ⟨x, hx, hx₀⟩ := S.toSubmodule.ne_bot_iff.mp hS'
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hx₀
  apply top_unique
  intro y _
  have hinv : Submodule.span k (Set.range A.representation) ≤
      S.toSubmodule.comap (LinearMap.applyₗ x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact S.apply_mem_toSubmodule g hx
  have hy : φ.smulRight y ∈ Submodule.span k (Set.range A.representation) := by
    rw [h]
    exact Submodule.mem_top
  have hout := hinv hy
  change φ x • y ∈ S.toSubmodule at hout
  change y ∈ S.toSubmodule
  simpa only [hφ, one_smul] using hout

/-- Irreducibility after extension to one algebraically closed field implies
irreducibility after every coefficient extension. -/
theorem irreducible_extendCoefficients_of_isAlgClosed
    (C : Type uc) [Field C] [Algebra k C] [IsAlgClosed C]
    (E : Type ue) [Field E] [Algebra k E] (A : FiniteRepresentation.{uk, ug, uv} k G)
    (hA : Representation.IsIrreducible (A.extendCoefficients C).representation) :
    Representation.IsIrreducible (A.extendCoefficients E).representation := by
  let := hA
  let : Nontrivial (A.extendCoefficients C) :=
    IsSimpleModule.nontrivial C[G] (A.extendCoefficients C).representation.asModule
  have hr : 0 < A.rank := by
    rw [← rank_extendCoefficients C A]
    exact Module.finrank_pos
  let : Nontrivial (A.extendCoefficients E) := by
    apply Module.nontrivial_of_finrank_pos (R := E)
    change 0 < (A.extendCoefficients E).rank
    simpa only [rank_extendCoefficients] using hr
  apply irreducible_of_full_span
  apply (span_eq_top_extendCoefficients_iff E A).mpr
  apply (span_eq_top_extendCoefficients_iff C A).mp
  exact Langlands.LinearAlgebra.irreducibleRepresentationSpan_proof C G
    (A.extendCoefficients C) _ hA

/-- An absolutely irreducible action remains irreducible over every extension. -/
theorem IsAbsolutelyIrreducible.extendCoefficients
    {A : FiniteRepresentation.{uk, ug, uv} k G} (hA : A.IsAbsolutelyIrreducible)
    (E : Type ue) [Field E] [Algebra k E] :
    Representation.IsIrreducible (A.extendCoefficients E).representation :=
  irreducible_extendCoefficients_of_isAlgClosed (AlgebraicClosure k) E A hA

end Langlands.FiniteRepresentation
