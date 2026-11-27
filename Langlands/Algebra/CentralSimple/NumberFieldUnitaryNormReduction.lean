import Langlands.Algebra.CentralSimple.NumberFieldUnitaryNormStatement
import Langlands.Algebra.CentralSimple.NumberFieldUnitaryEmbeddingStatement
import Langlands.Algebra.CentralSimple.NumberFieldUnitaryNormTorusStatement
import Langlands.Algebra.ReducedNormSubfield

/-! # The unitary norm theorem from embeddings of unitary tori -/

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic

/-- The unitary norm theorem follows from the local–global principle for embeddings of fields
with involution and the construction of a locally embeddable field with involution containing
a unitary element of the prescribed norm. -/
def NumberFieldUnitaryNormReductionStatement : Prop :=
  NumberFieldUnitaryEmbeddingStatement.{u} → NumberFieldUnitaryNormTorusStatement.{u} →
    NumberFieldUnitaryNormStatement.{u}

/-- Proof of `NumberFieldUnitaryNormReductionStatement`: the image of the unitary element
under a global embedding compatible with the involutions is unitary, and its reduced norm is
its field norm. -/
theorem numberFieldUnitaryNormReduction : NumberFieldUnitaryNormReductionStatement.{u} := by
  intro hemb htor F E B _ _ _ _ _ _ _ _ _ _ _ _ _ τ hτ z hz
  obtain ⟨P, _, _, _, _, _, σ, hσ, hdim, ⟨x, hx, hnorm⟩, hloc⟩ := htor F E B τ hτ z hz
  obtain ⟨φ, hφ⟩ := hemb F E B P τ σ hτ hσ hdim hloc
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hdeg : Module.finrank E P = reducedDegree E B := by
    rw [reducedDegree, hdim, Nat.sqrt_eq']
  refine ⟨Units.map φ.toMonoidHom (Units.mk0 x hx0), ?_, ?_⟩
  · change φ x * τ (φ x) = 1
    rw [← hφ, ← map_mul, hx, map_one]
  · change reducedNorm E B E ((1 : E) ⊗ₜ[E] φ x) = (z : E)
    rw [reducedNorm_eq_field_norm E B φ hdeg x, hnorm]

end Langlands.CentralSimple
