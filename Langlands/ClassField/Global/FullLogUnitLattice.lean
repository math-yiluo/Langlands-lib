import Langlands.ClassField.Global.FullLogEmbedding

/-! # The full logarithmic unit lattice in the sum-zero hyperplane -/

noncomputable section

open NumberField
open scoped Classical

namespace Langlands.ClassField.Global

universe v

variable (E : Type v) [Field E] [NumberField E]

/-- The unit lattice pulled back to full infinite-place coordinates. -/
def fullLogUnitLattice : Submodule ℤ (fullLogHyperplane E) :=
  ZLattice.comap ℝ (E := NumberField.Units.dirichletUnitTheorem.logSpace E)
    (F := fullLogHyperplane E) (NumberField.Units.unitLattice E)
    (fullLogHyperplaneEquiv E).toLinearMap

/-- The pulled-back lattice is exactly the image of the actual unit logarithm. -/
theorem mem_fullLogUnitLattice (y : fullLogHyperplane E) :
    y ∈ fullLogUnitLattice E ↔
      ∃ x : Additive (𝓞 E)ˣ, fullLogEmbeddingToHyperplane E x = y := by
  change fullLogHyperplaneEquiv E y ∈ NumberField.Units.unitLattice E ↔ _
  rw [NumberField.Units.unitLattice, Submodule.mem_map]
  constructor
  · rintro ⟨x, _, hx⟩
    exact ⟨x, (fullLogHyperplaneEquiv E).injective
      ((fullLogHyperplaneEquiv_log E x).trans hx)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, Submodule.mem_top,
      (fullLogHyperplaneEquiv_log E x).symm⟩

theorem fullLogUnitLattice_eq_range :
    fullLogUnitLattice E =
      LinearMap.range (fullLogEmbeddingToHyperplane E).toIntLinearMap := by
  ext y
  exact mem_fullLogUnitLattice E y

instance instDiscreteTopologyFullLogUnitLattice :
    DiscreteTopology (fullLogUnitLattice E) :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ
    (E := NumberField.Units.dirichletUnitTheorem.logSpace E) (F := fullLogHyperplane E)
    (NumberField.Units.unitLattice E)
    (fullLogHyperplaneEquiv E).toContinuousLinearEquiv.toLinearMap))

instance instIsZLatticeFullLogUnitLattice :
    IsZLattice ℝ (fullLogUnitLattice E) :=
  inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ
    (E := NumberField.Units.dirichletUnitTheorem.logSpace E) (F := fullLogHyperplane E)
    (NumberField.Units.unitLattice E)
    (fullLogHyperplaneEquiv E).toContinuousLinearEquiv.toLinearMap))

theorem fullLogUnitLattice_span :
    Submodule.span ℝ (fullLogUnitLattice E : Set (fullLogHyperplane E)) = ⊤ :=
  IsZLattice.span_top

local instance : AddCommGroup (Additive ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E)) :=
  inferInstance

/-- Actual units modulo torsion identify with the full logarithmic unit lattice. -/
def fullLogEmbeddingEquiv :
    Additive ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E) ≃ₗ[ℤ] fullLogUnitLattice E :=
  (NumberField.Units.logEmbeddingEquiv E).trans
    (ZLattice.comap_equiv ℝ (E := NumberField.Units.dirichletUnitTheorem.logSpace E)
      (F := fullLogHyperplane E) (NumberField.Units.unitLattice E)
      (fullLogHyperplaneEquiv E))

@[simp] theorem fullLogEmbeddingEquiv_apply (x : (𝓞 E)ˣ) :
    (fullLogEmbeddingEquiv E (Additive.ofMul (QuotientGroup.mk x)) :
      fullLogHyperplane E) = fullLogEmbeddingToHyperplane E (Additive.ofMul x) := by
  change (fullLogHyperplaneEquiv E).symm
      (NumberField.Units.logEmbedding E (Additive.ofMul x)) = _
  rw [← fullLogHyperplaneEquiv_log]
  exact (fullLogHyperplaneEquiv E).symm_apply_apply _

end Langlands.ClassField.Global
