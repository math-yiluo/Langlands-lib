import Langlands.LocalField.ResidueNormalizedMetricStatement
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # The topology of the residue-normalized metric -/

open scoped NNReal
open MonoidWithZeroHom ValuativeRel

namespace Langlands.LocalField

universe u

theorem residueNormalizedMetric (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ResidueNormalizedMetricStatement F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let v := Valued.v (R := F) (Γ₀ := ValueGroupWithZero F)
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hq : (1 : ℝ≥0) < (residueCardinality F : ℝ≥0) := by
    exact_mod_cast residueCardinality_gt_one F
  let ρ := WithZeroMulInt.toNNReal hq.ne_zero
  let : v.RankOne :=
    { hom' := ρ.comp (e.toMulEquiv.toMonoidWithZeroHom.comp ValueGroup₀.embedding)
      strictMono' := (WithZeroMulInt.toNNReal_strictMono hq).comp
        (e.strictMono.comp ValueGroup₀.embedding_strictMono) }
  let N := Valued.toNormedField F (ValueGroupWithZero F)
  refine ⟨N.toMetricSpace, rfl, ?_, ?_⟩
  · intro x y
    change (↑(ρ (e (ValueGroup₀.embedding (v.restrict (x - y))))) : ℝ) =
      residueNormalizedAbsoluteValue F (x - y)
    rw [v.embedding_restrict]
    rfl
  · let := N
    infer_instance

end Langlands.LocalField
