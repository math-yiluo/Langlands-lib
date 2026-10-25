import Mathlib.Algebra.Ring.Rat
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Topology.Order

open Topology TensorProduct

namespace Langlands.Topology.Rationalization

universe u v w

section Basic

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M]

/-- The final topology on `ℚ ⊗[ℤ] M` for the maps `x ↦ q ⊗ₜ x`, `q : ℚ`: a set is open
exactly when its preimage under every such map is open in `M`. -/
@[instance_reducible]
def finalTopology : TopologicalSpace (ℚ ⊗[ℤ] M) where
  IsOpen U := ∀ q : ℚ, IsOpen ((fun x : M => q ⊗ₜ[ℤ] x) ⁻¹' U)
  isOpen_univ _ := isOpen_univ
  isOpen_inter _ _ hU hV q := (hU q).inter (hV q)
  isOpen_sUnion S hS q := by
    rw [Set.preimage_sUnion]
    exact isOpen_biUnion fun U hU => hS U hU q

variable {M}

theorem isOpen_finalTopology_iff {U : Set (ℚ ⊗[ℤ] M)} :
    IsOpen[finalTopology M] U ↔ ∀ q : ℚ, IsOpen ((fun x : M => q ⊗ₜ[ℤ] x) ⁻¹' U) :=
  Iff.rfl

theorem isClosed_finalTopology_iff {C : Set (ℚ ⊗[ℤ] M)} :
    IsClosed[finalTopology M] C ↔ ∀ q : ℚ, IsClosed ((fun x : M => q ⊗ₜ[ℤ] x) ⁻¹' C) := by
  simp only [← isOpen_compl_iff, isOpen_finalTopology_iff, Set.preimage_compl]

variable (M) in
/-- `finalTopology M` is the supremum, in Mathlib's order on topologies, of the topologies
coinduced by the maps `x ↦ q ⊗ₜ x`. -/
theorem finalTopology_eq_iSup_coinduced :
    finalTopology M =
      ⨆ q : ℚ, TopologicalSpace.coinduced (fun x : M => q ⊗ₜ[ℤ] x) ‹TopologicalSpace M› := by
  refine TopologicalSpace.ext_iff.2 fun U => ?_
  rw [isOpen_finalTopology_iff, isOpen_iSup_iff]
  rfl

/-- Universal property of the final topology: a map out of `ℚ ⊗[ℤ] M` is continuous exactly
when its composite with every map `x ↦ q ⊗ₜ x` is continuous. -/
theorem continuous_finalTopology_iff {X : Type v} {t : TopologicalSpace X}
    {f : ℚ ⊗[ℤ] M → X} :
    Continuous[finalTopology M, t] f ↔ ∀ q : ℚ, Continuous[_, t] fun x : M => f (q ⊗ₜ[ℤ] x) := by
  simp only [continuous_def, isOpen_finalTopology_iff]
  exact ⟨fun h q V hV => h V hV q, fun h V hV q => h q V hV⟩

theorem continuous_of_forall_continuous_tmul {X : Type v} {t : TopologicalSpace X}
    {f : ℚ ⊗[ℤ] M → X} (hf : ∀ q : ℚ, Continuous[_, t] fun x : M => f (q ⊗ₜ[ℤ] x)) :
    Continuous[finalTopology M, t] f :=
  continuous_finalTopology_iff.2 hf

/-- Every map `x ↦ q ⊗ₜ x` is continuous for `finalTopology M`. -/
protected theorem continuous_tmul (q : ℚ) :
    Continuous[_, finalTopology M] fun x : M => q ⊗ₜ[ℤ] x :=
  continuous_def.2 fun _ hU => hU q

/-- Multiplication by any fixed rational number, including `0`, is continuous for
`finalTopology M`. -/
protected theorem continuous_smul (q : ℚ) :
    Continuous[finalTopology M, finalTopology M] fun y : ℚ ⊗[ℤ] M => q • y := by
  refine continuous_of_forall_continuous_tmul fun r => ?_
  simp only [smul_tmul', smul_eq_mul]
  exact Rationalization.continuous_tmul (q * r)

end Basic

variable {M : Type u} {N : Type w} [AddCommGroup M] [TopologicalSpace M]
  [AddCommGroup N] [TopologicalSpace N]

/-- The rational scalar extension of a continuous additive map is continuous for the final
topologies on its source and target. -/
theorem continuous_baseChange (f : M →+ N) (hf : Continuous f) :
    Continuous[finalTopology M, finalTopology N] (f.toIntLinearMap.baseChange ℚ) := by
  refine continuous_of_forall_continuous_tmul fun q => ?_
  simp only [LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap]
  exact continuous_def.2 fun U hU => hf.isOpen_preimage _ (hU q)

end Langlands.Topology.Rationalization
