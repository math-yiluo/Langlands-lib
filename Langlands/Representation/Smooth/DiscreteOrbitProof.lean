import Langlands.Representation.Smooth.DiscreteOrbitStatement
import Langlands.Representation.Smooth.Transfer.StabilizerProof
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Smoothness and continuity of discrete orbit maps

Proof of the vectorwise and global continuity characterizations in Renard III.1.1,
at the generality of the published statement.
-/

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V]

section Discrete

variable [IsTopologicalGroup G] [TopologicalSpace V] [DiscreteTopology V]

/-- A vector is smooth exactly when its orbit map into a discrete module is continuous. -/
theorem isSmoothVector_iff_continuous_orbitMap (ρ : Representation R G V) (v : V) :
    IsSmoothVector ρ v ↔ Continuous (fun g : G => ρ g v) := by
  rw [isSmoothVector_iff_isOpen_stabilizer]
  constructor
  · intro hv
    apply IsLocallyConstant.continuous
    apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
    intro g
    have hfiber : (fun x : G => ρ x v) ⁻¹' {ρ g v} =
        (fun x : G => g⁻¹ * x) ⁻¹' (ρ.stabilizer v : Set G) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
        Representation.mem_stabilizer, map_mul, Module.End.mul_apply,
        Representation.inv_apply_eq_iff]
    rw [hfiber]
    exact hv.preimage (continuous_const.mul continuous_id)
  · intro hv
    exact hv.isOpen_preimage {v} (isOpen_discrete _)

end Discrete

/-- The exact published discrete-orbit characterization, with all three universes independent. -/
theorem smoothDiscreteOrbit :
    SmoothDiscreteOrbitStatement (R := R) (G := G) (V := V) := by
  intro _ ρ
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := discreteTopology_bot V
  have h (v : V) : IsSmoothVector ρ v ↔ Continuous (fun g : G => ρ g v) :=
    isSmoothVector_iff_continuous_orbitMap ρ v
  exact ⟨h, ⟨fun hρ v => (h v).mp (hρ v), fun hρ v => (h v).mpr (hρ v)⟩⟩

end Langlands
