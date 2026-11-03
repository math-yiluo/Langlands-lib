import Langlands.AlgebraicGeometry.PointTopology.FiniteModuleTopologyStatements

/-! # The finite projective module topology comparison -/

noncomputable section

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology

theorem finiteProjectiveModuleTopologyProperties_proof
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    FiniteProjectiveModuleTopologyProperties R M := by
  refine ⟨?_, ?_, Module.Finite.exists_comp_eq_id_of_projective R M⟩
  · intro n q hq
    exact ModuleTopology.eq_coinduced_of_surjective hq
  · let _ : TopologicalSpace M := moduleTopology R M
    let _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup R M
    intro n s p hps
    have hleft : Function.LeftInverse p s := fun m ↦ LinearMap.congr_fun hps m
    exact hleft.isEmbedding
      (IsModuleTopology.continuous_of_linearMap p)
      (IsModuleTopology.continuous_of_linearMap s)

end Langlands.AlgebraicGeometry.PointTopology
