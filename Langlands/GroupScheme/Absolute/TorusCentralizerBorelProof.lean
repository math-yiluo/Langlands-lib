import Langlands.GroupScheme.Absolute.TorusCentralizerBorelIntersection
import Langlands.GroupScheme.Absolute.TorusCentralizerBorelConverse

/-! # Proof: Borel subgroups of a torus centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Borel subgroups of a torus centralizer are exactly its intersections with
ambient Borel subgroups containing the torus, with the forward statement over
every field and the converse over an algebraically closed field. -/
theorem torusCentralizerBorel : TorusCentralizerBorelStatement.{u} := by
  intro k _ G _ _ _ S s hS hs C c hrep hc
  constructor
  · intro B b hb hSB
    exact ⟨subgroupIntersection c b, subgroupIntersectionFst c b,
      hS.isGeometricBorelSubgroup_centralizerIntersection s c hrep hc b hb hSB,
      range_subgroupIntersectionHom c b⟩
  · intro hclosed
    let : IsAlgClosed k := hclosed
    have hsplit : IsSplitTorus S.toGrp :=
      hS.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
    exact exists_ambient_borel_of_torusCentralizer_intersections G S s hS hs C c hrep hc
      (fun B b hb hSB =>
        hsplit.isBorelSubgroup_centralizerIntersection s c hrep hc b hb hSB)

end Langlands.GroupScheme
