import Langlands.Global.AdelicPunctureEmbeddingStatement
import Langlands.Global.AdelicUnitSequence

/-! # Proof of the failure of embedding for adelic punctured-line points -/

noncomputable section

universe u

open CategoryTheory Filter Topology

namespace Langlands.AlgebraicGeometry.PointTopology

variable {S : Type u} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

/-- Units with values tending to one and inverse values not tending to one
give all three forms of the obstruction. -/
theorem affineLinePunctureEmbeddingObstruction_of_tendsto (x : ℕ → Sˣ)
    (hx : Tendsto (fun n => (x n : S)) atTop (𝓝 1))
    (hinv : ¬ Tendsto (fun n => Units.val ((x n)⁻¹)) atTop (𝓝 1)) :
    AffineLinePunctureEmbeddingObstruction S := by
  have hemb : ¬ IsEmbedding (Units.val : Sˣ → S) := by
    intro he
    have h1 : Tendsto x atTop (𝓝 1) := by
      rw [he.isInducing.tendsto_nhds_iff, Units.val_one]
      exact hx
    exact hinv (by simpa [Function.comp_def] using (Units.continuous_coe_inv.tendsto 1).comp h1)
  refine ⟨?_, hemb, ?_⟩
  · intro hg
    let t : TopologicalSpace Sˣ := TopologicalSpace.induced Units.val inferInstance
    have hc : Continuous[t, _] (fun y : Sˣ => Units.val y⁻¹) :=
      (continuous_induced_dom (f := (Units.val : Sˣ → S))).comp
        (@continuous_inv Sˣ t _ hg.toContinuousInv)
    have h1 : Tendsto x atTop (@nhds Sˣ t 1) := by
      rw [nhds_induced, Units.val_one]
      exact tendsto_comap_iff.2 hx
    exact hinv (by simpa [Function.comp_def] using (@Continuous.tendsto _ _ t _ _ hc 1).comp h1)
  · intro R _ _ he
    apply hemb
    have hval : (Units.val : Sˣ → S) = affineLinePointHomeomorph R S ∘
        (fun p : RingPoint R (affineLinePuncture R) S => p ≫ affineLinePunctureι R) ∘
          (affineLinePunctureUnitHomeomorph R S).symm := by
      funext y
      show (y : S) = affineLinePointEquiv R S
        ((affineLinePunctureUnitHomeomorph R S).symm y ≫ affineLinePunctureι R)
      rw [← affineLinePunctureUnitHomeomorph_val, Homeomorph.apply_symm_apply]
    rw [hval]
    exact (affineLinePointHomeomorph R S).isEmbedding.comp
      (he.comp (affineLinePunctureUnitHomeomorph R S).symm.isEmbedding)

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Conrad's nonembedding of punctured-line points in both global-field characteristics. -/
theorem adelicPunctureEmbedding : AdelicPunctureEmbeddingStatement.{u} :=
  ⟨fun K _ _ => affineLinePunctureEmbeddingObstruction_of_tendsto
      (numberFieldUnitSequence K) (tendsto_numberFieldUnitSequence_val K)
      (not_tendsto_numberFieldUnitSequence_inv K),
    fun k F _ _ _ _ _ _ => affineLinePunctureEmbeddingObstruction_of_tendsto
      (curvePlaceUnitSequence k F) (tendsto_curvePlaceUnitSequence_val k F)
      (not_tendsto_curvePlaceUnitSequence_inv k F)⟩

end Langlands.Global
