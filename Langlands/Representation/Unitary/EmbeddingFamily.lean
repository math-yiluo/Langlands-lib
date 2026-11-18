import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.EMetricSpace.Lipschitz

/-! # A unitary action from a coherent family of actual isometric embeddings -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands

universe uG uE uH

/-- A prescribed isometric family in one target, with image containment and a
translated Gram identity. The identity element's embedding is retained. -/
structure UnitaryEmbeddingFamily
    (G : Type uG) [Group G]
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  embedding : G → E →ₗᵢ[ℂ] H
  range_mem (g : G) (x : E) : embedding g x ∈ LinearMap.range (embedding 1).toLinearMap
  gram (g h : G) (x y : E) :
    Inner.inner ℂ (embedding g x) (embedding (g * h) y) =
      Inner.inner ℂ (embedding 1 x) (embedding h y)

namespace UnitaryEmbeddingFamily

variable {G : Type uG} [Group G]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (F : UnitaryEmbeddingFamily G E H)

/-- The supplied translated embedding, restricted to the identity image. -/
def rangeEmbedding (g : G) :
    E →ₗᵢ[ℂ] LinearMap.range (F.embedding 1).toLinearMap where
  toLinearMap := (F.embedding g).toLinearMap.codRestrict _ (F.range_mem g)
  norm_map' x := (F.embedding g).norm_map x

/-- Transport each supplied embedding through the original identity embedding. -/
def transport (g : G) : E →ₗᵢ[ℂ] E :=
  (F.embedding 1).equivRange.symm.toLinearIsometry.comp (F.rangeEmbedding g)

/-- The transported operator retains the prescribed actual target values. -/
theorem embedding_transport (g : G) (x : E) :
    F.embedding 1 (F.transport g x) = F.embedding g x :=
  congrArg Subtype.val ((F.embedding 1).equivRange.apply_symm_apply (F.rangeEmbedding g x))

@[simp]
theorem transport_one (x : E) : F.transport 1 x = x :=
  (F.embedding 1).injective (F.embedding_transport 1 x)

/-- The Gram identity forces the multiplication law for the transported maps. -/
theorem transport_mul (g h : G) (x : E) :
    F.transport g (F.transport h x) = F.transport (g * h) x := by
  have hp :
      Inner.inner ℂ (F.embedding g (F.transport h x)) (F.embedding (g * h) x) =
        Inner.inner ℂ (F.embedding h x) (F.embedding h x) :=
    (F.gram g h (F.transport h x) x).trans
      (congrArg (fun z : H => Inner.inner ℂ z (F.embedding h x)) (F.embedding_transport h x))
  have hn : ‖F.embedding g (F.transport h x)‖ ≤ ‖F.embedding (g * h) x‖ := by
    simp only [LinearIsometry.norm_map, le_refl]
  have hr :
      (Inner.inner ℂ (F.embedding g (F.transport h x)) (F.embedding (g * h) x)).re =
        ‖F.embedding (g * h) x‖ ^ 2 := by
    exact (congrArg Complex.re hp).trans
      ((norm_sq_eq_re_inner (𝕜 := ℂ) (F.embedding h x)).symm.trans
        (congrArg (fun t : ℝ => t ^ 2)
          (((F.embedding h).norm_map x).trans ((F.embedding (g * h)).norm_map x).symm)))
  have heq := eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ) hn hr
  apply (F.embedding 1).injective
  exact (F.embedding_transport g (F.transport h x)).trans
    (heq.trans (F.embedding_transport (g * h) x).symm)

/-- The inverse group element supplies surjectivity of each original transport. -/
theorem transport_surjective (g : G) : Function.Surjective (F.transport g) := by
  intro x
  refine ⟨F.transport g⁻¹ x, ?_⟩
  exact (F.transport_mul g g⁻¹ x).trans
    ((congrArg (fun a : G => F.transport a x) (mul_inv_cancel g)).trans (F.transport_one x))

/-- Each transported operator is a genuine complex-linear isometric equivalence. -/
def transportEquiv (g : G) : E ≃ₗᵢ[ℂ] E :=
  LinearIsometryEquiv.ofSurjective (F.transport g) (F.transport_surjective g)

/-- The actual bounded complex-linear group action induced by the given family. -/
def toContinuousLinearRepresentation : G →* (E →L[ℂ] E) where
  toFun g := (F.transport g).toContinuousLinearMap
  map_one' := ContinuousLinearMap.ext (F.transport_one)
  map_mul' g h := ContinuousLinearMap.ext fun x => (F.transport_mul g h x).symm

@[simp]
theorem toContinuousLinearRepresentation_apply (g : G) (x : E) :
    F.toContinuousLinearRepresentation g x = F.transport g x := rfl

/-- The induced action preserves the supplied inner product on the source. -/
theorem inner_toContinuousLinearRepresentation (g : G) (x y : E) :
    Inner.inner ℂ (F.toContinuousLinearRepresentation g x)
      (F.toContinuousLinearRepresentation g y) = Inner.inner ℂ x y :=
  (F.transport g).inner_map_map x y

variable [TopologicalSpace G]

/-- Continuity of the actual supplied target orbits gives continuity of the
corresponding source orbits. -/
theorem continuous_transportOrbit
    (hF : ∀ x : E, Continuous (fun g : G => F.embedding g x)) (x : E) :
    Continuous (fun g : G => F.transport g x) := by
  apply (F.embedding 1).isometry.isEmbedding.continuous_iff.mpr
  change Continuous (fun g : G => F.embedding 1 (F.transport g x))
  exact (hF x).congr (fun g => (F.embedding_transport g x).symm)

/-- Isometry gives joint continuity from continuity of the supplied target orbits. -/
theorem continuous_action
    (hF : ∀ x : E, Continuous (fun g : G => F.embedding g x)) :
    Continuous (fun p : G × E => F.toContinuousLinearRepresentation p.1 p.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun g => (F.transport g).isometry.lipschitzWith) (F.continuous_transportOrbit hF)

end UnitaryEmbeddingFamily
end Langlands
