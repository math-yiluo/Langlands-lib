import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemePointsTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers

/-! # Isomorphism invariance of the presheaf point topology -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F G : Presheaf S}

namespace Points

/-- An isomorphism of presheaves induces an equivalence of their quotient point sets. -/
def isoEquiv (e : F ≅ G) : Points F ≃ Points G where
  toFun := map e.hom
  invFun := map e.inv
  left_inv x := by rw [← map_comp, e.hom_inv_id]; exact map_id x
  right_inv x := by rw [← map_comp, e.inv_hom_id]; exact map_id x

/-- Presheaf isomorphisms are continuous on quotient point spaces. -/
theorem continuous_map_iso (e : F ≅ G) :
    Continuous[pointTopology F, pointTopology G] (map e.hom) := by
  let : TopologicalSpace (Points G) := pointTopology G
  rw [continuous_pointTopology_iff]
  intro U a ha
  have h := continuous_schemePoint_chart (a ≫ e.hom) (ha.comp_iso e)
  have heq : (map e.hom ∘ map a ∘ schemePoint U) =
      (map (a ≫ e.hom) ∘ schemePoint U) := by
    funext x
    exact (map_comp a e.hom (schemePoint U x)).symm
  rwa [heq]

/-- The point topology is invariant under arbitrary presheaf isomorphisms. -/
def isoHomeomorph (e : F ≅ G) :
    letI := pointTopology F
    letI := pointTopology G
    Points F ≃ₜ Points G := by
  letI := pointTopology F
  letI := pointTopology G
  exact
    { toEquiv := isoEquiv e
      continuous_toFun := continuous_map_iso e
      continuous_invFun := continuous_map_iso e.symm }

end Points

/-- Points of the product of two represented presheaves have the topology of the
actual scheme fibre product over the base. -/
def productSchemePointsHomeomorph (U V : Over S) :
    letI := pointTopology ((schemeYoneda S).obj U ⨯ (schemeYoneda S).obj V)
    Points ((schemeYoneda S).obj U ⨯ (schemeYoneda S).obj V) ≃ₜ
      (Limits.pullback U.hom V.hom : Scheme.{u}) := by
  letI := pointTopology ((schemeYoneda S).obj U ⨯ (schemeYoneda S).obj V)
  letI := pointTopology ((schemeYoneda S).obj (U ⨯ V))
  exact (Points.isoHomeomorph (PreservesLimitPair.iso (schemeYoneda S) U V).symm).trans
    ((schemePointsHomeomorph (U ⨯ V)).trans (Over.prodLeftIsoPullback U V).hom.homeomorph)

end Langlands.AlgebraicGeometry.AlgebraicSpace
