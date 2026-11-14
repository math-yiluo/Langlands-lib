import Langlands.Geometry.Building.Kottwitz.FundamentalGroupStatement
import Langlands.Geometry.Building.Kottwitz.InertiaFunctoriality
import Langlands.Geometry.Building.Kottwitz.TorusFundamentalComparisonProof

/-! # The residual Galois comparison of the torus inertia targets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

/-- The actual torus comparison descends with its inverse and residual Galois action. -/
theorem torusInertiaComparison_of_fundamentalComparison
    (h : TorusFundamentalComparisonStatement.{u}) :
    TorusInertiaComparisonStatement.{u} := by
  intro k K E _ _ _ _ _ _ _ _ _ _ T hT
  obtain ⟨_, hspec, hbij, hgal⟩ := h k E T hT
  let e : (fundamentalGroupGalois k T.toGrp E
      hT.isConnectedReductive_of_fieldSplitting).Equiv
        (cocharacterLattice.galoisRepresentation k E T) :=
    Representation.Equiv.mk
      (LinearEquiv.ofBijective (torusFundamentalComparison k E T hT) hbij)
      (fun σ => LinearMap.ext (hgal σ))
  let m := (inertiaEquiv k K E e).toLinearMap
  have hm : IsTorusInertiaComparison k K E T hT m := by
    intro x
    exact inertiaEquiv_projection k K E e x
  have huniq : ∀ n, IsTorusInertiaComparison k K E T hT n → n = m := by
    intro n hn
    exact inertiaMap_unique k K E e.toIntertwiningMap n hn
  have hex : ∃! n, IsTorusInertiaComparison k K E T hT n :=
    ⟨m, hm, huniq⟩
  have hselected : IsTorusInertiaComparison k K E T hT
      (torusInertiaComparison k K E T hT) :=
    Classical.epsilon_spec hex.exists
  have heq : torusInertiaComparison k K E T hT = m := huniq _ hselected
  refine ⟨hex, hselected, ?_, ?_⟩
  · rw [heq]
    exact (inertiaEquiv k K E e).bijective
  · intro σ x
    rw [heq]
    exact inertiaMap_equivariant k K E e.toIntertwiningMap σ x

/-- The canonical torus comparison is an equivalence of residual inertia targets. -/
theorem torusInertiaComparison_proof : TorusInertiaComparisonStatement.{u} :=
  torusInertiaComparison_of_fundamentalComparison torusFundamentalComparison_proof

end Langlands.Geometry.Building.Kottwitz
