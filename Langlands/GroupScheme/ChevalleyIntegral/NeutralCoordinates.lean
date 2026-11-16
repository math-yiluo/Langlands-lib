import Langlands.GroupScheme.ChevalleyIntegral.IntegralCoordinates
import Langlands.GroupScheme.IntegralModel.KernelCentralizerTorus
import Langlands.GroupScheme.GeometricConnectedness

/-! # Coordinate tori and field comparisons in the relative neutral model -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ChevalleyIntegral

open SplitExistence SplitExistence.ChevalleyData

variable {I J : Type u} [Fintype I] [DecidableEq I]
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base}
  (D : ChevalleyData P b)
  (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K)
  {N : GroupScheme (Spec (CommRingCat.of R))}
  {iN : N ⟶ (genericModel D R K C).group}
  (hi : IsRelativeIdentityComponent (genericModel D R K C).group iN)

/-- The full integral coordinate torus factors through the relative neutral component. -/
def neutralCoordinateTorus : splitTorus (Spec (CommRingCat.of R)) I ⟶ N := by
  let : GeometricallyConnected (splitTorus (Spec (CommRingCat.of R)) I).X.hom :=
    (isSplitTorus_splitTorus I).geometricallyConnected
  exact Classical.choose (hi.exists_hom_lift (integralCoordinateTorus D R K C))

@[reassoc]
theorem neutralCoordinateTorus_comp :
    neutralCoordinateTorus D R K C hi ≫ iN = integralCoordinateTorus D R K C := by
  let : GeometricallyConnected (splitTorus (Spec (CommRingCat.of R)) I).X.hom :=
    (isSplitTorus_splitTorus I).geometricallyConnected
  exact Classical.choose_spec (hi.exists_hom_lift (integralCoordinateTorus D R K C))

/-- Passing to the neutral component retains closedness of the full coordinate torus. -/
theorem neutralCoordinateTorus_closed :
    IsClosedSubgroup (neutralCoordinateTorus D R K C hi) := by
  apply hi.isClosedSubgroup_of_comp
  rw [neutralCoordinateTorus_comp]
  exact integralCoordinateTorus_closed D R K C

variable [GeometricallyConnected N.X.hom]
  (k : Type u) [Field k] [Algebra R k] (H : D.ChevGroup k)

/-- The actual field Chevalley group embeds into the field fibre of the neutral model. -/
def neutralFieldEmbedding :
    H.H ⟶ (baseChange (Spec.algebraMap R k)).obj N := by
  let : Smooth H.H.X.hom := H.smooth
  let : IsAffineHom H.H.X.hom := H.affine
  let : ConnectedSpace H.H.X.left := H.connected
  let : GeometricallyConnected H.H.X.hom := H.H.geometricallyConnected_of_connected
  exact Classical.choose ((hi.baseChange (Spec.algebraMap R k)).exists_hom_lift
    (fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H))

omit [Fintype I] [DecidableEq I] in
@[reassoc]
theorem neutralFieldEmbedding_comp :
    neutralFieldEmbedding D R K C hi k H ≫ (baseChange (Spec.algebraMap R k)).map iN =
      fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H := by
  let : Smooth H.H.X.hom := H.smooth
  let : IsAffineHom H.H.X.hom := H.affine
  let : ConnectedSpace H.H.X.left := H.connected
  let : GeometricallyConnected H.H.X.hom := H.H.geometricallyConnected_of_connected
  exact Classical.choose_spec ((hi.baseChange (Spec.algebraMap R k)).exists_hom_lift
    (fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H))

omit [Fintype I] [DecidableEq I] in
/-- The neutral field embedding is a closed subgroup. -/
theorem neutralFieldEmbedding_closed :
    IsClosedSubgroup (neutralFieldEmbedding D R K C hi k H) := by
  apply (hi.baseChange (Spec.algebraMap R k)).isClosedSubgroup_of_comp
  rw [neutralFieldEmbedding_comp]
  exact fieldEmbedding_closed D R K C k (CommRingCat.ofHom (algebraMap R k)) H

/-- The field embedding preserves the full coordinate torus of the single neutral family. -/
theorem coordinateTorusHom_neutralFieldEmbedding :
    coordinateTorusHom H ≫ neutralFieldEmbedding D R K C hi k H =
      splitTorus.baseChangeHom (K := k) N I (neutralCoordinateTorus D R K C hi) := by
  have : Mono ((baseChange (Spec.algebraMap R k)).map iN).hom.hom :=
    (hi.baseChange (Spec.algebraMap R k)).mono_hom
  apply Grp.hom_ext
  apply (cancel_mono ((baseChange (Spec.algebraMap R k)).map iN).hom.hom).mp
  change ((coordinateTorusHom H ≫ neutralFieldEmbedding D R K C hi k H) ≫
      (baseChange (Spec.algebraMap R k)).map iN).hom.hom =
    (splitTorus.baseChangeHom (K := k) N I (neutralCoordinateTorus D R K C hi) ≫
      (baseChange (Spec.algebraMap R k)).map iN).hom.hom
  rw [Category.assoc, neutralFieldEmbedding_comp,
    coordinateTorusHom_fieldEmbedding]
  dsimp only [splitTorus.baseChangeHom]
  rw [Category.assoc, ← Functor.map_comp, neutralCoordinateTorus_comp]

/-- Isomorphic neutral field embeddings give the comparisons for the same neutral family
and its full coordinate torus chosen over the integral base. -/
theorem hasFieldComparisons_of_neutralFieldEmbedding_isIso [Finite J]
    (h : ∀ (k : Type u) [Field k] [Algebra R k],
      ∃ H : D.ChevGroup k, IsIso (neutralFieldEmbedding D R K C hi k H)) :
    HasFieldComparisons D N (neutralCoordinateTorus D R K C hi) := by
  intro k _ _
  obtain ⟨H, hH⟩ := h k
  let := hH
  let e := asIso (neutralFieldEmbedding D R K C hi k H)
  refine ⟨H, e.symm, ?_⟩
  rw [← coordinateTorusHom_neutralFieldEmbedding D R K C hi k H]
  change (coordinateTorusHom H ≫ e.hom) ≫ e.inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Langlands.GroupScheme.ChevalleyIntegral
