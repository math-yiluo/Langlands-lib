import Langlands.AlgebraicGeometry.ConnectedCoproductFactorization
import Langlands.AlgebraicGeometry.FlatReducedDvrConnectedness
import Langlands.AlgebraicGeometry.Picard.GenericFractionField
import Langlands.AlgebraicGeometry.SmoothReducedBase
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Generic pullbacks of connected étale schemes over a DVR -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- The map from a chosen fraction field is dominant. -/
theorem isDominant_fractionFieldMap
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsDominant (Spec.algebraMap R K) := by
  let S := Spec (CommRingCat.of R)
  let e := fractionFieldGenericPointIso (CommRingCat.of R) K
  have hd : IsDominant (S.fromSpecResidueField (genericPoint S)) := by
    constructor
    change Dense (Set.range (S.fromSpecResidueField (genericPoint S)))
    rw [Scheme.range_fromSpecResidueField]
    exact dense_iff_closure_eq.mpr (genericPoint_closure S)
  have hc : IsDominant (e.hom ≫ S.fromSpecResidueField (genericPoint S)) := inferInstance
  simpa only [e, S, fractionFieldGenericPointIso_hom_fromSpecResidueField] using hc

/-- The actual generic pullback for a specified fraction field identifies with
the residue-field fibre over the generic point, over the original base. -/
def genericPullbackIsoFiber
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {U : Scheme.{u}} (q : U ⟶ Spec (CommRingCat.of R)) :
    (pullback q (Spec.algebraMap R K) : Scheme.{u}) ≅
      q.fiber (genericPoint (Spec (CommRingCat.of R))) := by
  let S := Spec (CommRingCat.of R)
  let e := fractionFieldGenericPointIso (CommRingCat.of R) K
  let m : pullback q (Spec.algebraMap R K) ⟶ q.fiber (genericPoint S) :=
    pullback.map q (Spec.algebraMap R K) q (S.fromSpecResidueField (genericPoint S))
      (𝟙 U) e.hom (𝟙 S) (by simp [S]) (by
        dsimp only [e, S]
        simpa only [Category.comp_id] using
          (fractionFieldGenericPointIso_hom_fromSpecResidueField (CommRingCat.of R) K).symm)
  have hm : IsIso m := by dsimp only [m]; infer_instance
  exact asIso m

/-- A connected étale scheme over a DVR has connected generic pullback for any
specified fraction field. -/
theorem connectedSpace_etale_genericPullback
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {U : Scheme.{u}} [ConnectedSpace U] (q : U ⟶ Spec (CommRingCat.of R))
    [Etale q] : ConnectedSpace (pullback q (Spec.algebraMap R K) : Scheme.{u}) := by
  let S := Spec (CommRingCat.of R)
  have hred : IsReduced (q.fiber (IsLocalRing.closedPoint R)) :=
    SmoothReducedBase.isReduced_of_smooth_of_isReduced
      (q.fiberToSpecResidueField (IsLocalRing.closedPoint R))
  have hc : ConnectedSpace (q.fiber (genericPoint S)) := by
    change ConnectedSpace (q.fiber (genericPoint (Spec (CommRingCat.of R))))
    rw [genericPoint_eq_bot_of_affine]
    exact FlatReducedDvrConnectedness.connectedSpace_genericFiber_of_reduced_specialFiber R U q
  exact (genericPullbackIsoFiber R K q).hom.homeomorph.connectedSpace_iff.mpr hc

end Langlands.AlgebraicGeometry
