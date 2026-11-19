import Langlands.GroupScheme.RelativeLevi.FaceCoverQuotientDescent
import Langlands.GroupScheme.RelativeLevi.FaceCoverEndpoints
import Langlands.GroupScheme.RelativeUnipotent.FiltrationTermination
import Langlands.GroupScheme.RelativeUnipotent.SeriesTransport
import Langlands.GroupScheme.RelativeUnipotent.RadicalFiltrationStatement

/-! # Finite series from the actual descended face quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

namespace FiniteParabolicFaceCover

variable {S : Scheme.{u}} [IsAffine S] {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)
  (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

/-- The actual global quotients are the only remaining input to the finite
series construction; the length is the constructed common face-weight bound. -/
theorem hasVectorBundleSeries_of_vectorBundleQuotients
    (hV : ∀ d, RelativeUnipotent.IsVectorBundleAdditive
      (D.globalFaceQuotientData r hG hp hr d).group) :
    RelativeUnipotent.HasVectorBundleSeries D.bound U := by
  have hs : RelativeUnipotent.HasVectorBundleSeries D.bound
      (D.globalTerm r hG hp hr 0) := by
    refine RelativeUnipotent.hasVectorBundleSeries_of_segment
      (D.globalTerm r hG hp hr) (D.globalTermStep r hG hp hr) ?_ D.bound 0
      (by
        rw [Nat.zero_add]
        exact D.globalTerm_bound_range_id_eq_bot r hG hp hr)
    · intro d
      exact ⟨(D.globalFaceQuotientData r hG hp hr d).group,
        (D.globalFaceQuotientData r hG hp hr d).projection,
        D.isClosedSubgroup_globalTermStep r hG hp hr d,
        D.smooth_closedTermRepresentative r hG hp hr (d + 1),
        D.isNormal_globalTermStep r hG hp hr d,
        (D.globalFaceQuotientData r hG hp hr d).quotient, hV d⟩
  exact hs.of_iso (D.globalTermZeroIso r hG hp hr)

/-- The exact supplied-radical finite-series conclusion after the remaining
vector-bundle identification of the actual constructed quotients. -/
theorem hasFiniteVectorBundleSeries_of_vectorBundleQuotients
    (hV : ∀ d, RelativeUnipotent.IsVectorBundleAdditive
      (D.globalFaceQuotientData r hG hp hr d).group) :
    RelativeUnipotent.HasFiniteVectorBundleSeries U :=
  ⟨D.bound, D.hasVectorBundleSeries_of_vectorBundleQuotients r hG hp hr hV⟩

end FiniteParabolicFaceCover

/-- A precise reduction of the unchanged arbitrary-universe target to the
vector-bundle predicate for the actual effectively descended face quotients. -/
theorem relativeUnipotentRadicalFiltration_of_globalFaceQuotients
    (hV : ∀ (S : Scheme.{u}) [IsAffine S] (G H U : GroupScheme S)
      [IsAffineHom G.X.hom] (p : H ⟶ G) (r : U ⟶ H)
      (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
      (hr : IsRelativeUnipotentRadical r) (D : FiniteParabolicFaceCover p) (d : ℕ),
      RelativeUnipotent.IsVectorBundleAdditive
        (D.globalFaceQuotientData r hG hp hr d).group) :
    RelativeUnipotentRadicalFiltrationStatement.{u} := by
  intro S _ G H U p r hG hp hr
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let D := finiteParabolicFaceCover p hG hp
  exact D.hasFiniteVectorBundleSeries_of_vectorBundleQuotients r hG hp hr
    (hV S G H U p r hG hp hr D)

end Langlands.GroupScheme.RelativeLevi
