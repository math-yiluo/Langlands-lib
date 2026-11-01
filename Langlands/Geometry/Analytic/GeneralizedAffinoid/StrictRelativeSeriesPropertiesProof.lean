import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesComparison
import Langlands.Geometry.Analytic.TateNoetherian
import Langlands.Geometry.Analytic.ClosedIdealsBanach
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictRelativeSeriesPropertiesStatement

/-! # Noetherianity and closed ideals of strict relative unit-radius series -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- The appended unit polyradius remains the unit polyradius. -/
private theorem strict_unit_append (P : PresentedStrictAffinoidAlgebra K) (m : ℕ) :
    (ofStrict K P).polyradius.append (PositivePolyradius.unit (Fin m)) =
      PositivePolyradius.unit (Fin (P.arity + m)) := by
  change (PositivePolyradius.unit (Fin P.arity)).append
    (PositivePolyradius.unit (Fin m)) = PositivePolyradius.unit (Fin (P.arity + m))
  unfold PositivePolyradius.append PositivePolyradius.unit
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- Noetherianity transports along the actual enlarged quotient presentation
and the published relative-series comparison. No scalar witness is needed. -/
theorem strict_relative_series_noetherian
    (P : PresentedStrictAffinoidAlgebra K) (m : ℕ) :
    IsNoetherianRing (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin m))
      (ofStrict K P)) := by
  let A := ofStrict K P
  let s := PositivePolyradius.unit (Fin m)
  have : IsNoetherianRing (GeneralizedTateAlgebra (A.polyradius.append s) K) := by
    change IsNoetherianRing (GeneralizedTateAlgebra
      ((ofStrict K P).polyradius.append (PositivePolyradius.unit (Fin m))) K)
    rw [strict_unit_append K P m]
    exact isNoetherianRing_of_ringEquiv (StrictTateAlgebra (Fin (P.arity + m)) K)
      (unitAlgEquiv K).symm.toRingEquiv
  have : IsNoetherianRing (Adjoin.algebra K A s ∅) :=
    isNoetherianRing_of_surjective
      (GeneralizedTateAlgebra (A.polyradius.append s) K) (Adjoin.algebra K A s ∅)
      (presentationMap K (Adjoin.algebra K A s ∅)).toAlgHom.toRingHom
      (presentationMap_surjective K (Adjoin.algebra K A s ∅))
  exact isNoetherianRing_of_surjective _ _
    (Adjoin.relativeSeriesMap K A s).toAlgHom.toRingHom
    (Adjoin.relativeSeriesMap_surjective K A s)

/-- The explicit scalar witness extends the given normed-field structure;
all ideals in the actual relative series algebra are closed. -/
theorem strict_relative_series_closed (hK : ∃ c : K, 1 < ‖c‖)
    (P : PresentedStrictAffinoidAlgebra K) (m : ℕ)
    (I : Ideal (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin m)) (ofStrict K P))) :
    IsClosed (I : Set (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin m))
      (ofStrict K P))) := by
  let : NontriviallyNormedField K := { (inferInstance : NormedField K) with non_trivial := hK }
  have := strict_relative_series_noetherian K P m
  exact isClosed_ideal_of_noetherian_banach (K := K) I

/-- The exact published, internally quantified target. -/
theorem strict_relative_series_properties :
    StrictRelativeSeriesPropertiesStatement.{u} := by
  intro K _ _ _ hK P m
  exact ⟨strict_relative_series_noetherian K P m,
    strict_relative_series_closed K hK P m⟩

end Langlands.Analytic.PresentedAffinoidAlgebra
