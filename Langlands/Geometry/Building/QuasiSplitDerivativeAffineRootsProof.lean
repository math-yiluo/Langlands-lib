import Langlands.Geometry.Building.QuasiSplitDerivativeAffineRootsStatement
import Langlands.Geometry.Building.QuasiSplitBoundedApartmentExistence
import Langlands.Geometry.Building.IntegerBoundedDerivativeAffineRoots
import Langlands.Geometry.Building.IntegerOmegaApartmentUniqueness
import Langlands.Geometry.Building.UnramifiedOmegaGaloisStable

/-! # Full ordinary derivatives of quasi-split integer apartments -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Every full-V6-compatible quasi-split integer apartment has all actual
relative-root forms as derivatives of ordinary affine roots. -/
theorem quasiSplitDerivativeAffineRoots :
    QuasiSplitDerivativeAffineRootsStatement.{u} := by
  intro k _ v hv hH G _ hQS S i hi
  let := mono_of_isMaximalSplitTorus hi
  intro D C hD
  let := ValuativeRel.ofValuation v
  let := Valuation.Compatible.ofValuation v
  obtain ⟨E, C₀, hE, hbounded⟩ :=
    quasiSplitAllDepthBoundedApartmentExistence k v hv hH G hQS S i hi
  have hEC : IntegerValuation.IsOmegaCompatible v E C :=
    hE.of_centralizerDatum v C
  have hDE : D = E :=
    hD.eq_of_isMaximalSplitTorus hEC hQS.isConnectedReductive hi
  subst E
  let B : IntegerValuationBuildingData v G :=
    { isConnectedReductive := hQS.isConnectedReductive
      S := S
      i := i
      isMaximalSplitTorus := hi
      apartment := D
      centralizer := C
      isOmegaCompatible := hD }
  have hB : B.HasBoundedRootFiltrations := by
    intro a
    exact ⟨Classical.arbitrary D.Apartment, 0,
      hbounded (Classical.arbitrary D.Apartment) a a.property 0⟩
  have hlarge : ∃ t : k, (1 : k) <ᵥ t := by
    obtain ⟨t, ht⟩ := hv (WithZero.exp (1 : ℤ))
    refine ⟨t, ?_⟩
    rw [v.one_vlt_iff, ht, WithZero.one_lt_exp_iff]
    norm_num
  exact B.derivativeRoots_affineRoots_of_bounded hB hlarge

end Langlands.Geometry.Building
