import Langlands.Geometry.Building.OmegaCompatibleApartmentUniquenessStatement
import Langlands.Geometry.Building.OmegaCompatibleApartmentRigidity
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Proof of uniqueness of the full omega-compatible apartment class -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **KP Proposition 6.2.6**, bundled: two full omega-compatible apartment classes for the
same actual maximal split torus and actual centralizer datum are equal. The opposite factor
pairs needed by `omegaCompatibleApartmentRigidity` come from `rootRankOneFactorization`. -/
theorem omegaCompatibleApartmentUniqueness :
    OmegaCompatibleApartmentUniquenessStatement.{u} := by
  intro F _ _ _ _ G _ hG S i _ hi C D E hD hE
  have hrank : RelativeRoot.HasRankOneFactorization i :=
    rootRankOneFactorization.{u} F G hG S i hi
  have hpair : RelativeRoot.HasOppositeFactorPairs i :=
    fun a ha x hx hx1 => (hrank a ha x hx hx1).1.exists
  exact omegaCompatibleApartmentRigidity.{u} F G hG S i hi hpair C D E hD hE

end Langlands.Geometry.Building
