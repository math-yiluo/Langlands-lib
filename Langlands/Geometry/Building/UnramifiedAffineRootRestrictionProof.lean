import Langlands.Geometry.Building.UnramifiedZeroJumpLiftReducedProof
import Langlands.Geometry.Building.UnramifiedZeroJumpLiftMultipliableReduction
import Langlands.Geometry.Building.UnramifiedZeroJumpFieldComparisonProof
import Langlands.Geometry.Building.UnramifiedZeroJumpDescentProof

/-! # Unramified descent of affine roots

Proof of `Langlands.Geometry.Building.UnramifiedAffineRootRestrictionStatement` (Kaletha–Prasad,
Proposition 9.4.28, set form): the reduction `unramifiedAffineRootRestriction_of_zeroJumps`
applied to the published proofs of its three pointwise zero-value jump inputs. -/

universe u

namespace Langlands.Geometry.Building

/-- **Unramified descent of affine roots.** Along a Galois-fixed lift of the apartment over `F`
into the apartment over `F^ur`, the relative affine roots are exactly the nonconstant
restrictions of the absolute affine roots. -/
theorem unramifiedAffineRootRestriction : UnramifiedAffineRootRestrictionStatement.{u} :=
  unramifiedAffineRootRestriction_of_zeroJumps unramifiedZeroJumpLiftReduced
    (unramifiedZeroJumpLiftMultipliable_of_fieldComparison unramifiedZeroJumpFieldComparison)
    unramifiedZeroJumpDescent

end Langlands.Geometry.Building
