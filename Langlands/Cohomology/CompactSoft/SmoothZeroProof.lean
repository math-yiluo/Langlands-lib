import Langlands.Cohomology.CompactSoft.FamilyCutoff
import Langlands.Cohomology.CompactSoft.SmoothZeroBridge
import Langlands.Sheaf.Equivariant.CoinducedFamilies.Coordinates

/-!
# C-softness of the degree-zero smooth Godement sheaf
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory Langlands.Sheaf.Equivariant

universe u

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]

/-- The ordinary sheaf underlying the degree-zero smooth Godement sheaf is
c-soft, with exactly the hypotheses of the published statement. -/
theorem smoothGodementZeroCSoft : SmoothGodementZeroCSoftStatement R G X := by
  apply CompactSoft.smoothGodementZeroCSoft_of_coinducedZero
  intro F
  exact CompactSoft.isCSoft_smooth_of_family
    (CoinducedFamilies.Coefficients F) (CoinducedFamilies.coinducedZero F)
    (CoinducedFamilies.read F) (CoinducedFamilies.read_map F)

end Langlands.Cohomology
