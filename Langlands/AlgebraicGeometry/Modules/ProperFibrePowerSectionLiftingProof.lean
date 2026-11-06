import Langlands.AlgebraicGeometry.Modules.ProperFibrePowerSectionLiftingLocalCase
import Langlands.AlgebraicGeometry.Modules.IdealAdicFibreSerre
import Langlands.AlgebraicGeometry.Modules.ProperAdicCohomologyStableImageProof

/-! # Eventual lifting of fibre sections of a specified ample power -/

universe u

namespace Langlands.AlgebraicGeometry.Modules

/-- Uniform first-cohomology vanishing on the maximal-ideal layers of large powers of a
line bundle that is ample on the closed fibre. -/
theorem localAdicLayerVanishing : LocalAdicLayerVanishing.{u} :=
  fun _ _ _ _ _ _ _ L _ _ hpb hL =>
    (IdealAdic.exists_uniform_vanishing_adicLayer_maximalIdeal hpb L hL).imp
      fun _ h n hn k => h n hn k 0

/-- The section-lifting statement, given the stable-image statement. -/
theorem properFibrePowerSectionLifting_of_stableImage
    (hs : ProperAdicCohomologyStableImageStatement.{u}) :
    ProperFibrePowerSectionLiftingStatement.{u} :=
  properFibrePowerSectionLifting_of_local
    (localClosedFibrePowerSectionLifting_of_layerVanishing hs localAdicLayerVanishing)

/-- The neighbourhood form of the case `F = O_X` of Stacks Lemma 30.21.3 (tag 02OF):
sections of every sufficiently high power of a line bundle that is ample on a fibre lift
over the inverse image of an affine neighbourhood of the base point. -/
theorem properFibrePowerSectionLifting : ProperFibrePowerSectionLiftingStatement.{u} :=
  properFibrePowerSectionLifting_of_stableImage properAdicCohomologyStableImage

end Langlands.AlgebraicGeometry.Modules
