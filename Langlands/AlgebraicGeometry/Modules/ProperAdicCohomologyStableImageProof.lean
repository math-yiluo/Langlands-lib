import Langlands.AlgebraicGeometry.Modules.ProperAdicCohomologyStableImageStatement
import Langlands.AlgebraicGeometry.Modules.ProperAdicArtinRees
import Langlands.AlgebraicGeometry.OrderedAffineCoverCompact

/-! # Stable images of actual proper adic cohomology -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- Stacks Lemma 30.20.4(3): for a coherent module on a proper scheme over a noetherian
ring, the image from a sufficiently high adic quotient in degree `p` cohomology is the
image from the original module, with one bound on the difference of indices. -/
theorem properAdicCohomologyStableImage : ProperAdicCohomologyStableImageStatement.{u} := by
  intro R _ _ I X f hf M hM hfin p
  have := hf
  have := hM
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := Scheme.OrderedAffineCover.ofCompactSpace X
  obtain ⟨c, hc⟩ := ProperAdicArtinRees.exists_uniform_cechBoundaryLift f M hfin 𝒰 I p
  exact ⟨c, IdealAdic.adic_stable_image_of_cech_boundary_lift f M 𝒰 I p c hc⟩

end Langlands.AlgebraicGeometry.Modules
