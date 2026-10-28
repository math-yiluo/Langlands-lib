import Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentStatement
import Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionProof
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Unique descent of distributions supported on a closed subset -/

namespace Langlands.HarmonicAnalysis.Distribution

universe u

variable {X : Type u} [TopologicalSpace X] {Z : Set X}

/-- A surjective closed restriction identifies distributions on the closed
subset with the ambient functionals annihilating its restriction kernel. -/
theorem closedPushforwardSupported_bijective_of_surjective
    (hZ : IsClosed Z)
    (hsurj : Function.Surjective (SchwartzBruhat.restrictClosed hZ)) :
    Function.Bijective (closedPushforwardSupported hZ) := by
  let r := SchwartzBruhat.restrictClosed hZ
  constructor
  · intro D E h
    apply LinearMap.dualMap_injective_of_surjective hsurj
    exact congrArg (fun S : supportedOn Z => (S : Distribution X)) h
  · intro T
    have hker : LinearMap.ker r ≤ LinearMap.ker (T : Distribution X) := by
      intro f hf
      apply T.property f
      intro z hz
      change r f = 0 at hf
      exact congrArg (fun g : SchwartzBruhat Z => g ⟨z, hz⟩) hf
    let D : Distribution Z :=
      ((LinearMap.ker r).liftQ (T : Distribution X) hker).comp
        (r.quotKerEquivOfSurjective hsurj).symm.toLinearMap
    refine ⟨D, ?_⟩
    apply Subtype.ext
    ext f
    change ((LinearMap.ker r).liftQ (T : Distribution X) hker)
      ((r.quotKerEquivOfSurjective hsurj).symm (r f)) = T.val f
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- The actual closed pushforward is a bijection onto the pointwise-supported
algebraic distributions, for every space and closed subset in the statement. -/
theorem closedSupportedDescent : ClosedSupportedDescentStatement.{u} := by
  intro X _ _ _ _ Z hZ
  exact closedPushforwardSupported_bijective_of_surjective hZ
    (SchwartzBruhat.closedRestrictionSurjective X Z hZ)

end Langlands.HarmonicAnalysis.Distribution
