import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitSections
import Langlands.GroupScheme.Rational.SemistandardSpectralDynamicCoverageProof
import Langlands.Representation.Aubert.General.DynamicInductionExactness

/-! # Continuity of the literal semistandard Levi projection -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

/-- The fixed-torus dynamic realization gives the continuous projection on the
literal parabolic and Levi point subgroups. -/
theorem projectionContinuity {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
    [ValuativeRel F] [TopologicalSpace F] [IsAffineHom G.X.hom] :
    ProjectionContinuityStatement (i := i) := by
  intro _ hG hi p
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsSeparated G.X.hom := hG.isSeparated
  obtain ⟨ζ, rfl⟩ := semistandardSpectralDynamicCoverage F G hG S i hi p
  exact Aubert.General.continuous_dynamic_projection F G (CommGroupScheme.groupHom ζ ≫ i)

end Langlands.HarishChandraSchwartz.RationalSemistandard
