import Langlands.GroupScheme.Absolute.BruhatCoveringSteps
import Langlands.GroupScheme.HomogeneousQuotientProof

/-! # Actual homogeneous quotients by a prescribed Borel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {B G : GroupScheme (Spec (CommRingCat.of k))}
variable {b : B ⟶ G} (hb : IsBorelSubgroup b)

include hb

/-- Choose an actual homogeneous quotient by this particular Borel. -/
def IsBorelSubgroup.homogeneousQuotient [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient b :=
  Classical.choice (by
    obtain ⟨Q, q, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩ :=
      smoothSubgroupQuotientExistence k G B b hb.isClosedSubgroup hb.smooth
    exact ⟨⟨Q, q, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩⟩)

/-- The parabolic-quotient properness statement applies to the supplied quotient
model of a prescribed Borel over an algebraically closed field. -/
theorem IsBorelSubgroup.quotient_isProper_of_parabolicQuotient
    [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left]
    (hproper : ParabolicSubgroupQuotientProperStatement.{u})
    (R : HomogeneousQuotientFromEmbedding.HomogeneousQuotient b) :
    IsProper R.scheme.hom :=
  hproper k G inferInstance B b (BruhatCovering.isParabolicSubgroup_of_isBorelSubgroup hb)
    R.scheme R.projection R.separated R.locallyOfFiniteType R.quasiCompact
    R.smooth_projection R.surjective_projection R.quasiCompact_projection R.fibers

/-- Properness of the chosen actual Borel quotient, under the explicit general
parabolic-quotient properness statement. -/
theorem IsBorelSubgroup.homogeneousQuotient_isProper_of_parabolicQuotient
    [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left]
    (hproper : ParabolicSubgroupQuotientProperStatement.{u}) :
    IsProper hb.homogeneousQuotient.scheme.hom :=
  hb.quotient_isProper_of_parabolicQuotient hproper hb.homogeneousQuotient

end Langlands.GroupScheme
