import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsClosedLocallyCompactStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsCompactProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianFinitePointProperProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeIntegralPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartSeparated
import Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedFieldProof
import Mathlib.Analysis.Normed.Field.ProperSpace

/-!
# Closedness of integral points over locally compact fields

Conrad's Corollary 5.7, closedness, when the field is locally compact. Injectivity is the
published change-of-coefficients injectivity for separated spaces. The image is quasi-compact
by the published quasi-compactness part of Corollary 5.7, and the rational points of the
separated generic fibre are Hausdorff by Proposition 5.4, because a locally compact
nontrivially normed field is complete, hence henselian. A quasi-compact subset of a
Hausdorff space is closed.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace HenselianIntegralPointsClosedOfLocallyCompact

/-- A separated algebraic space is quasi-separated: a closed immersion is quasi-compact. -/
theorem isQuasiSeparated_of_isSeparated {S : Scheme.{u}} {X : AlgebraicSpace S}
    (hX : IsSeparated X) : IsQuasiSeparated X :=
  HenselianFinitePointProperProof.isQuasiSeparated_of_isSeparated hX

end HenselianIntegralPointsClosedOfLocallyCompact

open HenselianIntegralPointsClosedOfLocallyCompact in
/-- **Conrad's Corollary 5.7, closedness over a locally compact field.** For a locally compact
nontrivially normed field `K` whose closed unit ball is a henselian subring `O`, and a separated
algebraic space `X` over `Spec O`, the map `X(O) → X_K(K)` is injective, and its image is closed
for the étale-chart topology when `X` is of finite type. -/
theorem henselianIntegralPointsClosedOfLocallyCompact :
    HenselianIntegralPointsClosedOfLocallyCompactStatement.{u} := by
  intro K _ O hO hH hLC X hXsep ι
  refine ⟨?_, fun hXft => ?_⟩
  · have hinj : Function.Injective (Algebra.ofId O K) := fun x y h => Subtype.ext h
    exact (baseChangeRingPointsEquiv O K K X).symm.injective.comp
      (RelativeIntegralPoints.changeRing_injective hXsep (Algebra.ofId O K) hinj)
  · have hXqs : IsQuasiSeparated X := isQuasiSeparated_of_isSeparated hXsep
    have hcpt := henselianIntegralPointsCompact K O hO hH hLC X hXqs hXft
    have : LocallyCompactSpace K := hLC
    have : ProperSpace K :=
      ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    have hK : PointTopology.IsHenselianValuedField K :=
      PointTopology.completeHenselianValuedField K
    have hXlft : LocallyOfFiniteTypeOverBase X := by
      obtain ⟨U, a, ha, hs, hU⟩ := hXft.exists_atlas
      exact ⟨U, a, ha, hs, hU.1⟩
    have hXK : IsQuasiSeparatedLocallyFiniteType K (baseChange (Spec.algebraMap O K) X) :=
      And.intro (IsQuasiSeparated.baseChange hXqs) (HasAtlasProperty.baseChange hXlft)
    let : TopologicalSpace (RingPoints K (baseChange (Spec.algebraMap O K) X) K) :=
      etaleChartTopology K (baseChange (Spec.algebraMap O K) X)
    have := t2Space_etaleChartTopology hK hXK (IsSeparated.baseChange hXsep)
    exact hcpt.isClosed

end Langlands.AlgebraicGeometry.AlgebraicSpace
