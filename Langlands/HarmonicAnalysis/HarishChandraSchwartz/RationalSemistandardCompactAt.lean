import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDynamicIwasawa
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProjectionContinuityProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceConstants

/-! # Semistandard compact pictures at one specified Iwasawa compact -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Aubert.General
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.CompactData

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
  {K : OpenSubgroup (rationalPoints G)} (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

/-- Construct each literal compact picture at exactly the specified
minimal Iwasawa compact. -/
def atMinimalIwasawa (p : SemistandardSpectralIndex i) : CompactData p where
  compact := K
  isCompact := hK
  projection_continuous := projectionContinuity ‹IsNonarchimedeanLocalField F› hG hi p
  factorization := by
    let r := CocharacterPresentation.ofCoverage hG semistandardSpectralDynamicCoverage hi p
    have hp : (Dynamic.parabolic r.hom).rationalPoints = parabolic p :=
      congrArg SubgroupFunctor.rationalPoints r.parabolic_eq
    exact factorization_subtype
      (hp ▸ isIwasawaPair_dynamicParabolic_of_minimal hG hi hν hPK r.hom)

@[simp] theorem atMinimalIwasawa_compact (p : SemistandardSpectralIndex i) :
    (atMinimalIwasawa hG hi hν hK hPK p).compact = K := rfl

end Langlands.HarishChandraSchwartz.RationalSemistandard.CompactData
