import Langlands.Representation.CompactCoefficient.AllProjectiveLifting
import Langlands.Representation.Induction.OpenAdjunction
import Langlands.Representation.Induction.SplitStagesComparison
import Langlands.Representation.CuspidalSupport.RationalUniversalProgenerator
import Langlands.Representation.CuspidalSupport.RationalInertiaLifting

/-! Projectivity of the actual norm-kernel compact induction from compact coefficients. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Compact induction of a compact-coefficient smooth object from an open subgroup
is projective at the actual function-carrier universe, with no size restriction
on the original inducing carrier. -/
theorem projective_compactInduced_of_compactCoefficients
    (H : Subgroup G) (hH : IsOpen (H : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ H)
    (hc : HasCompactSmoothDualCoefficients A.representation) :
    Projective (SmoothRep.of (compactInduced H A.representation)
      (compactInduced_smooth H A.representation)) := by
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let A' := SmoothRep.universeLift.{uG} A
  have hc' : HasCompactSmoothDualCoefficients A'.representation :=
    (hasCompactSmoothDualCoefficients_iff_of_equiv
      (SmoothRep.universeLiftEquiv.{uG} A)).mp hc
  have hP : Projective ((smoothCompactInduction.{0, uG, uV} ℂ H).obj A') :=
    projective_smoothCompactInduction H hH A'
      (CompactCoefficient.projective_of_compactCoefficients A' hc')
  exact Projective.of_iso (SmoothRep.mkIso
    (compactInducedEquiv H (SmoothRep.universeLiftEquiv.{uG} A))).symm hP

end Langlands.Induction

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalUniversalProjectivityTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalUniversalProjectivityTopologicalGroup : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))

/-- The actual full-restriction alternative is ambient projective whenever its
entire norm-kernel restriction has compact smooth-dual coefficients. -/
theorem rationalNormKernelCompactInduction_projective
    (hc : HasCompactSmoothDualCoefficients
      (π.representation.comp (rationalCommonNormKernel G).subtype)) :
    Projective (rationalNormKernelCompactInduction G π) := by
  let : T2Space F := BruhatTits.localField_t2Space F
  let : TotallyDisconnectedSpace F := BruhatTits.localField_totallyDisconnectedSpace F
  let : T2Space (GroupScheme.rationalPoints G) := rationalPoint_t2Space F G
  let : LocallyCompactSpace (GroupScheme.rationalPoints G) :=
    rationalPoint_locallyCompactSpace F G
  let : TotallyDisconnectedSpace (GroupScheme.rationalPoints G) :=
    BruhatTits.rationalPoint_totallyDisconnectedSpace F G
  exact Induction.projective_compactInduced_of_compactCoefficients
    (rationalCommonNormKernel G) (isOpen_rationalCommonNormKernel G)
    ((SmoothRep.restrictSubgroupFunctor (rationalCommonNormKernel G)).obj π) hc

/-- Actual membership and compactness of the entire restriction give block
projectivity of the actual compact induction. -/
theorem rationalNormKernelCompactInduction_block_projective
    (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      (rationalNormKernelCompactInduction G π))
    (hc : HasCompactSmoothDualCoefficients
      (π.representation.comp (rationalCommonNormKernel G).subtype)) :
    Projective (⟨rationalNormKernelCompactInduction G π, hmem⟩ :
      RationalInertiaBlock G (rationalInertiaBaseLift G π)) :=
  rationalInertiaBlock_projective_of_projective G (rationalInertiaBaseLift G π)
    _ (rationalNormKernelCompactInduction_projective G π hc)

/-- A chosen lift in the actual inertia block for the actual norm-kernel compact
induction, conditional only on its membership and compact restriction. -/
def rationalNormKernelBlockProjectiveLift
    (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      (rationalNormKernelCompactInduction G π))
    (hc : HasCompactSmoothDualCoefficients
      (π.representation.comp (rationalCommonNormKernel G).subtype))
    {X Y : RationalInertiaBlock G (rationalInertiaBaseLift G π)}
    (f : (⟨rationalNormKernelCompactInduction G π, hmem⟩ :
      RationalInertiaBlock G (rationalInertiaBaseLift G π)) ⟶ Y)
    (q : X ⟶ Y) [Epi q] :
    (⟨rationalNormKernelCompactInduction G π, hmem⟩ :
      RationalInertiaBlock G (rationalInertiaBaseLift G π)) ⟶ X :=
  let := rationalNormKernelCompactInduction_block_projective G π hmem hc
  Projective.factorThru f q

/-- The chosen lift has the required composite. -/
@[simp]
theorem rationalNormKernelBlockProjectiveLift_comp
    (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      (rationalNormKernelCompactInduction G π))
    (hc : HasCompactSmoothDualCoefficients
      (π.representation.comp (rationalCommonNormKernel G).subtype))
    {X Y : RationalInertiaBlock G (rationalInertiaBaseLift G π)}
    (f : (⟨rationalNormKernelCompactInduction G π, hmem⟩ :
      RationalInertiaBlock G (rationalInertiaBaseLift G π)) ⟶ Y)
    (q : X ⟶ Y) [Epi q] :
    rationalNormKernelBlockProjectiveLift G π hmem hc f q ≫ q = f := by
  let := rationalNormKernelCompactInduction_block_projective G π hmem hc
  exact Projective.factorThru_comp f q

end Langlands.CuspidalSupport
