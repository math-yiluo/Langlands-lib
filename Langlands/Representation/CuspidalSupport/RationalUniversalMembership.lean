import Langlands.Representation.CuspidalSupport.OpenNormalInductionSupport
import Langlands.Representation.CuspidalSupport.RationalUniversalProgenerator
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitTwistStatement
import Langlands.Representation.Induction.SplitStagesComparison

/-! Actual inertia-block membership from norm-kernel restriction inputs. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalUniversalMembershipTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalUniversalMembershipTopologicalGroup : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable [LocallyCompactSpace (GroupScheme.rationalPoints G)]
  [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
  (hG : GroupScheme.IsConnectedReductive G)
  (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
  (hπ : π.IsIrreducible)
  (hc : HasCompactSmoothDualCoefficients
    (π.representation.comp (rationalCommonNormKernel G).subtype))
  (hfin : RationalNormKernelFiniteRestrictionStatement.{uF, uV})
  (htw : RationalNormKernelTwistEquivalenceStatement.{uF, max uF uV, max uF uV})

include hG hπ hc hfin htw in
/-- Finite restriction, compact coefficients of the whole restriction, and the
actual twist-equivalence theorem give membership of the actual full-restriction
compact induction in the inertia block of its explicitly lifted base. -/
theorem rationalNormKernelCompactInduction_mem_of_restriction :
    rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      (rationalNormKernelCompactInduction G π) := by
  obtain ⟨-, -, m, W, hWirr, hWspan⟩ := hfin F G hG π hπ
  intro D hD hDC
  obtain ⟨q, hq⟩ := openNormalFamily_compactInduction_subquotient_restricted_hom
    (rationalCommonNormKernel G) (isOpen_rationalCommonNormKernel G) π hc
    W hWirr hWspan D hD hDC
  let e := Induction.restrictAlongEquiv (rationalCommonNormKernel G).subtype
    (SmoothRep.universeLiftEquiv.{uF} π)
  let q' := e.toIntertwiningMap.comp q
  have hq' : q' ≠ 0 := by
    intro hz
    apply hq
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hv := DFunLike.congr_fun hz v
    change e (q v) = 0 at hv
    change q v = 0
    exact e.injective (hv.trans (map_zero e).symm)
  have hπlift : (rationalInertiaBaseLift G π).IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff.{uF} π).mpr hπ
  have h3 := htw F G hG D (rationalInertiaBaseLift G π) hD hπlift
  obtain ⟨χ, ⟨i⟩⟩ := h3.1.mp (h3.2.mpr ⟨q', hq'⟩)
  exact IsRationalInertiaRelated.symm
    ⟨χ, ⟨(SmoothRep.mkIso (A := rationalUnramifiedTwist G χ D)
      (B := rationalInertiaBaseLift G π) i).symm⟩⟩

/-- The actual induced function representation, regarded as an object of its
actual inertia block after discharging membership from restriction inputs. -/
def rationalNormKernelCompactInductionBlockObject :
    RationalInertiaBlock G (rationalInertiaBaseLift G π) :=
  ⟨rationalNormKernelCompactInduction G π,
    rationalNormKernelCompactInduction_mem_of_restriction G hG π hπ hc hfin htw⟩

end Langlands.CuspidalSupport
