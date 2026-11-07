import Langlands.Representation.CuspidalSupport.RationalUniversalMembership
import Langlands.Representation.CuspidalSupport.RationalUniversalGeneration
import Langlands.Representation.CuspidalSupport.RationalUniversalSmallness

/-! The five actual small-progenerator conditions from explicit restriction inputs. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalUniversalReductionTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X

local instance rationalUniversalReductionTopologicalGroup :
    IsTopologicalGroup (GroupScheme.rationalPoints G) := rationalPoint_isTopologicalGroup F G

/-- A conditional reduction to genuine restriction inputs. This proposition is
separate from the unchanged unconditional VI.4.1 target. -/
def RationalNormKernelSmallProgeneratorReductionStatement
    [LocallyCompactSpace (GroupScheme.rationalPoints G)]
    [NonarchimedeanGroup (GroupScheme.rationalPoints G)] : Prop :=
  ∀ (hG : GroupScheme.IsConnectedReductive G)
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)),
    π.IsIrreducible →
    HasCompactSmoothDualCoefficients
      (π.representation.comp (rationalCommonNormKernel G).subtype) →
    RationalNormKernelFiniteRestrictionStatement.{uF, uV} →
    RationalNormKernelTwistEquivalenceStatement.{uF, max uF uV, max uF uV} →
    IsRationalNormKernelSmallProgenerator G π

/-- The published membership, projectivity, generation, coproduct and smallness
APIs give all five conclusions for the actual full-restriction induction. -/
theorem rationalNormKernelSmallProgeneratorReduction
    [LocallyCompactSpace (GroupScheme.rationalPoints G)]
    [NonarchimedeanGroup (GroupScheme.rationalPoints G)] :
    RationalNormKernelSmallProgeneratorReductionStatement G := by
  intro hG π hπ hc hfin htw
  have hmem := rationalNormKernelCompactInduction_mem_of_restriction
    G hG π hπ hc hfin htw
  have hfinite := (hfin F G hG π hπ).2.1
  refine ⟨hmem, ?_, rationalNormKernelHom_faithful G π hmem hc, ?_, ?_⟩
  · intro X Y q hq f
    let := hq
    exact ⟨rationalNormKernelBlockProjectiveLift G π hmem hc f q,
      rationalNormKernelBlockProjectiveLift_comp G π hmem hc f q⟩
  · intro I
    exact rationalInertiaBlock_hasColimitsOfShape G (rationalInertiaBaseLift G π) (I := I)
  · intro I
    exact rationalNormKernelHom_preservesCoproducts_of_finiteLength G π hfinite hmem I

end Langlands.CuspidalSupport
