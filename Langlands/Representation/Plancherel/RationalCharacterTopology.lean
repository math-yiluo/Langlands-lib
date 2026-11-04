import Langlands.GroupScheme.Rational.PointTopology
import Langlands.Representation.Plancherel.FieldUnitsTopologyProof
import Langlands.Representation.Plancherel.RationalImageCharacters
import Langlands.Representation.Plancherel.NormKernelTopologyProof

/-! # Actual rational norm characters in the canonical point topology -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

local instance instRationalCharacterTopology1 : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- Each actual normalized rational-character norm is locally constant. -/
theorem isLocallyConstant_rationalNormCharacter (chi : GroupScheme.rationalCharacters G) :
    IsLocallyConstant (rationalNormCharacters G chi).toMul :=
  (fieldNormUnits_isLocallyConstant F).comp_continuous
    (GroupScheme.continuous_rationalCharacterEval G chi)

/-- The actual rational-character integer coordinate is locally constant. -/
theorem isLocallyConstant_rationalOrderCharacter (chi : GroupScheme.rationalCharacters G) :
    IsLocallyConstant (fun g : GroupScheme.rationalPoints G =>
      fieldOrderUnits F (GroupScheme.rationalCharacterEval chi g)) :=
  (fieldOrderUnits_isLocallyConstant F).comp_continuous
    (GroupScheme.continuous_rationalCharacterEval G chi)

/-- The actual normalized norm, bundled in the named canonical point topology. -/
def rationalNormContinuousCharacter (chi : GroupScheme.rationalCharacters G) :
    GroupScheme.rationalPoints G →ₜ* ℝ≥0ˣ where
  toMonoidHom := (rationalNormCharacters G chi).toMul
  continuous_toFun := (isLocallyConstant_rationalNormCharacter G chi).continuous

@[simp] theorem rationalNormContinuousCharacter_apply
    (chi : GroupScheme.rationalCharacters G) (g : GroupScheme.rationalPoints G) :
    rationalNormContinuousCharacter G chi g =
      fieldNormUnits F (GroupScheme.rationalCharacterEval chi g) := rfl

/-- The actual source-positive integer order, continuously bundled. -/
def rationalOrderContinuousCharacter (chi : GroupScheme.rationalCharacters G) :
    GroupScheme.rationalPoints G →ₜ* Multiplicative ℤ where
  toMonoidHom := (fieldOrderUnits F).comp (GroupScheme.rationalCharacterEval chi)
  continuous_toFun := (isLocallyConstant_rationalOrderCharacter G chi).continuous

@[simp] theorem rationalOrderContinuousCharacter_apply
    (chi : GroupScheme.rationalCharacters G) (g : GroupScheme.rationalPoints G) :
    rationalOrderContinuousCharacter G chi g =
      fieldOrderUnits F (GroupScheme.rationalCharacterEval chi g) := rfl

/-- The actual common norm kernel is closed without local compactness assumptions. -/
theorem isClosed_rationalCommonNormKernel :
    IsClosed (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)) := by
  change IsClosed (commonNormKernel (fun chi => (rationalNormCharacters G chi).toMul) :
    Set (GroupScheme.rationalPoints G))
  simp only [commonNormKernel, Subgroup.coe_iInf]
  exact isClosed_iInter fun chi => isClosed_eq
    (rationalNormContinuousCharacter G chi).continuous continuous_const

/-- Every compact subgroup lies in the actual common norm kernel. -/
theorem compactSubgroup_le_rationalCommonNormKernel
    (K : Subgroup (GroupScheme.rationalPoints G))
    (hK : IsCompact (K : Set (GroupScheme.rationalPoints G))) :
    K ≤ rationalCommonNormKernel G := by
  intro g hg
  apply (mem_rationalCommonNormKernel G g).mpr
  intro chi
  exact Langlands.RankinSelberg.LastRowReduction.eq_one_of_isCompact
    (rationalNormCharacters G chi).toMul
    (rationalNormContinuousCharacter G chi).continuous K hK hg

section ConditionalPointGroupTopology

variable [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
  [WeaklyLocallyCompactSpace (GroupScheme.rationalPoints G)]

/-- Conditional on the stated canonical point-group properties, the actual
common norm kernel is open. These instances are not constructed here. -/
theorem isOpen_rationalCommonNormKernelConditional :
    IsOpen (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)) :=
  (commonNormKernelTopology (GroupScheme.rationalPoints G)
    (GroupScheme.rationalCharacters G) (fun chi => (rationalNormCharacters G chi).toMul)
    (fun chi => (rationalNormContinuousCharacter G chi).continuous)).1

/-- The actual norm-kernel quotient is discrete under the stated point-group hypotheses. -/
theorem rationalNormKernelQuotientDiscreteConditional :
    DiscreteTopology (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) :=
  QuotientGroup.discreteTopology (isOpen_rationalCommonNormKernelConditional G)

/-- The algebraic quotient-to-image identification is a topological group equivalence,
conditional on the displayed canonical point-group hypotheses. -/
def rationalNormKernelQuotientContinuousEquivConditional :
    (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) ≃ₜ*
      rationalDiscreteValuationImage G := by
  letI := rationalNormKernelQuotientDiscreteConditional G
  exact
    { toMulEquiv := rationalNormKernelQuotientEquiv G
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- Projection to the explicitly discrete actual image is continuous, conditional
on the displayed canonical point-group hypotheses. -/
theorem continuous_rationalValuationImageProjectionConditional :
    Continuous (rationalValuationImageProjection G) := by
  have h := (rationalNormKernelQuotientContinuousEquivConditional G).continuous.comp
    QuotientGroup.continuous_mk
  convert h using 1
  funext g
  exact (rationalNormKernelQuotientEquiv_mk G g).symm

/-- The actual valuation image projection, continuously bundled under the
canonical nonarchimedean and weak local compactness hypotheses. -/
def rationalCanonicalValuationImageProjectionConditional :
    GroupScheme.rationalPoints G →ₜ* rationalDiscreteValuationImage G :=
  rationalValuationImageContinuousProjection G
    (continuous_rationalValuationImageProjectionConditional G)

/-- The existing comparison with continuous unramified characters now uses the
canonical topology and a proved projection-continuity argument. -/
def rationalCanonicalImageUnramifiedEquivConditional :
    rationalImageCharacters G ≃*
      unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) :=
  rationalImageUnramifiedEquiv G
    (continuous_rationalValuationImageProjectionConditional G)

end ConditionalPointGroupTopology

end Langlands.Plancherel
