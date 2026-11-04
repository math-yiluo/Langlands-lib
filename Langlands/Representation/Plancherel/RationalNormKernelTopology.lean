import Langlands.Representation.Plancherel.RationalCharacterTopology
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-! # Open actual norm kernel and discrete valuation quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalNormKernelTopology1 : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance instRationalNormKernelTopology2 : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- A proved compact open subgroup lies in the actual common norm kernel.
Thus openness requires no extra point-group topology premise. -/
theorem isOpen_rationalCommonNormKernel :
    IsOpen (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)) := by
  obtain ⟨K, hK⟩ := Langlands.BruhatTits.rationalPoint_exists_compactOpenSubgroup F G
  exact Subgroup.isOpen_mono
    (compactSubgroup_le_rationalCommonNormKernel G K.toSubgroup hK) K.isOpen

/-- The actual common norm kernel, bundled as an open subgroup in the canonical topology. -/
def rationalCommonNormOpenSubgroup : OpenSubgroup (GroupScheme.rationalPoints G) where
  toSubgroup := rationalCommonNormKernel G
  isOpen' := isOpen_rationalCommonNormKernel G

@[simp] theorem rationalCommonNormOpenSubgroup_toSubgroup :
    (rationalCommonNormOpenSubgroup G).toSubgroup = rationalCommonNormKernel G := rfl

/-- The quotient topology on the actual norm-kernel quotient is discrete. -/
theorem rationalNormKernelQuotientDiscrete :
    DiscreteTopology (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) :=
  QuotientGroup.discreteTopology (isOpen_rationalCommonNormKernel G)

/-- The actual norm-kernel quotient and the explicitly discrete valuation image
are topologically isomorphic for the canonical rational-point topology. -/
def rationalNormKernelQuotientContinuousEquiv :
    (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) ≃ₜ*
      rationalDiscreteValuationImage G := by
  letI := rationalNormKernelQuotientDiscrete G
  exact
    { toMulEquiv := rationalNormKernelQuotientEquiv G
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

@[simp] theorem rationalNormKernelQuotientContinuousEquiv_mk
    (g : GroupScheme.rationalPoints G) :
    rationalNormKernelQuotientContinuousEquiv G (QuotientGroup.mk g) =
      rationalValuationImageProjection G g :=
  rationalNormKernelQuotientEquiv_mk G g

/-- Continuity of the actual projection to its discrete integer-valuation image. -/
theorem continuous_rationalValuationImageProjection :
    Continuous (rationalValuationImageProjection G) := by
  have h := (rationalNormKernelQuotientContinuousEquiv G).continuous.comp
    QuotientGroup.continuous_mk
  convert h using 1
  funext g
  exact (rationalNormKernelQuotientEquiv_mk G g).symm

/-- All integer valuation coordinates are jointly locally constant. -/
theorem isLocallyConstant_rationalValuationImageProjection :
    IsLocallyConstant (rationalValuationImageProjection G) :=
  (IsLocallyConstant.iff_continuous _).mpr
    (continuous_rationalValuationImageProjection G)

/-- The canonical actual image projection as a continuous homomorphism. -/
def rationalCanonicalValuationImageProjection :
    GroupScheme.rationalPoints G →ₜ* rationalDiscreteValuationImage G :=
  rationalValuationImageContinuousProjection G
    (continuous_rationalValuationImageProjection G)

@[simp] theorem rationalCanonicalValuationImageProjection_apply
    (g : GroupScheme.rationalPoints G) :
    rationalCanonicalValuationImageProjection G g =
      rationalValuationImageProjection G g := rfl

/-- Characters of the actual discrete image are the continuous unramified
characters in the canonical point topology, with no extra continuity premise. -/
def rationalCanonicalImageUnramifiedEquiv :
    rationalImageCharacters G ≃*
      unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) :=
  rationalImageUnramifiedEquiv G (continuous_rationalValuationImageProjection G)

@[simp] theorem rationalCanonicalImageUnramifiedEquiv_apply
    (chi : rationalImageCharacters G) (g : GroupScheme.rationalPoints G) :
    (rationalCanonicalImageUnramifiedEquiv G chi).val g =
      chi (rationalValuationImageProjection G g) := rfl

@[simp] theorem rationalCanonicalImageUnramifiedEquiv_symm_projection
    (chi : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))
    (g : GroupScheme.rationalPoints G) :
    (rationalCanonicalImageUnramifiedEquiv G).symm chi
        (rationalValuationImageProjection G g) = chi.val g :=
  rationalImageUnramifiedDescend_projection G chi g

end Langlands.Plancherel
