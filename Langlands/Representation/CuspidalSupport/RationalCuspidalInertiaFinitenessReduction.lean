import Langlands.Representation.CuspidalSupport.RationalNormKernelDecompositionStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitTwistStatement
import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaDecompositionReduction
import Langlands.Representation.CompactCoefficient.FixedTypeEmbedding
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionProof

/-!
# Fixed-level transport for actual rational cuspidal inertia classes

The actual compact-open level pulls back to a compact-open level in the
common rational-character norm kernel. Nonzero intertwiners on that kernel
identify the existing actual unramified inertia classes, conditional on the
published twist-equivalence proposition. The generic compact-type injection
then reduces the exact inertia-finiteness target to separately owned inputs.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section FixedLevel

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance inertiaFinitenessReductionPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- Pull back an actual rational-point open level along the common norm
kernel inclusion, with its canonical subtype topology. -/
def rationalNormKernelFixedLevel
    (K : OpenSubgroup (GroupScheme.rationalPoints G)) :
    OpenSubgroup (Plancherel.rationalCommonNormKernel G) :=
  OpenSubgroup.comap (Plancherel.rationalCommonNormKernel G).subtype
    continuous_subtype_val K

omit [LocallyOfFiniteType G.X.hom] in
/-- Every compact subgroup of the actual rational-point group lies in the
common norm kernel, so pulling back a compact open level preserves compactness. -/
theorem isCompact_rationalNormKernelFixedLevel
    (K : OpenSubgroup (GroupScheme.rationalPoints G))
    (hK : IsCompact (K : Set (GroupScheme.rationalPoints G))) :
    IsCompact (rationalNormKernelFixedLevel G K :
      Set (Plancherel.rationalCommonNormKernel G)) := by
  rw [Subtype.isCompact_iff]
  have hKN := Plancherel.compactSubgroup_le_rationalCommonNormKernel G K.toSubgroup hK
  have himage : (Subtype.val : Plancherel.rationalCommonNormKernel G →
        GroupScheme.rationalPoints G) ''
      (rationalNormKernelFixedLevel G K : Set (Plancherel.rationalCommonNormKernel G)) =
        (K : Set (GroupScheme.rationalPoints G)) := by
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro hg
      exact ⟨⟨g, hKN hg⟩, hg, rfl⟩
  rwa [himage]

end FixedLevel

/-- Conditional on the exact norm-kernel twist-equivalence proposition, a
nonzero restricted intertwiner identifies the actual irreducible inertia classes. -/
theorem rationalIrreducibleInertiaClass_eq_of_normKernel_hom
    (htw : RationalNormKernelTwistEquivalenceStatement.{uF, uV, uV})
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ (A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
      (hA : A.IsIrreducible) (hB : B.IsIrreducible),
      (∃ f : (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) A).representation.IntertwiningMap
          (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) B).representation,
          f ≠ 0) →
      rationalIrreducibleInertiaClass G A hA = rationalIrreducibleInertiaClass G B hB := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro A B hA hB hf
  apply (rationalIrreducibleInertiaClass_eq_iff G A B hA hB).mpr
  obtain ⟨χ, ⟨e⟩⟩ := (htw F G hG A B hA hB).1.mp
    ((htw F G hG A B hA hB).2.mpr hf)
  exact ⟨χ, ⟨(SmoothRep.mkIso
    (A := rationalUnramifiedTwist G χ A) (B := B) e).symm⟩⟩

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- The exact cuspidal inertia-finiteness target follows from norm-kernel
fixed-level finiteness, norm-kernel twist equivalence, cuspidal compact
restriction, and the existence of the special-vertex inputs of that restriction. -/
theorem rationalCuspidalInertiaFiniteness_of_specialVertexInputs
    (hfin : RationalNormKernelFixedLevelFinitenessStatement.{uF, uV})
    (htw : RationalNormKernelTwistEquivalenceStatement.{uF, uV, uV})
    (hCompact : RationalCuspidalCompactRestrictionStatement.{uF, uV})
    (hInputs : RationalSpecialVertexCompactInputsStatement.{uF}) :
    RationalCuspidalInertiaFinitenessStatement.{uF, uV} := by
  intro F _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro _ _ _ ν hν hStandard hRoots hU
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro h K hK
  let N := Plancherel.rationalCommonNormKernel G
  let L := rationalNormKernelFixedLevel G K
  obtain ⟨D, x, hspecial, hprops, hbasis, hcover⟩ := hInputs F G hG T i hi ν hν
  exact CompactCoefficient.finite_classes_of_compactRestriction N
    (Plancherel.isOpen_rationalCommonNormKernel G)
    (fun A hA => rationalIrreducibleInertiaClass G A hA)
    (IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU)
    (fun A hA => hCompact F G hG T i hi ν hν hStandard hRoots hU D x
      hspecial hprops hbasis hcover A hA)
    (fun A B hA hB hf =>
      rationalIrreducibleInertiaClass_eq_of_normKernel_hom htw F G hG A B hA hB hf)
    K.toSubgroup L.toSubgroup (fun _ hx => hx)
    (hfin F G hG T i hi ν hν hStandard hRoots hU L
      (isCompact_rationalNormKernelFixedLevel G K hK))

/-- Using the published cuspidal compact-restriction proof, the remaining
inputs are norm-kernel fixed-level finiteness, norm-kernel twist equivalence,
and joint special-compact basis existence. -/
theorem rationalCuspidalInertiaFiniteness_of_jointBasis
    (hfin : RationalNormKernelFixedLevelFinitenessStatement.{uF, uV})
    (htw : RationalNormKernelTwistEquivalenceStatement.{uF, uV, uV})
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF}) :
    RationalCuspidalInertiaFinitenessStatement.{uF, uV} :=
  rationalCuspidalInertiaFiniteness_of_specialVertexInputs hfin htw
    Aubert.General.rationalCuspidalCompactRestriction
    (rationalSpecialVertexCompactInputs_of_jointBasis hJoint)

end Langlands.CuspidalSupport
