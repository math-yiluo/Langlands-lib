import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement
import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.CompactCoefficient.AmbientProjector

/-! # Fixed-vector detection through the actual rational norm kernel -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands

universe u uV

/-- Internal consumer of finite restriction to the actual rational-character norm
kernel. Compact coefficients of the restriction remain an explicit premise. -/
def RationalNormKernelFixedVectorDetectionStatement : Prop :=
  CuspidalSupport.RationalNormKernelFiniteRestrictionStatement.{u, uV} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (A D : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G))
      (K : Subgroup (GroupScheme.rationalPoints G)),
      IsCompact (K : Set (GroupScheme.rationalPoints G)) →
      D.IsIrreducible →
      (∀ S : Subrepresentation A.representation,
        fixedVectors A.representation K ≤ S.toSubmodule → S = ⊤) →
      HasCompactSmoothDualCoefficients
        (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) D).representation →
      SmoothRep.IsSubquotient D A →
      ∃ v : D, v ∈ fixedVectors D.representation K ∧ v ≠ 0

end Langlands
