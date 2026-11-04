import Langlands.Representation.Aubert.General.SupportCategoryExhaustion
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity

/-! # Finite invariant spans for actual standard induction-Jacquet objects -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance rationalSupportExhaustionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]

/-- The actual standard induction-Jacquet object is exhausted by images of
finite invariant spans. Only quotient compactness remains a topological input:
the compact-limit condition follows from the standard-cocharacter statement. -/
theorem standardInductionJacquet_iSup_finiteSpanFunctorImage
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (K : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν K : Set (RationalPoint k G.X)))
    [CompactSpace (Induction.LeftQuotient (parabolic i ν K))]
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) :
    (⨆ s, finiteSpanFunctorImage.{u, max (u + 1) v}
      (inductionJacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν K)
        hU) E s) = ⊤ :=
  inductionJacquet_iSup_finiteSpanFunctorImage.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν K) hU
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν K) E

end Langlands.Aubert.General.RationalPointFamily
