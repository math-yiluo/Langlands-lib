import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Rational.GeneralLinearIndexing
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialPacketCompact

/-! # The standard compact for the general linear wave-packet arguments -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace

/-- The clauses of `HasSpecialPacketCompact` at the actual standard integral
subgroup of `GL_N`, with the diagonal torus and a strictly decreasing reference
cocharacter. The same subgroup supplies every clause. -/
def GeneralLinearPacketCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ),
    let G := GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)
    let S := splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
    let i := GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    let K := (GroupScheme.GeneralLinear.standardIntegralModel ↥𝒪[F] F (Fin N)).integralPoints
    haveI : IsAffineHom G.X.hom :=
      GroupScheme.GeneralLinear.isAffineHom_groupScheme (Fin N) (CommRingCat.of F)
    have hi : IsMaximalSplitTorus (T := S) i :=
      GroupScheme.GeneralLinear.isMaximalSplitTorus_diagonalTorus (n := Fin N) F
    ∀ ν : cocharacterLattice S,
      StrictAnti (GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin N) F ν) →
      ∃ L : OpenSubgroup (rationalPoints G), L.toSubgroup = K ∧
        IsCompact (L : Set (rationalPoints G)) ∧
        WeakExpansion.IsSpecialVertexCompact ν hi L ∧
        Langlands.BruhatTits.Iwasawa.ParabolicPointProductFamily i ν L.toSubgroup ∧
        SimultaneousStandardBasisAt i ν L.toSubgroup ∧
        RationalPointFamily.FiniteCartanCovering F i ν L.toSubgroup ∧
        ∀ J ⊆ simpleRelativeRoots i ν, StandardLeviCartanCovering F i ν J L.toSubgroup

end Langlands.HarishChandraSchwartz
