import Langlands.Representation.Aubert.General.DirectedUnions
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity

/-! # Directed covers for actual standard rational-point induction-Jacquet -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance rationalDirectedUnionsPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]

/-- At the canonical point topology, the actual standard normalized composite
exhausts every directed cover by injective smooth coefficient maps. Quotient
compactness remains explicit; the compact-limit condition is proved. -/
theorem standardInductionJacquetFunctor_exists_preimage_of_directed_cover
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (K : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν K : Set (RationalPoint k G.X)))
    [CompactSpace (Induction.LeftQuotient (parabolic i ν K))] {Index : Type w}
    (A : Index → SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (B : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (φ : ∀ j, A j ⟶ B) (hinj : ∀ j, Function.Injective (SmoothRep.hom (φ j)))
    (hdir : Directed (· ≤ ·) (fun j => (SmoothRep.hom (φ j)).range))
    (hcover : ∀ b : B, ∃ j, b ∈ (SmoothRep.hom (φ j)).range)
    (f : (inductionJacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν K) hU).obj B) :
    ∃ j, ∃ g : (inductionJacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν K) hU).obj (A j),
      SmoothRep.hom ((inductionJacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν K) hU).map (φ j)) g = f := by
  exact inductionJacquetFunctor_exists_preimage_of_directed_cover.{u, max (u + 1) v, w}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν K) hU
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν K) A B φ hinj hdir hcover f

/-- A chosen stage and vector lifting `f` in the actual standard normalized
composite, together with the exact equation for its image. -/
def standardInductionJacquetDirectedLift
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (K : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν K : Set (RationalPoint k G.X)))
    [CompactSpace (Induction.LeftQuotient (parabolic i ν K))] {Index : Type w}
    (A : Index → SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (B : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (φ : ∀ j, A j ⟶ B) (hinj : ∀ j, Function.Injective (SmoothRep.hom (φ j)))
    (hdir : Directed (· ≤ ·) (fun j => (SmoothRep.hom (φ j)).range))
    (hcover : ∀ b : B, ∃ j, b ∈ (SmoothRep.hom (φ j)).range)
    (f : (inductionJacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν K) hU).obj B) :
    {jg : (Σ j, (inductionJacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν K) hU).obj (A j)) //
      SmoothRep.hom ((inductionJacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν K) hU).map (φ jg.1)) jg.2 = f} := by
  let hexists := standardInductionJacquetFunctor_exists_preimage_of_directed_cover
    i ν hStandard hG hi hν K hU A B φ hinj hdir hcover f
  exact ⟨⟨hexists.choose, hexists.choose_spec.choose⟩,
    hexists.choose_spec.choose_spec⟩

end Langlands.Aubert.General.RationalPointFamily
