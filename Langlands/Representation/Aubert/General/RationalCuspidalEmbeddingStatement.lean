import Langlands.Representation.Aubert.General.RationalAlternatingOperator
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Representation.Aubert.General.SupportCategory
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsStatement
import Langlands.Representation.Induction.CompactQuotientProof
import Mathlib.NumberTheory.LocalField.Basic

/-! # Cuspidal embedding on the actual standard rational-point families -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard VI.2.1, Corollary: an irreducible smooth representation has a
nonzero cuspidal standard Jacquet module and embeds into induction from an
irreducible cuspidal representation of that same standard Levi. -/
def RationalCuspidalEmbeddingStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (_hEndpoints : StandardParabolicEndpointsStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (_hCompact : ∀ I, CompactSpace (Induction.LeftQuotient (parabolic i ν I)))
      (_hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      let hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν
      ∀ π : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X),
        π.IsIrreducible →
        ∃ I : Finset (SimpleRoot i ν),
          Nontrivial ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) ∧
          IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
            hU I (hM I) (hL I)
            ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) ∧
          ∃ σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I),
            σ.IsIrreducible ∧
            IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
              hU I (hM I) (hL I) σ ∧
            SmoothRep.IsSubrepresentation π
              ((normalizedInductionFunctor.{u, max (u + 1) v} (h I) (hU I)).obj σ)

end Langlands.Aubert.General.RationalPointFamily
