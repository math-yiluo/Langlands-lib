import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Langlands.Representation.Jacquet.IwahoriStablePairingData
import Mathlib.NumberTheory.LocalField.Basic

/-! # A common contracting element for opposite rational-point radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- One Levi-central element and an ambient-cofinal compact-open basis give
opposite Iwahori contractions on the actual standard and inverse-cocharacter
radicals. This is a proof target. -/
def RationalOppositeIwahoriBasisStatement : Prop :=
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
      (ν : cocharacterLattice T) (_hν : IsGenericCocharacter i ν)
      (_hStandard : StandardCocharacterStatement.{u})
      (I : Finset (SimpleRoot i ν))
      (_hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (ζ : cocharacterLattice T)
      (_hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ),
      ∃ g : RationalPoint k G.X,
        (∀ m ∈ levi i ν I, m * g = g * m) ∧
        Jacquet.HasOppositeIwahoriContractionBasis
          (unipotent i ν I) (levi i ν I) (oppositeUnipotent i ζ) g

end Langlands.Aubert.General.RationalPointFamily
