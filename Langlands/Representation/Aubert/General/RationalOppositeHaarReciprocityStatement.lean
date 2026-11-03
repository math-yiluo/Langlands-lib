import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Mathlib.NumberTheory.LocalField.Basic

/-! # Reciprocal actual Haar characters on opposite rational-point radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- On the literal common standard Levi, the actual Haar scaling characters of
the standard and inverse-cocharacter opposite radicals are reciprocal.
This is a proof target. -/
def RationalOppositeHaarReciprocityStatement : Prop :=
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
      (I : Finset (SimpleRoot i ν))
      (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (ζ : cocharacterLattice T)
      (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ),
      ∀ m : levi i ν I,
        HaarModulus.closedRestrictCharacter (unipotent i ν I) hU (levi i ν I)
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I).levi_le_normalizer m *
        HaarModulus.closedRestrictCharacter (oppositeUnipotent i ζ)
          (isClosed_oppositeUnipotent_localField i ζ) (levi i ν I)
          (opposite_isSemidirectDecomposition
            i ν hStandard hG hi hν I ζ hζ).levi_le_normalizer m = 1

end Langlands.Aubert.General.RationalPointFamily
