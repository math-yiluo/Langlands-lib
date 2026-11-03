import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Langlands.Representation.Category.Contragredient
import Mathlib.NumberTheory.LocalField.Basic

/-! # Natural opposite-Jacquet duality on the actual rational-point group -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- Normalized Jacquet restriction of the smooth dual is naturally the smooth
dual of opposite Jacquet restriction on admissible objects. This is a proof target. -/
def RationalNaturalJacquetDualityStatement : Prop :=
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
      let rP := jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU
      let rO := jacquetFunctor.{u, max (u + 1) v}
        (opposite_isSemidirectDecomposition i ν hStandard hG hi hν I ζ hζ)
        (isClosed_oppositeUnipotent_localField i ζ)
      ∃ E : ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)),
          A.IsAdmissible →
            (rP.obj A.contragredient ≅ (rO.obj A).contragredient),
        ∀ (A B : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
          (hA : A.IsAdmissible) (hB : B.IsAdmissible) (f : A ⟶ B),
          rP.map (contragredientHom f) ≫ (E A hA).hom =
            (E B hB).hom ≫ contragredientHom (rO.map f)

end Langlands.Aubert.General.RationalPointFamily
