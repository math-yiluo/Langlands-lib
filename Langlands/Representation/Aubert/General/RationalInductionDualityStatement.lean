import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.Representation.Category.Contragredient
import Mathlib.NumberTheory.LocalField.Basic

/-! # Natural induction duality on the actual rational-point group -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- Same-parabolic normalized induction commutes naturally with the smooth
contragredient on admissible inducing objects. This is a proof target. -/
def RationalNaturalInductionDualityStatement : Prop :=
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
      (_hP : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
      (_hproj : Continuous
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I).projection),
      let F := normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU
      ∃ E : ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)),
          A.IsAdmissible →
            ((F.obj A).contragredient ≅ F.obj A.contragredient),
        ∀ (A B : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
          (hA : A.IsAdmissible) (hB : B.IsAdmissible) (f : A ⟶ B),
          contragredientHom (F.map f) ≫ (E A hA).hom =
            (E B hB).hom ≫ F.map (contragredientHom f)

end Langlands.Aubert.General.RationalPointFamily
