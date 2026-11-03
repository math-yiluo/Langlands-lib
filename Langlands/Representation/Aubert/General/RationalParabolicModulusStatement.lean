import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.Group.HaarModulus
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.NumberTheory.LocalField.Basic

/-! # Modular characters of the actual rational-point group and its standard parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The group of rational points is unimodular, and Mathlib's modular character
of an actual standard parabolic `P = M ⋉ U` is the Haar modulus of conjugation
on its unipotent radical `U`. This is a proof target. -/
def RationalParabolicModulusStatement : Prop :=
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
      (hP : IsClosed (parabolic i ν I : Set (RationalPoint k G.X))),
      Continuous
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I).projection →
      haveI : LocallyCompactSpace (parabolic i ν I) := hP.locallyCompactSpace
      (∀ g : RationalPoint k G.X, MeasureTheory.Measure.modularCharacter g = 1) ∧
        ∀ p : parabolic i ν I,
          MeasureTheory.Measure.modularCharacter p =
            (HaarModulus.closedRestrictCharacter (unipotent i ν I) hU (parabolic i ν I)
              (isSemidirectDecomposition_of_standardCocharacterStatement
                i ν hStandard hG hi hν I).le_normalizer p : ℝ≥0)

end Langlands.Aubert.General.RationalPointFamily
