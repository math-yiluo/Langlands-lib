import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-! # Unimodularity of actual connected reductive rational-point groups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- The general ambient unimodularity input, without a chosen maximal split
torus or cocharacter. This is a proof target, not an assumed instance. -/
def RationalReductiveUnimodularityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (_hStandard : StandardCocharacterStatement.{u})
      (g : RationalPoint k G.X), MeasureTheory.Measure.modularCharacter g = 1

end Langlands.Aubert.General.RationalPointFamily
