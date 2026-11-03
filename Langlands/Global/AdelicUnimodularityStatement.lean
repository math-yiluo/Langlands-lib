import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.GroupScheme.Reductive.Basic

/-! # Unimodularity targets for actual adelic Haar measures -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGroupPoints

/-- Getz–Hahn, Lemma 3.6.4, first assertion, restricted to smooth connected
affine groups over number fields. This proposition supplies no Haar instance. -/
def NormOneHaarRightInvariantStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    Smooth G.X.hom → ConnectedSpace G.X.left →
      (Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant

/-- Getz–Hahn, Lemma 3.6.4, second assertion, in the connected reductive
number-field case, for the existing full adelic Haar measure. -/
def ConnectedReductiveHaarRightInvariantStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    Langlands.GroupScheme.IsConnectedReductive G →
      (Measure.haar : Measure (AdelicGroupPoints F G)).IsMulRightInvariant

/-- Both source assertions, as a single exact proof target. Neither analytic
right-invariance assertion is an input to this proposition. -/
def AdelicHaarUnimodularityStatement : Prop :=
  NormOneHaarRightInvariantStatement.{u} ∧
    ConnectedReductiveHaarRightInvariantStatement.{u}

end Langlands.Global.AdelicGroupPoints
