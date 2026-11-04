import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.Separation.Hausdorff

/-! # Hausdorffness from separatedness over the original field -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Separated field schemes have Hausdorff actual function-field adelic points
for any specified finite-type arithmetic spread, with no separation on its model. -/
def CurvePlaceSpreadSeparatedStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (M : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom]
    (Y : Over (Spec (CommRingCat.of F))) [IsSeparated Y.hom]
    (e : curvePlaceModelGenericFiber k F S M ≅ Y),
    letI := curvePlaceSpreadAdelePointTopology k F S M Y e
    T2Space (CurvePlaceAdelePoints k F Y)

/-- Separated field schemes have Hausdorff actual full-number-field adelic
points for any specified finite-type arithmetic spread. -/
def NumberFieldSpreadSeparatedStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (M : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom]
    (Y : Over (Spec (CommRingCat.of K))) [IsSeparated Y.hom]
    (e : numberFieldModelGenericFiber K S M ≅ Y),
    letI := numberFieldSpreadAdelePointTopology K S M Y e
    T2Space (NumberFieldAdelePoints K Y)

/-- Both arithmetic forms of field-separated Hausdorffness, independently of
separatedness of the chosen arithmetic spread. -/
def AdelicSpreadSeparatedStatement : Prop :=
  CurvePlaceSpreadSeparatedStatement.{u} ∧ NumberFieldSpreadSeparatedStatement.{u}

end Langlands.Global
