import Langlands.Global.AdelicGenericFiberPoints
import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.LocallyCompact

/-! # Actual adelic groups from specified arithmetic spreads -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global

/-- Actual group-scheme points over function-field adeles are Hausdorff
 topological groups; finite constants give local compactness and countability. -/
def CurvePlaceSpreadGroupStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (M : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S M ≅ G.X),
    letI : Group (CurvePlaceAdelePoints k F G.X) :=
      inferInstanceAs (Group
        (Langlands.AlgebraicGeometry.PointTopology.ringTest F
          (CurvePlaceAdeleRing k F) ⟶ G.X))
    letI := curvePlaceSpreadAdelePointTopology k F S M G.X e
    IsTopologicalGroup (CurvePlaceAdelePoints k F G.X) ∧
      T2Space (CurvePlaceAdelePoints k F G.X) ∧
      (∀ [Finite k], LocallyCompactSpace (CurvePlaceAdelePoints k F G.X) ∧
        SecondCountableTopology (CurvePlaceAdelePoints k F G.X))

/-- The full number-field adele points of any group scheme with a specified
 finite-type spread form a locally compact Hausdorff topological group. -/
def NumberFieldSpreadGroupStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (M : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S M ≅ G.X),
    letI : Group (NumberFieldAdelePoints K G.X) :=
      inferInstanceAs (Group
        (Langlands.AlgebraicGeometry.PointTopology.ringTest K (Adeles K) ⟶ G.X))
    letI := numberFieldSpreadAdelePointTopology K S M G.X e
    IsTopologicalGroup (NumberFieldAdelePoints K G.X) ∧
      T2Space (NumberFieldAdelePoints K G.X) ∧
      LocallyCompactSpace (NumberFieldAdelePoints K G.X) ∧
      SecondCountableTopology (NumberFieldAdelePoints K G.X)

/-- Both arithmetic forms of the actual adelic topological group assertion,
 with no affine or separated-model hypothesis. -/
def AdelicSpreadGroupStatement : Prop :=
  CurvePlaceSpreadGroupStatement.{u} ∧ NumberFieldSpreadGroupStatement.{u}

end Langlands.Global
