import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Products on actual adelic points from independent arithmetic spreads -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Any field product cone has its product point topology for independently
specified finite-type function-field spreads. -/
def CurvePlaceSpreadProductStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S T U : Finset (AlgebraicCurve.Place k F))
    (MX : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (MY : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F T))))
    (MP : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F U))))
    [LocallyOfFiniteType MX.hom] [QuasiCompact MX.hom]
    [LocallyOfFiniteType MY.hom] [QuasiCompact MY.hom]
    [LocallyOfFiniteType MP.hom] [QuasiCompact MP.hom]
    (X Y : Over (Spec (CommRingCat.of F)))
    (eX : curvePlaceModelGenericFiber k F S MX ≅ X)
    (eY : curvePlaceModelGenericFiber k F T MY ≅ Y)
    (c : BinaryFan X Y)
    (eP : curvePlaceModelGenericFiber k F U MP ≅ c.pt), IsLimit c →
    @IsHomeomorph (CurvePlaceAdelePoints k F c.pt)
      (CurvePlaceAdelePoints k F X × CurvePlaceAdelePoints k F Y)
      (curvePlaceSpreadAdelePointTopology k F U MP c.pt eP)
      (@instTopologicalSpaceProd _ _
        (curvePlaceSpreadAdelePointTopology k F S MX X eX)
        (curvePlaceSpreadAdelePointTopology k F T MY Y eY))
      (fun p => (p ≫ c.fst, p ≫ c.snd))

/-- The full-number-field product comparison, including every infinite factor. -/
def NumberFieldSpreadProductStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S T U : Finset (FinitePlace K))
    (MX : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (MY : Over (Spec (CommRingCat.of ((T : Set (FinitePlace K)).integer K))))
    (MP : Over (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType MX.hom] [QuasiCompact MX.hom]
    [LocallyOfFiniteType MY.hom] [QuasiCompact MY.hom]
    [LocallyOfFiniteType MP.hom] [QuasiCompact MP.hom]
    (X Y : Over (Spec (CommRingCat.of K)))
    (eX : numberFieldModelGenericFiber K S MX ≅ X)
    (eY : numberFieldModelGenericFiber K T MY ≅ Y)
    (c : BinaryFan X Y)
    (eP : numberFieldModelGenericFiber K U MP ≅ c.pt), IsLimit c →
    @IsHomeomorph (NumberFieldAdelePoints K c.pt)
      (NumberFieldAdelePoints K X × NumberFieldAdelePoints K Y)
      (numberFieldSpreadAdelePointTopology K U MP c.pt eP)
      (@instTopologicalSpaceProd _ _
        (numberFieldSpreadAdelePointTopology K S MX X eX)
        (numberFieldSpreadAdelePointTopology K T MY Y eY))
      (fun p => (p ≫ c.fst, p ≫ c.snd))

/-- Both arithmetic forms of preservation of binary products for arbitrary
independently specified finite-type spreads. -/
def AdelicSpreadProductStatement : Prop :=
  CurvePlaceSpreadProductStatement.{u} ∧ NumberFieldSpreadProductStatement.{u}

end Langlands.Global
