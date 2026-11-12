import Langlands.Automorphic.GroupSchemeCuspidalForms
import Langlands.Automorphic.GroupSchemeActualDifferential

/-! # Enveloping derivatives preserve vanishing parabolic constant terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

/-- If the normalized constant term of an original finite plot-smooth rational function along
a proper rational parabolic vanishes at every adelic point, then so does the normalized constant
term of each of its actual enveloping derivatives along the same parabolic. -/
def AdelicConstantTermEnvelopingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (P : ProperRationalParabolic G) (a : AdelicEnvelopingAlgebra F G hsmooth)
    (f : FinitePlotSmoothRationalFunctions F G),
    (∀ g : AdelicGroupPoints F G,
      constantTerm F G (properRationalParabolicRadicals hPD hG P)
        (properParabolicQuotientMeasure F G hPD hG P) f.val g = 0) →
    ∀ g : AdelicGroupPoints F G,
      constantTerm F G (properRationalParabolicRadicals hPD hG P)
        (properParabolicQuotientMeasure F G hPD hG P)
        (actualAdelicEnvelopingAction F G hsmooth a f).val g = 0

end Langlands.Automorphic.GroupSchemeFunctions
