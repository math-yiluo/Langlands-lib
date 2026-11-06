import Langlands.GroupScheme.Rational.ParabolicDoubleCosetRepresentatives
import Langlands.GroupScheme.Rational.ParabolicLeviTorusConjugation

/-! # Parabolic double-coset assembly through the supplied Levi bridge -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A supplied torus factor gives the all-test containment required by the
parabolic-to-Levi construction. Its two structural inputs remain explicit. -/
theorem parabolicSplitTorusLeviConjugacyStatement_of_dynamic_and_smoothConjugacy
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u}) :
    ParabolicSplitTorusLeviConjugacyStatement.{u} := by
  intro k _ G hG P M p l hp hl T i hi f hf
  exact ParabolicLeviTorus.exists_point_and_factor hPD hconj hG hp hl hi
    (SubgroupFunctor.range_le_of_factor f hf)

variable {k : Type u} [Field k]
    {G P M Q L : GroupScheme (Spec (CommRingCat.of k))}

/-- Choose a literal rational representative with both required torus
factorizations, under the three displayed structural propositions. -/
def torusAdaptedParabolicRepresentative
    (hCommon : ParabolicIntersectionCentralizerStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l)
    (q : Q ⟶ G) (lQ : L ⟶ Q) (hq : IsParabolicSubgroup q)
    (hlQ : IsRationalLeviSubgroup lQ) (g : rationalPoints G) :
    {z : rationalPoints G //
      DoubleCoset.mk (rationalPoints.map p).range (rationalPoints.map q).range z =
        DoubleCoset.mk (rationalPoints.map p).range (rationalPoints.map q).range g ∧
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
        IsMaximalSplitTorus i ∧ (∃ a : T.toGrp ⟶ M, a ≫ l ≫ p = i) ∧
          ∃ b : T.toGrp ⟶ L, b ≫ lQ ≫ q ≫ (G.innerIso z).hom = i} :=
  Classical.indefiniteDescription _ (by
    exact torusAdaptedDoubleCosetRepresentative_of_common_torus
      (parabolicIntersectionSplitTorusStatement_of_centralizer hCommon)
      (parabolicSplitTorusLeviConjugacyStatement_of_dynamic_and_smoothConjugacy hPD hconj)
      hG p l hp hl q lQ hq hlQ g)

/-- Conditional assembly from the six existing structural propositions.
This theorem does not prove any of those premises. -/
theorem representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs
    (hBruhat : RationalBruhatStatement.{u})
    (hGeneric : GenericMinimalParabolicStatement.{u})
    (hConjugacy : MinimalParabolicConjugacyStatement.{u})
    (hCommon : ParabolicIntersectionCentralizerStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u}) :
    RepresentedParabolicDoubleCosetStatement.{u} :=
  representedParabolicDoubleCosetStatement_of_structural_inputs
    hBruhat hGeneric hConjugacy
    (parabolicIntersectionSplitTorusStatement_of_centralizer hCommon)
    (parabolicSplitTorusLeviConjugacyStatement_of_dynamic_and_smoothConjugacy hPD hconj)

end Langlands.GroupScheme
