import Langlands.GroupScheme.Rational.MinimalParabolicLeviCentralizerStatement
import Langlands.GroupScheme.Rational.MinimalParabolicCompatibleRefinement
import Langlands.GroupScheme.Rational.CentralLeviTorusRadical
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Rational Levis of a minimal parabolic as split-torus centralizers: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Rational Levis of minimal parabolics** (Borel–Tits 4.15(b) and 4.16, (i) implies (iii)).
The split component of a rational Levi of a minimal rational parabolic, factored through the
specified solvable radical, is an ambient maximal split torus whose whole-torus centralizer is
the image of that Levi. -/
theorem minimalParabolicLeviCentralizer : MinimalParabolicLeviCentralizerStatement.{u} := by
  intro k _ G hG P j hj L l hl R r hR
  have hjc : IsClosedSubgroup j := hj.1.isClosedSubgroup
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG P j hjc).mp hj.1
  have : IsClosedImmersion j.hom.hom.left := hjc
  have hP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, hχ⟩
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k L hl.isConnectedReductive).1
  have hmax : IsMaximalSplitTorus (a ≫ l ≫ j) :=
    hl.isMaximalSplitTorus_splitComponent_of_dynamicMinimalParabolic hG hj χ hP ha
  obtain ⟨-, -, -, hcent⟩ := hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP ha
  let bR := hl.centralTorusRadicalFactor a hR.1 ha.1.1.1.isTorus ha.1.1.2 ha.1.2
  have hamb : bR ≫ r ≫ j = a ≫ l ≫ j := by
    rw [← Category.assoc,
      hl.centralTorusRadicalFactor_comp a hR.1 ha.1.1.1.isTorus ha.1.1.2 ha.1.2,
      Category.assoc]
  exact ⟨A, bR, by rw [hamb]; exact hmax, by rw [hamb]; exact hcent⟩

end Langlands.GroupScheme
