import Langlands.GroupScheme.Rational.LeviSplitComponentRecallStatements
import Langlands.GroupScheme.Rational.OriginalLeviCocharacter
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # A rational Levi is the centralizer of its specified split component -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Renard V.3.1: the centralizer of the specified split component of a
rational Levi is exactly that embedded Levi, on every test scheme. -/
theorem leviSplitComponentCentralizer : LeviSplitComponentCentralizerStatement.{u} := by
  intro k _ G hG P L j l hj hl A a ha
  obtain ⟨χ, hχ⟩ :=
    ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup hG j hj
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have hP : (Dynamic.parabolic χ).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, hχ⟩
  obtain ⟨ν, hνP, hνZ, hA⟩ :=
    hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP ha
  exact hA

end Langlands.GroupScheme
