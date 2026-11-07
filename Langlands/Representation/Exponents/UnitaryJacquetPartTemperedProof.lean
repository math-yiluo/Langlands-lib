import Langlands.Representation.Exponents.UnitaryJacquetPartTemperedStatement
import Langlands.Representation.Exponents.UnitaryInnerRootData
import Langlands.Representation.Exponents.TemperedLeviJacquetDecomposition
import Langlands.GroupScheme.Rational.NestedParabolicInnerPresentation

/-! # Temperedness of the unitary Jacquet part -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.3 for the original actual parabolic, Levi, radical and component. -/
theorem unitaryJacquetPartTempered : UnitaryJacquetPartTemperedStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  let := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ Q L U A q l r a hq hl hr hmulQ ha
  let := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  let : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q l hq hl
  let : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q l hq hl
  intro π hπ
  refine ⟨hπ.unitaryJacquetPart_isCompl q l r hq hl hr hmulQ ha, ?_⟩
  refine ⟨hπ.isAdmissible_leviUnitaryJacquetModule q l r hq hl hr hmulQ ha, ?_⟩
  intro PL M B pL mL b hpL hmL hb
  have := hG.smooth
  have := hl.isConnectedReductive.smooth
  refine ⟨?_, ?_⟩
  · obtain ⟨NL, nL, hnL, hmulL⟩ := hmL.exists_unipotentRadical
    obtain ⟨d⟩ := nonempty_unitaryInnerRootData q l r hq hl hr hmulQ
      pL mL nL hpL hmL hnL hmulL ha hb π hπ
    let := hmulQ
    exact ⟨d.fine.innerPresentation d.outer pL mL d.commonLevi hG d.nested
      d.intersection hpL hmL hb hr⟩
  · intro inner NL nL hnL hmulL χ hχ
    exact normalizedRealPart_mem_innerNonnegCone_of_unitary
      q l r hq hl hr hmulQ pL mL nL hpL hmL hnL hmulL ha hb π hπ inner χ hχ

end Langlands.Aubert.General.RepresentedParabolic
