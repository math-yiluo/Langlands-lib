import Langlands.Representation.Exponents.SquareIntegrableNormalizedTemperedStatement
import Langlands.Representation.Exponents.CasselmanNecessity
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof

/-! # Square-integrable representations are normalized-exponent tempered: proof

Renard 2026, VII.2.1, Remark 2 (printed p.227/PDF p.233). The proof combines the
published necessity half of Casselman's criterion (VII.1.2), which puts every
normalized exponent in the strictly positive root cone of every compatible
presentation, with the published existence of compatible root presentations
(V.3.14) and the inclusion of the strictly positive cone in the nonnegative one.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- **Renard VII.2.1, Remark 2.** A smooth complex representation of `G(F)` that is
square integrable modulo the center for some Haar measure on `G(F) ⧸ Z(G(F))`
satisfies the normalized-exponent temperedness condition at every actual rational
parabolic, rational Levi and split component. -/
theorem squareIntegrableNormalizedTempered :
    SquareIntegrableNormalizedTemperedStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  let := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ _ _ haar _ π hπ
  let := hG.smooth
  refine ⟨hπ.1, ?_⟩
  intro P M A p l a hp hl ha
  refine ⟨parabolicRootPresentationExistence k G hG P M A p l a hp hl ha, ?_⟩
  intro pres U r hr hmul χ hχ
  exact pres.positiveCone_subset_nonnegCone
    (arbitraryParabolicCasselmanNecessity k G hG haar π hπ P M U A p l r a hp hl hr hmul ha
      pres χ hχ)

end Langlands.Aubert.General.RepresentedParabolic
