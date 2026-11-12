import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.Representation.Exponents.ArbitraryParabolicFiniteSupportReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Compactness of the literal rational-point quotient for every represented parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- For every represented parabolic `p : P ⟶ G` of a connected reductive group over a
nonarchimedean local field, the quotient `P(k) \ G(k)` of the rational points by the literal
image of `P(k)` is compact (Renard, V.5.1 Corollary, compactness part). -/
theorem arbitraryParabolicQuotientCompact :
    ArbitraryParabolicQuotientCompactStatement.{u} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  intro _ _ P p hp
  exact compactSpace_leftQuotient_pointImage_of_dynamic parabolicDynamic
    BruhatTits.dynamicParabolicQuotientCompact hG p hp

end Langlands.Aubert.General.RepresentedParabolic
