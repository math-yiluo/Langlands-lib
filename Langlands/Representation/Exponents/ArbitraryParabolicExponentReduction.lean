import Langlands.Representation.Exponents.ArbitraryParabolicExponentStatement
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityStatement
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.Representation.Exponents.ArbitraryParabolicInductionComparison
import Langlands.Representation.Exponents.JacquetExponentRestriction
import Langlands.Representation.Exponents.SplitComponentFiniteSupport

/-! # The exponent theorem from Jacquet admissibility and quotient compactness

This internal reduction assembles Renard VII.1.1 from two explicit global
prerequisites. It does not prove either prerequisite unconditionally.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The exact arbitrary-parabolic exponent proposition follows from preservation
of Jacquet admissibility and compactness of the actual parabolic quotients. -/
def ArbitraryParabolicExponentReductionStatement : Prop :=
  ArbitraryParabolicJacquetAdmissibilityStatement.{u, v} →
    ArbitraryParabolicQuotientCompactStatement.{u} →
      ArbitraryParabolicExponentStatement.{u, v}

/-- Conditional assembly of all three clauses, retaining the original target
and both global prerequisite statements unchanged. -/
theorem arbitraryParabolicExponent_reduction :
    ArbitraryParabolicExponentReductionStatement.{u, v} := by
  intro hJ hcompact k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _
  refine ⟨?_, ?_, ?_⟩
  · intro P M U A p l r a hp hl hr hmul ha π hπ
    have hdecomp := normalizedJacquetWeightSpace_decomposition_of_admissible
      p l r hp hl hr hmul ha π (hJ k G hG P M U p l r hp hl hr hmul π hπ)
    refine ⟨hdecomp.1, hdecomp.2, ?_⟩
    intro hfinite
    let := hcompact k G hG P p hp
    exact finite_normalizedJacquetExponents_of_hasFiniteLength_of_compactQuotient_of_spanning
      p l r hp hl hr hmul ha π hfinite hdecomp.2
  · intro AG aG haG V hV
    exact groupWeightSpace_decomposition haG V hV
  · intro P M U A AG p l r a aG hp hl hr hmul ha haG e he
    exact ⟨inducedExponent_restrict p l r hp hl hr hmul ha haG e he,
      normalizedJacquetExponent_restrict p l r hp hl hr hmul ha haG e he⟩

end Langlands.Aubert.General.RepresentedParabolic
