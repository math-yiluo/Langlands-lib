import Langlands.Representation.Exponents.LeviJacquetFiniteTypeStatement
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Exponents.LeviInductionFiniteTypeReduction
import Langlands.Representation.Aubert.General.JacquetFiniteGeneration

/-! # Proof that normalized parabolic restriction preserves finite type

Renard 2026, VI.1.3 Proposition, for represented parabolics.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.1.3 Proposition from compactness of every represented parabolic quotient. -/
theorem leviJacquetFiniteType_of_quotientCompact
    (hC : ArbitraryParabolicQuotientCompactStatement.{u}) :
    LeviJacquetFiniteTypeStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro π hπ
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) := hC k G hG P p hp
  have h := JacquetFiniteGeneration.finite_of_compactQuotient
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup) π hπ
  exact (NoetherianRepresentation.finite_comp_surjective_iff _
    (leviPointsEquiv p l hp hl).toMonoidHom (leviPointsEquiv p l hp hl).surjective).mp h

/-- Renard VI.1.3 Proposition: normalized parabolic restriction preserves finite type. -/
theorem leviJacquetFiniteType : LeviJacquetFiniteTypeStatement.{u, v} :=
  leviJacquetFiniteType_of_quotientCompact arbitraryParabolicQuotientCompact

end Langlands.Aubert.General.RepresentedParabolic
