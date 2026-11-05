import Langlands.GroupScheme.Rational.MultiplicativeTypeSplitQuotientAnisotropyStatement
import Langlands.GroupScheme.Rational.MaximalSplitQuotientAnisotropy
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Torus.MultiplicativeTypeQuotients
import Langlands.GroupScheme.Torus.MultiplicativeTypeStructure

/-! # Structural anisotropy of multiplicative-type maximal-split quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The quotient by a maximal split subtorus has a closed anisotropic torus
and an actual finite schematic fppf quotient, over every field. -/
theorem multiplicativeTypeSplitQuotientAnisotropy :
    MultiplicativeTypeSplitQuotientAnisotropyStatement.{u} := by
  intro k _ Z hZ A j hj C q hq
  have : IsAffine Z.X.left := hZ.isAffine
  have : IsCommMonObj Z.X := hZ.isCommMonObj
  have hjc : IsCentral j := by
    intro U x V b y
    exact Commute.all _ _
  have hCa : IsAnisotropic C := hj.isAnisotropic_quotient hjc q hq
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  obtain ⟨T, i, hT, hi, Q, p, hQ, hp⟩ := (hZ.of_fppfHom q).exists_torus_finiteQuotient
  have hTa : IsAnisotropic T :=
    le_antisymm ((splitRank_le_of_isClosedSubgroup i hi).trans_eq hCa) bot_le
  exact ⟨T, i, hT, hTa, hi, Q, p, hQ, hp⟩

end Langlands.GroupScheme
