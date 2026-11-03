import Langlands.GroupScheme.Rational.RootAnnihilatorRank
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsStatement
import Langlands.Geometry.Building.FiniteRealTorusSpace

/-! # Standard-root annihilator rank from the relative root system -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme

/-- The existing relative-root-system proposition implies the entire
standard-root annihilator rank proposition at the same universe. -/
def RelativeRootSystemImpliesStandardRootAnnihilatorRankStatement : Prop :=
  RelativeRootSystemStatement.{u} → StandardRootAnnihilatorRankStatement.{u}

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- The existing relative-root-system realization supplies all finiteness and
rank conclusions for a selection of actual simple roots. -/
theorem HasRelativeRootSystem.standardRootAnnihilatorRank
    (hR : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    Finite J ∧
      Module.Finite ℝ (V T) ∧
      Module.Finite ℝ (rootAnnihilator T J) ∧
      Module.finrank ℝ (V T) = splitTorusRank T ∧
      Module.finrank ℝ (rootAnnihilator T J) + Nat.card J = splitTorusRank T := by
  have : Finite J := ((hR.finite_simpleRelativeRoots i hT ν).subset hJ).to_subtype
  have := hT.finite_realCocharacterSpace
  have hli := (hR.linearIndependent_simpleRelativeRoots i ν hT hν).comp
    (Set.inclusion hJ) (Set.inclusion_injective hJ)
  refine ⟨inferInstance, inferInstance, inferInstance,
    hT.finrank_realCocharacterSpace, ?_⟩
  rw [← hT.finrank_realCocharacterSpace]
  exact finrank_rootAnnihilator_add_card hT J hli

/-- Reduction of the full first standard-Levi central-direction conjunct to
the existing unrestricted relative-root-system proposition. -/
theorem standardRootAnnihilatorRankStatement_of_relativeRootSystemStatement
    (hR : RelativeRootSystemStatement.{u}) : StandardRootAnnihilatorRankStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro ν hν J hJ
  exact (hR k G hG T i hi).standardRootAnnihilatorRank i hi.1.1 ν hν J hJ

/-- The conditional rank reduction holds at every universe. -/
theorem relativeRootSystemImpliesStandardRootAnnihilatorRankStatement :
    RelativeRootSystemImpliesStandardRootAnnihilatorRankStatement.{u} :=
  standardRootAnnihilatorRankStatement_of_relativeRootSystemStatement

end Langlands.GroupScheme
