import Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsStatement
import Langlands.GroupScheme.Rational.StandardLeviSplitContainment
import Langlands.GroupScheme.Rational.StandardLeviCentralImage
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.RootAnnihilatorRank
import Langlands.GroupScheme.Rational.CharacterRestrictionRational
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement

/-! # Standard-Levi central directions from intrinsic structural statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme.RealTorusSpace
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

/-- A reduction to the existing intrinsic standard-cocharacter, dynamic
centralizer, dynamic Lie, and integral character-restriction propositions. -/
def StandardLeviCentralDirectionsReductionStatement : Prop :=
  StandardCocharacterStatement.{u} →
    DynamicCentralizerReductiveStatement.{u} →
      DynamicLieStatement.{u} →
        CharacterRestrictionStatement.{u} →
          StandardLeviCentralDirectionsStatement.{u}

/-- Standard cocharacters for all faces already supply root independence and
therefore the complete selected-root rank statement. -/
theorem standardRootAnnihilatorRank_of_standardCocharacter
    (hstandard : StandardCocharacterStatement.{u}) :
    StandardRootAnnihilatorRankStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro ν hν J hJ
  have hexists : ∀ K : Set (characterLattice T), K ⊆ simpleRelativeRoots i ν →
      ∃ zeta, IsStandardCocharacter i ν K zeta :=
    fun K hK => (hstandard k G hG T i hi ν hν K hK).1
  have hfinite := finite_simpleRelativeRoots_of_standardCocharacter_exists
    i ν hi.1.1 hexists
  have : Finite J := (hfinite.subset hJ).to_subtype
  have hLI : LinearIndependent ℚ
      (fun α : simpleRelativeRoots i ν => toRat (α : characterLattice T)) :=
    Module.Flat.linearIndependent_one_tmul
      (linearIndependent_simpleRelativeRoots_of_standardCocharacter_exists i ν hexists)
  have hLIJ : LinearIndependent ℚ
      (fun α : J => toRat (α : characterLattice T)) :=
    hLI.comp (Set.inclusion hJ) (Set.inclusion_injective hJ)
  have := hi.1.1.finite_realCocharacterSpace
  refine ⟨inferInstance, inferInstance, inferInstance,
    hi.1.1.finrank_realCocharacterSpace, ?_⟩
  rw [← hi.1.1.finrank_realCocharacterSpace]
  exact finrank_rootAnnihilator_add_card hi.1.1 J hLIJ

/-- Combine the existing intrinsic structural propositions to prove every
conjunct of the unchanged standard-Levi central-directions target. None of the
four structural propositions is proved by this conditional assembly. -/
theorem standardLeviCentralDirections_of_standard_dynamic_characterRestriction
    (hstandard : StandardCocharacterStatement.{u})
    (hreductive : DynamicCentralizerReductiveStatement.{u})
    (hDynamic : DynamicLieStatement.{u})
    (hrestriction : CharacterRestrictionStatement.{u}) :
    StandardLeviCentralDirectionsStatement.{u} := by
  have hrankStatement := standardRootAnnihilatorRank_of_standardCocharacter hstandard
  refine ⟨hrankStatement, ?_⟩
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hG.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have := hi.isSplitSubtorus.mono
  intro ν hν J hJ L j hjc hj
  have hstd := hstandard k G hG T i hi ν hν J hJ
  obtain ⟨zeta, hzeta⟩ := hstd.1
  have hL : IsConnectedReductive L :=
    hreductive k G hG (CommGroupScheme.groupHom zeta ≫ i) L j hjc (by
      rw [← (hstd.2 zeta hzeta).2.1]
      exact hj)
  refine ⟨hL, ?_⟩
  intro A a ha
  have hexists : ∀ K : Set (characterLattice T), K ⊆ simpleRelativeRoots i ν →
      ∃ eta, IsStandardCocharacter i ν K eta :=
    fun K hK => (hstandard k G hG T i hi ν hν K hK).1
  have hfinite := finite_simpleRelativeRoots_of_standardCocharacter_exists
    i ν hi.1.1 hexists
  obtain ⟨hVA, f, hf, hfc, hfinj, hreverse⟩ :=
    ha.exists_commFactor_standardLevi_containing_annihilator hi ν J hjc hj
      hfinite ⟨zeta, hzeta⟩
  have hforward := range_cocharacterMapReal_le_rootAnnihilator_standardLevi
    hDynamic i ν J hJ hjc hj a ha.1 f hf
  have himage : (cocharacterMapReal f).range = rootAnnihilator T J :=
    le_antisymm hforward hreverse
  have hrank : Module.finrank ℝ (rootAnnihilator T J) = splitTorusRank A := by
    rw [← himage, LinearMap.finrank_range_of_inj hfinj]
    exact ha.1.1.1.finrank_realCocharacterSpace
  have hcodim := (hrankStatement k G hG T i hi ν hν J hJ).2.2.2.2
  have hsum : splitTorusRank T = Nat.card J + splitTorusRank A := by
    rw [hrank] at hcodim
    omega
  exact ⟨hVA, f, hf, hfc, hfinj, himage, hrank, hsum,
    rationalCharacterRank_eq_splitTorusRank_of_characterRestriction hrestriction hL ha⟩

/-- The named reduction proposition, at its complete arbitrary universe. -/
theorem standardLeviCentralDirectionsReduction :
    StandardLeviCentralDirectionsReductionStatement.{u} :=
  standardLeviCentralDirections_of_standard_dynamic_characterRestriction

end Langlands.GroupScheme
