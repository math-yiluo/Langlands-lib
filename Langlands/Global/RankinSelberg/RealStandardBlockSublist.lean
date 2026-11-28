import Langlands.Global.RankinSelberg.RealCanonicalWhittakerComparison
import Langlands.Global.RankinSelberg.RealDescendingWhittakerRange
import Langlands.Global.RankinSelberg.RealLocalCharacterGrowthInterfaces
import Langlands.Global.RankinSelberg.RealPrincipalSeriesWhittakerReduction
import Langlands.Representation.Archimedean.RealStandardGenericProof
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionProof
import Langlands.Representation.Archimedean.RealStandardUnlinkedNecessity

/-! # Irreducibility for real standard sublists and nonzero Whittaker models -/

noncomputable section

open Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open RealGodement RealGodementProfiles RealPrincipalSeries
open RealJacquet (isRealCharacterList_expand)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Each rank-correct real standard block list has a nonzero exact compact-finite
Whittaker coefficient map at every nonzero additive scale. -/
def RealExactBlockWhittakerNonzeroStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    ∀ a : ℝˣ, ∃ B : realStandardKFinite (r + 1) ds →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℝ → ℂ),
      IsRealWhittakerIntertwiner r ds a B ∧ B ≠ 0

set_option maxHeartbeats 600000 in
theorem realExactBlockWhittakerNonzero : RealExactBlockWhittakerNonzeroStatement := by
  intro r ds hd a
  obtain ⟨cs, hcs⟩ := isRealCharacterList_expand ds
  have hr : realRank (cs.map RealBlock.character) = r + 1 := by rw [← hcs, realRank_expand, hd]
  obtain ⟨p, z, hz⟩ := exists_characterList_of_map_character cs hr
  have he := hcs.trans hz
  let C := canonicalJacquetMap (-a) p z
  have hC : IsRealWhittakerIntertwiner r (characterList p z) a C := by
    simpa only [neg_neg, C] using (realGodementCanonicalModel r (-a) p z).1
  have hi := realStandardKFinite_le_expand (r + 1) ds
  have hDetect := restrict_expand_ne_zero r ds hd a
  rw [he] at hi hDetect
  exact ⟨C.comp (Submodule.inclusion hi), isRealWhittakerIntertwiner_restrict hi hC,
    hDetect hi C hC (canonicalJacquetMap_ne_zero r (-a) p z)⟩

/-- Each rank-correct real standard block list has a nonzero exact Whittaker model. -/
theorem realWhittakerModel_ne_bot_of_rank (r : ℕ) (ds : List RealBlock) (hd : realRank ds = r + 1)
    (a : ℝˣ) : realWhittakerModel r ds a ≠ ⊥ := by
  obtain ⟨B, hB, hn⟩ := realExactBlockWhittakerNonzero r ds hd a
  intro h
  have hle : B.range ≤ realWhittakerModel r ds a := le_iSup_of_le B (le_iSup_of_le hB le_rfl)
  rw [h, le_bot_iff, LinearMap.range_eq_bot] at hle
  exact hn hle

/-- An ordered irreducible real standard list has irreducible standard modules for its sublists
at their respective ranks. -/
def RealStandardIrreducibleSublistStatement : Prop :=
  ∀ (ds es : List RealBlock), es.Sublist ds → Langlands.Archimedean.IsRealLanglandsOrdered ds →
    IsIrreducibleGKModule (realStandardRep (realRank ds) ds) (realStandardLie (realRank ds) ds) →
    IsIrreducibleGKModule (realStandardRep (realRank es) es) (realStandardLie (realRank es) es)

set_option maxHeartbeats 650000 in
theorem realStandardIrreducibleSublist : RealStandardIrreducibleSublistStatement := by
  intro ds es he ho hi
  have hg := isRealGeneric_realStandardLie (realRank ds) ds rfl
  have hu := realStandard_unlinked_of_ordered rfl ho hi hg
  apply realStandardIrreducibleCriterion (realRank es) es rfl (List.Pairwise.sublist he ho)
  exact List.Pairwise.sublist (he.flatMap realBlockMoeglinData) hu

end Langlands.Global.RankinSelbergGlobal
