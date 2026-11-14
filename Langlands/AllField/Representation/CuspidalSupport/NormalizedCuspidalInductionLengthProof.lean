import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof
import Langlands.AllField.Representation.CuspidalSupport.AssociatedProof
import Langlands.AllField.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
import Langlands.AllField.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.AllField.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
import Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatementSupplement
/-! Finite length and the factorial composition bound for cuspidal induction. -/

noncomputable section

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem CuspidalInductionLengthTheorem GLCuspidalTensorStatement JacquetDetectingFamilyLengthTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem NormalizedJacquetSubquotientTheorem PadicAssociatedGeometricPiecesTheorem PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement PadicProperRefinedInductionTheorem ProperRefinedInductionTheorem TotalConjugatingCountTheorem associatedFiltration_of_geometricPieces associatedGeometricPieceEquivalence associatedGeometricPieceVanishing associatedJacquetFiltration associatedJacquetFiltration_of_geometricPieces associatedJacquetFiltration_of_prerequisites associatedJacquetFiltration_rankZero cuspidalInductionLength cuspidalInductionSubquotientJacquet determinantUnitInclusion determinantUnitRestriction determinantUnitSubgroup fullRefinedInductionEquiv fullRefinedJacquetEquiv geometricPieceFunctor_subsingleton_of_proper_source geometricPieceInducingFunctor geometricPieceSmoothFunctor geometricPieceSmoothFunctor_obj_toRep geometricPieceSmoothFunctor_toRep induced_quasicuspidal_subrepresentation_subsingleton jacquetDetectingFamilyLength leviHarishChandraTheorem leviQuasicuspidalDecomposition levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup minimalNonzeroJacquet minimalWeylTransportQuasicuspidal nonassociatedJacquetSubquotients nonassociatedJacquetSubquotients_rankZero normalizedJacquetSubquotient normalizedRefinedInductionFunctor_subsingleton padicAssociatedGeometricPieces padicLeviFiltrationNoQuasicuspidalSubquotients padicProperRefinedInduction rankZero_jacquetInductionEquiv refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full totalConjugatingCount
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators

universe uF uV

variable (F : Type uF) [Field F]
  (T : LocalFieldData F) (n : ℕ)

private theorem countBound (B : BlockShape n) (s : Finset (BlockShape n)) :
    (∑ C ∈ s, Nat.card (MinimalConjugatingPermutations (F := F) B C)) ≤
      Nat.factorial B.length := by
  classical
  let : Fintype (BlockShape n) := Fintype.ofFinite _
  calc
    _ ≤ ∑ C : BlockShape n,
        Nat.card (MinimalConjugatingPermutations (F := F) B C) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ s)
    _ = Nat.card ((C : BlockShape n) ×
        MinimalConjugatingPermutations (F := F) B C) := Nat.card_sigma.symm
    _ = _ := (totalConjugatingCount F n B).2

private theorem associatedLengthBound :
    letI := T.topology
    ∀ (B C : BlockShape n) (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F)),
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      LevisAssociated (F := F) B C →
      HasCompositionLengthAtMost
        (Rep.of ((T.normalizedJacquetFunctor C).obj
          ((T.normalizedParabolicInductionFunctor B).obj σ)).representation)
        (Nat.card (MinimalConjugatingPermutations (F := F) B C)) := by
  let := T.topology
  intro B C σ hσ hcus hBC
  obtain ⟨_, r, e, s, hs⟩ := associatedJacquetFiltration F T n B C σ hcus.2 hBC
  refine ⟨r, ?_, s, ?_⟩
  · exact le_of_eq (by simpa using Nat.card_congr e)
  · intro i
    obtain ⟨E⟩ := hs i
    apply (isIrreducible_iff_of_equiv E).mpr
    exact isIrreducible_comp_of_surjective σ.representation (hρ := hσ)
      (leviConjugation B C (e i).val.val (e i).property).symm.toMonoidHom
      (leviConjugation B C (e i).val.val (e i).property).symm.surjective

/-- Every nonzero smooth subquotient of quasicuspidal induction has a
nonzero quasicuspidal Jacquet module at a Levi associated to the source. -/
theorem cuspidalInductionSubquotientJacquet :
    letI := T.topology
    ∀ (B : BlockShape n) (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F)),
      IsLeviQuasicuspidal B σ.representation →
      ∀ D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F),
        SmoothRep.IsSubquotient D ((T.normalizedParabolicInductionFunctor B).obj σ) →
        Nontrivial D → ∃ C : BlockShape n,
          LevisAssociated (F := F) B C ∧
          Nontrivial ((T.normalizedJacquetFunctor C).obj D) ∧
          IsLeviQuasicuspidal C
            ((T.normalizedJacquetFunctor C).obj D).representation := by
  let := T.topology
  intro B σ hcus D hD hne
  obtain ⟨C, hJ, hqc⟩ := minimalNonzeroJacquet F T n D hne
  refine ⟨C, ?_, hJ, hqc⟩
  by_contra hBC
  have hsub := normalizedJacquetSubquotient F T n C
    ((T.normalizedParabolicInductionFunctor B).obj σ) D hD
  have hzero := nonassociatedJacquetSubquotients F T n B C σ hcus hBC
    ((T.normalizedJacquetFunctor C).obj D) hsub hqc
  exact not_nontrivial_iff_subsingleton.mpr hzero hJ

/-- Actual normalized induction of irreducible cuspidal data has finite
group-algebra length and a composition series with at most `B.length!` factors. -/
theorem cuspidalInductionLength :
    CuspidalInductionLengthTheorem.{uF, uV} F T n := by
  classical
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro B σ hσ hcus
  let : Fintype (BlockShape n) := Fintype.ofFinite _
  let A := (T.normalizedParabolicInductionFunctor B).obj σ
  let s := Finset.univ.filter (fun C => LevisAssociated (F := F) B C)
  let b := fun C => Nat.card (MinimalConjugatingPermutations (F := F) B C)
  have hlength : ∀ C ∈ s, HasCompositionLengthAtMost
      (Rep.of ((T.normalizedJacquetFunctor C).obj A).representation) (b C) := by
    intro C hC
    exact associatedLengthBound F T n B C σ hσ hcus
      (Finset.mem_filter.mp hC).2
  have hdetect : ∀ D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F),
      SmoothRep.IsSubquotient D A → Nontrivial D →
      ∃ C ∈ s, Nontrivial ((T.normalizedJacquetFunctor C).obj D) := by
    intro D hD hne
    obtain ⟨C, hBC, hJ, _⟩ :=
      cuspidalInductionSubquotientJacquet F T n B σ hcus.2 D hD hne
    exact ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBC⟩, hJ⟩
  obtain ⟨hfinite, r, hr, hseries⟩ :=
    jacquetDetectingFamilyLength.{uF, max uF uV} F T n A s b hlength hdetect
  exact ⟨hfinite, r, hr.trans (countBound F n B s), hseries⟩

end Langlands.AllField.CuspidalSupport
