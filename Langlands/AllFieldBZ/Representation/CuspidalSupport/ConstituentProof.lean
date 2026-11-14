import Langlands.AllFieldBZ.Representation.CuspidalSupport.ConstituentComplement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.ConstituentInduction
import Langlands.AllFieldBZ.Representation.CuspidalSupport.ConstituentRankZero
import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalBlockIsolationProof
import Langlands.Representation.CuspidalSupport.ConstituentProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.ConstituentProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.ConstituentProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem DeterminantUnitSmoothDualStatement GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement IrreducibleQuasicuspidalLeviAdmissibilityTheorem LeviCuspidalBlockIsolationTheorem LeviCuspidalConstituentTheorem LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem NonassociatedJacquetSubquotientsTheorem NormalizedQuasicuspidalEmbeddingTheorem ZeroRankCuspidalEmbeddingTheorem continuous_determinantUnitInclusion cuspidalDatum_eq_of_equiv determinantUnitInclusion determinantUnitInclusion_apply determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnit_sup_center_finiteIndex exists_leviPiOpenSubgroup_subset glCuspidalTensorAssociation isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup leviCuspidalBlockIsolationTheorem leviCuspidalConstituentTheorem leviCuspidalConstituent_rankZero leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup leviQuasicuspidalDecomposition_of_inputs levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_leviPiOpenSubgroup
open Langlands.GeneralLinear
open Langlands.SmoothRep
universe uF uV

/-- The full cuspidal constituent theorem, including rank zero and independent
field and representation-carrier universes. -/
theorem leviCuspidalConstituentTheorem (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) :
    LeviCuspidalConstituentTheorem.{uF, uV} F T B := by
  by_cases hn : n = 0
  · subst n
    exact leviCuspidalConstituent_rankZero F T B
  let := T.topology
  let := T.leviNonarchimedean B
  let := T.leviLocallyCompactSpace B
  let H := determinantUnitOpenSubgroup T B
  let : H.toSubgroup.Normal := determinantUnitSubgroup_normal T B
  let : (H.toSubgroup ⊔ Subgroup.center (B.Levi F.Carrier)).FiniteIndex :=
    determinantUnit_sup_center_finiteIndex T B
  intro A D hAa hDi hDc hDA
  obtain ⟨_, m, V, hV, _, S, Q, hSQ, hS, htypes, hQ⟩ :=
    leviCuspidalBlockIsolationTheorem F T n B A D hDi hDc
  have hDS := irreducibleSubquotient_of_isCompl S Q hSQ hDi hDA hQ
  have hSa : (subrepresentation A S).IsAdmissible :=
    isAdmissible_of_injective (hom (subtype A S)) (subtype_injective A S) hAa
  have hVne (i : Fin m) : V i ≠ ⊥ := by
    let := hV i
    let : Nontrivial (V i).toSubmodule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (determinantUnitSubgroup T B))
        (V i).toRepresentation.asModule
    obtain ⟨v, hv⟩ := exists_ne (0 : (V i).toSubmodule)
    intro heq
    have hz : (v : D) ∈ (⊥ : Subrepresentation
        (determinantUnitRestriction T B D.representation)) := heq ▸ v.property
    exact hv (Subtype.ext hz)
  have hSD : IsSubrepresentation D (subrepresentation A S) ∧
      IsQuotient D (subrepresentation A S) := by
    apply constituent_of_finite_types H (subrepresentation A S) D hSa hS
      hDc.1 hDi V hVne
    · intro W hW
      obtain ⟨i, ⟨e⟩⟩ := htypes W
        (FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom W hW)
      exact ⟨i, ⟨e.symm⟩⟩
    · exact hDS
  exact constituent_of_isCompl S Q hSQ hSD

end Langlands.AllFieldBZ.CuspidalSupport
