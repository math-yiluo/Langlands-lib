import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupportStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociationReverseProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem CompactCoefficientFixedLevelFinitenessTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem CuspidalInductionReverseAssociationTheorem DeterminantUnitCornerStructureStatement DeterminantUnitSmoothDualStatement GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement LeviCuspidalConstituentTheorem LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem MinimalNonzeroJacquetTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem NormalizedJacquetEquivalenceTheorem NormalizedJacquetSubquotientTheorem PadicAssociatedGeometricPiecesTheorem PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement PadicProperRefinedInductionTheorem ProperRefinedInductionTheorem TotalConjugatingCountTheorem associatedFiltration_of_geometricPieces associatedGeometricPieceEquivalence associatedGeometricPieceVanishing associatedJacquetFiltration associatedJacquetFiltration_of_geometricPieces associatedJacquetFiltration_of_prerequisites associatedJacquetFiltration_rankZero compactCoefficientFixedLevelFiniteness compactCoefficientFixedLevelFiniteness_of_cornerStructure continuous_determinantUnitInclusion cuspidalDatum_eq_of_equiv cuspidalInductionReverseAssociation determinantUnitCompactOpenCofinal determinantUnitCornerStructure determinantUnitInclusion determinantUnitInclusion_apply determinantUnitIsotypic_isCompl determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnitTotalIsotypic_compact determinantUnitTotalIsotypic_exhaust exists_leviPiOpenSubgroup_subset fullRefinedInductionEquiv fullRefinedJacquetEquiv geometricPieceFunctor_subsingleton_of_proper_source geometricPieceInducingFunctor geometricPieceSmoothFunctor geometricPieceSmoothFunctor_obj_toRep geometricPieceSmoothFunctor_toRep glCuspidalTensor glCuspidalTensorAssociation induced_quasicuspidal_subrepresentation_subsingleton isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup leviQuasicuspidalDecomposition leviQuasicuspidalDecomposition_of_inputs levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_determinantUnitSubgroup_iff_valuation mem_leviPiOpenSubgroup minimalNonzeroJacquet minimalWeylTransportQuasicuspidal nonassociatedJacquetSubquotients nonassociatedJacquetSubquotients_rankZero normalizedAbs_eq_one_iff normalizedJacquetEquivalence normalizedJacquetSubquotient normalizedRefinedInductionFunctor_subsingleton padicAssociatedGeometricPieces padicLeviFiltrationNoQuasicuspidalSubquotients padicProperRefinedInduction rankZero_jacquetInductionEquiv refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full totalConjugatingCount
open Langlands.AllFieldBZ.CuspidalSupport
open Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uV uF

/-- Any two supercuspidal supports of an irreducible smooth representation
of `GL_n(F)` are equal, with independent field and factor universes. -/
theorem glSupercuspidalSupportUniqueness :
    GLSupercuspidalSupportUniquenessStatement.{uV, uF} := by
  intro F T n hn
  let := T.topology
  intro π hπ s s' hs hs'
  obtain ⟨k, ρ, hρ, h, A, hA, _, hsub⟩ := hs
  obtain ⟨l, ρ', hρ', h', A', hA', _, hsub'⟩ := hs'
  have hσ := Langlands.AllFieldBZ.CuspidalSupport.glCuspidalTensor.{uV, uF} F T n hn (T.cuspidalShape ρ h) A
  have hτ := Langlands.AllFieldBZ.CuspidalSupport.glCuspidalTensor.{uV, uF} F T n hn (T.cuspidalShape ρ' h') A'
  have hassoc := Langlands.AllFieldBZ.CuspidalSupport.cuspidalInductionReverseAssociation.{uF, uV, uV} F T n
    (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h')
    (FiniteTensor.externalSmoothObject (fun i => (A i).obj))
    (FiniteTensor.externalSmoothObject (fun i => (A' i).obj))
    hσ.1 hσ.2 hτ.1 hτ.2
  apply hρ.symm.trans
  apply Eq.trans _ hρ'
  apply Langlands.AllFieldBZ.CuspidalSupport.glCuspidalTensorAssociation.{uV, uF} F T n hn
    k l ρ ρ' h h' A A' hA hA'
  apply hassoc
  obtain ⟨S, Q, ⟨e⟩⟩ := hsub
  obtain ⟨S', Q', ⟨e'⟩⟩ := hsub'
  refine ⟨S, Q, S', Q', ?_, ⟨SmoothRep.equivOfIso (e.symm.trans e')⟩⟩
  exact (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso e)).mp hπ

end Langlands.AllFieldBZ
