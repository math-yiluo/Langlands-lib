import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociationForwardHomProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.AllFieldBZ.Representation.CuspidalSupport.InducedJacquetEvaluation
import Langlands.AllFieldBZ.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
import Langlands.Representation.CuspidalSupport.TwoBlockAssociationProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.TwoBlockAssociationProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.TwoBlockAssociationProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open Representation
namespace Langlands.AllFieldBZ.CuspidalSupport.JacquetLength
open Langlands.CuspidalSupport.JacquetLength hiding count count_bot count_strictMono count_top count_top_eq_ker_add_range haveSameJordanHolderFactors_of_hypotheses isIrreducible_transport jacquetLength jacquetLength_congr jacquetLength_eq_add_of_exact jacquetLength_eq_zero_of_subsingleton jacquetLength_induced_le jacquetLength_le jacquetLength_step jacquetLength_top nonempty_equiv_of_count_eq_one nonempty_equiv_of_jacquetLength_eq_one normalizedJacquetEquiv one_le_jacquetLength_of_isSubquotient one_le_jacquetLength_stepQuotient stepQuotient subtypeMap subtypeMap_injective topEquiv
open Langlands.GeneralLinear
universe uF uU uV uW

section Schur
variable {k : Type*} [Field k] {G : Type*} [Monoid G]
  {U : Type*} {V : Type*} {W : Type*}
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

end Schur
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData) {n : ℕ}

/-- **Detection.** Let `X` have summed Jacquet length one over `I`, and let
`B, C ∈ I`. Nonzero maps from the Jacquet modules of `X` along `B` and `C` to
irreducible representations `σ` and `τ` force `B = C` and an actual
equivalence of the normalized inductions of `σ` and `τ`. -/
theorem nonempty_equiv_of_jacquetLength_eq_one (I : Finset (BlockShape n))
    {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {X : Representation ℂ (GeneralLinear n F.Carrier) U}
    (hX : jacquetLength T I X = 1) {B C : BlockShape n} (hB : B ∈ I) (hC : C ∈ I)
    {σ : Representation ℂ (B.Levi F.Carrier) V} {τ : Representation ℂ (C.Levi F.Carrier) W}
    (hσ : σ.IsIrreducible) (hτ : τ.IsIrreducible)
    (g : (T.normalizedJacquet B X).IntertwiningMap σ) (hg : g ≠ 0)
    (g' : (T.normalizedJacquet C X).IntertwiningMap τ) (hg' : g' ≠ 0) :
    Nonempty ((T.normalizedParabolicInduced B σ).Equiv (T.normalizedParabolicInduced C τ)) := by
  have hpos : ∀ D ∈ I, Nontrivial (D.JacquetModule X) →
      (1 : ℕ∞) ≤ repLength (T.normalizedJacquet D X) := fun D _ h =>
    Order.one_le_iff_pos.mpr (repLength_pos_iff.mpr h)
  have hBpos := hpos B hB (nontrivial_of_ne_zero g hg)
  have hCpos := hpos C hC (nontrivial_of_ne_zero g' hg')
  have hBC : B = C := by
    classical
    by_contra hne
    have hsub : ({B, C} : Finset (BlockShape n)) ⊆ I := Finset.insert_subset hB
      (Finset.singleton_subset_iff.mpr hC)
    have hle := Finset.sum_le_sum_of_subset
      (f := fun D => repLength (T.normalizedJacquet D X)) hsub
    rw [Finset.sum_pair hne] at hle
    have h2 : (1 : ℕ∞) + 1 ≤ 1 := by
      calc (1 : ℕ∞) + 1 ≤ _ := add_le_add hBpos hCpos
        _ ≤ jacquetLength T I X := hle
        _ = 1 := hX
    exact absurd h2 (by norm_num)
  subst hBC
  have hlen : repLength (T.normalizedJacquet B X) = 1 := by
    refine le_antisymm ?_ hBpos
    calc repLength (T.normalizedJacquet B X) ≤ jacquetLength T I X :=
          Finset.single_le_sum (f := fun D => repLength (T.normalizedJacquet D X))
            (fun _ _ => zero_le) hB
      _ = 1 := hX
  obtain ⟨e⟩ := nonempty_equiv_of_ne_zero (repLength_eq_one_iff.mp hlen) hσ hτ g hg g' hg'
  exact ⟨T.normalizedParabolicInducedEquiv B e⟩

/-- **Count-one detection on a subrepresentation.** Inside the normalized
induction of `σ` from `B`, a subrepresentation `S` of count one on which an
intertwiner `A` to the normalized induction of `τ` from `C` does not vanish
forces the two inductions to be equivalent, when `B, C ∈ I`. -/
theorem nonempty_equiv_of_count_eq_one (I : Finset (BlockShape n))
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {B C : BlockShape n} (hB : B ∈ I) (hC : C ∈ I)
    {σ : Representation ℂ (B.Levi F.Carrier) V} {τ : Representation ℂ (C.Levi F.Carrier) W}
    (hσ : σ.IsIrreducible) (hτ : τ.IsIrreducible)
    (A : (T.normalizedParabolicInduced B σ).IntertwiningMap (T.normalizedParabolicInduced C τ))
    (S : Subrepresentation (T.normalizedParabolicInduced B σ))
    (hS : count T I S = 1) (hAS : ∃ v ∈ S, A v ≠ 0) :
    Nonempty ((T.normalizedParabolicInduced B σ).Equiv (T.normalizedParabolicInduced C τ)) := by
  obtain ⟨v, hv, hAv⟩ := hAS
  have hJ : jacquetLength T I S.toRepresentation = 1 := by
    have h := (ENat.toNat_eq_iff one_ne_zero).mp hS
    rwa [Nat.cast_one] at h
  have hv0 : subtypeMap S ⟨v, hv⟩ ≠ 0 := fun h => hAv (by
    have h' : v = 0 := h
    rw [h', map_zero])
  obtain ⟨g, hg⟩ := exists_ne_zero_normalizedJacquet_hom T B (subtypeMap S)
    (ne_zero_of_apply_ne_zero _ hv0)
  obtain ⟨g', hg'⟩ := exists_ne_zero_normalizedJacquet_hom T C (A.comp (subtypeMap S))
    (ne_zero_of_apply_ne_zero (g := A.comp (subtypeMap S)) ⟨v, hv⟩ hAv)
  exact nonempty_equiv_of_jacquetLength_eq_one T I hJ hB hC hσ hτ g hg g' hg'

/-- **Two-block matching from the analytic inputs.** For associated block
shapes `B` and `C` with `B.length = 2`, irreducible quasicuspidal data `σ` on
`B` and `τ` on `C`, and nonzero intertwiners in both directions between their
normalized inductions, the two inductions have the same composition factors
with multiplicities, provided the two Jacquet statements for quasicuspidal
induction hold at rank `n` in both carrier universes. -/
theorem haveSameJordanHolderFactors_of_hypotheses
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (hnon' : NonassociatedJacquetSubquotientsTheorem.{uF, uW} F T n)
    (hfilt : AssociatedJacquetFiltrationTheorem.{uF, uV} F T n)
    (hfilt' : AssociatedJacquetFiltrationTheorem.{uF, uW} F T n)
    (B C : BlockShape n) (hassoc : Langlands.CuspidalSupport.LevisAssociated (F := F.Carrier) B C)
    (hB2 : B.length = 2) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      σ.IsIrreducible → Langlands.CuspidalSupport.IsLeviQuasicuspidal B σ.representation →
      τ.IsIrreducible → Langlands.CuspidalSupport.IsLeviQuasicuspidal C τ.representation →
      ∀ (A : (T.normalizedParabolicInduced B σ.representation).IntertwiningMap
          (T.normalizedParabolicInduced C τ.representation))
        (A' : (T.normalizedParabolicInduced C τ.representation).IntertwiningMap
          (T.normalizedParabolicInduced B σ.representation)), A ≠ 0 → A' ≠ 0 →
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced B σ.representation))
        (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  let := T.topology
  intro σ τ hσ hσq hτ hτq A A' hA0 hA'0
  have hmin := minimalNonzeroJacquet.{uF, max uF uV}
  have hmin' := minimalNonzeroJacquet.{uF, max uF uW}
  have hcount := totalConjugatingCount.{uF}
  let I := associatedShapes F.Carrier B
  have hBI : B ∈ I := mem_associatedShapes.mpr (Langlands.CuspidalSupport.LevisAssociated.refl B)
  have hCI : C ∈ I := mem_associatedShapes.mpr hassoc
  have hI₁ : ∀ D, Langlands.CuspidalSupport.LevisAssociated (F := F.Carrier) B D → D ∈ I :=
    fun D h => mem_associatedShapes.mpr h
  have hI₂ : ∀ D ∈ I, Langlands.CuspidalSupport.LevisAssociated (F := F.Carrier) B D :=
    fun D h => mem_associatedShapes.mp h
  have hI₃ : ∀ D, Langlands.CuspidalSupport.LevisAssociated (F := F.Carrier) C D → D ∈ I :=
    fun D h => mem_associatedShapes.mpr (hassoc.trans h)
  have hI₄ : ∀ D ∈ I, Langlands.CuspidalSupport.LevisAssociated (F := F.Carrier) C D :=
    fun D h => hassoc.symm.trans (mem_associatedShapes.mp h)
  have hC2 : C.length = 2 := hassoc.length_eq ▸ hB2
  have hπ : IsSmooth (T.normalizedParabolicInduced B σ.representation) :=
    T.isSmooth_normalizedParabolicInduced B σ.representation
  have hπ' : IsSmooth (T.normalizedParabolicInduced C τ.representation) :=
    T.isSmooth_normalizedParabolicInduced C τ.representation
  have hle : jacquetLength T I (T.normalizedParabolicInduced B σ.representation) ≤ (2 : ℕ) := by
    have h := jacquetLength_induced_le T hfilt hcount B I hI₂ σ hσ hσq
    have h2 : B.length.factorial = 2 := by rw [hB2]; rfl
    rw [h2] at h
    exact h
  have hle' : jacquetLength T I (T.normalizedParabolicInduced C τ.representation) ≤ (2 : ℕ) := by
    have h := jacquetLength_induced_le T hfilt' hcount C I hI₄ τ hτ hτq
    have h2 : C.length.factorial = 2 := by rw [hC2]; rfl
    rw [h2] at h
    exact h
  have hfin := ne_top_of_le_ne_top (ENat.natCast_ne_top 2) hle
  have hfin' := ne_top_of_le_ne_top (ENat.natCast_ne_top 2) hle'
  have hμ := count_strictMono T I hπ hfin
    (one_le_jacquetLength_stepQuotient T hmin hnon B I hI₁ σ hσq)
  have hν := count_strictMono T I hπ' hfin'
    (one_le_jacquetLength_stepQuotient T hmin' hnon' C I hI₃ τ hτq)
  have hμ2 : count T I (⊤ : Subrepresentation (T.normalizedParabolicInduced B σ.representation))
      ≤ 2 := by
    rw [count_top]
    exact ENat.toNat_le_of_le_natCast hle
  have hν2 : count T I (⊤ : Subrepresentation (T.normalizedParabolicInduced C τ.representation))
      ≤ 2 := by
    rw [count_top]
    exact ENat.toNat_le_of_le_natCast hle'
  refine LengthTwo.haveSameJordanHolderFactors_of_count_le_two (count T I) (count T I)
    hμ hν (count_bot T I) (count_bot T I) hμ2 hν2 A A' hA0 hA'0
    (count_top_eq_ker_add_range T I hπ hfin A) (count_top_eq_ker_add_range T I hπ' hfin' A')
    ?_ ?_
  · intro S hS hAS
    exact nonempty_equiv_of_count_eq_one T I hBI hCI hσ hτ A S hS hAS
  · intro S hS hAS
    obtain ⟨e⟩ := nonempty_equiv_of_count_eq_one T I hCI hBI hτ hσ A' S hS hAS
    exact ⟨e.symm⟩

end Langlands.AllFieldBZ.CuspidalSupport.JacquetLength
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedCuspidalInductionFactorsTheorem AssociatedCuspidalInductionHomTheorem AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem CompactCoefficientFixedLevelFinitenessTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem DeterminantUnitCornerStructureStatement DeterminantUnitSmoothDualStatement GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement IrreducibleQuasicuspidalLeviAdmissibilityTheorem LeviCuspidalBlockIsolationTheorem LeviCuspidalConstituentTheorem LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem MinimalNonzeroJacquetTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem NormalizedJacquetEquivalenceTheorem NormalizedJacquetSubquotientTheorem NormalizedQuasicuspidalEmbeddingTheorem PadicAssociatedGeometricPiecesTheorem PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement PadicProperRefinedInductionTheorem ProperRefinedInductionTheorem TotalConjugatingCountTheorem TwoBlockAssociatedCuspidalInductionFactorsTheorem ZeroRankCuspidalEmbeddingTheorem associatedCuspidalInductionFactors_of_adjacent associatedCuspidalInductionFactors_of_length_lt_two associatedCuspidalInductionHomTheorem associatedFiltration_of_geometricPieces associatedGeometricPieceEquivalence associatedGeometricPieceVanishing associatedJacquetFiltration associatedJacquetFiltration_of_geometricPieces associatedJacquetFiltration_of_prerequisites associatedJacquetFiltration_rankZero compactCoefficientFixedLevelFiniteness compactCoefficientFixedLevelFiniteness_of_cornerStructure continuous_determinantUnitInclusion cuspidalDatum_eq_of_equiv determinantUnitCompactOpenCofinal determinantUnitCornerStructure determinantUnitInclusion determinantUnitInclusion_apply determinantUnitIsotypic_isCompl determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnitTotalIsotypic_compact determinantUnitTotalIsotypic_exhaust determinantUnit_sup_center_finiteIndex exists_leviPiOpenSubgroup_subset exists_ne_zero_normalizedJacquet_hom exists_ne_zero_of_gradedRepresentation_equiv exists_ne_zero_to_normalizedParabolicInduced factors_of_blockMap factors_step fullRefinedInductionEquiv fullRefinedJacquetEquiv geometricPieceFunctor_subsingleton_of_proper_source geometricPieceInducingFunctor geometricPieceSmoothFunctor geometricPieceSmoothFunctor_obj_toRep geometricPieceSmoothFunctor_toRep glCuspidalTensorAssociation inducedEvaluation inducedEvaluation_levi inducedEvaluation_parabolic inducedEvaluation_translate inducedEvaluation_unipotent induced_quasicuspidal_subrepresentation_subsingleton isCompact_leviPiOpenSubgroup isIrreducible_normalizedParabolicInduced_singleBlock isOpen_determinantUnitSubgroup jacquetEvaluation jacquetEvaluation_mk jacquetEvaluation_ne_zero leviCuspidalBlockIsolationTheorem leviCuspidalConstituentTheorem leviCuspidalConstituent_rankZero leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup leviQuasicuspidalDecomposition leviQuasicuspidalDecomposition_of_inputs levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_determinantUnitSubgroup_iff_valuation mem_leviPiOpenSubgroup minimalNonzeroJacquet minimalWeylTransportQuasicuspidal nonassociatedJacquetSubquotients nonassociatedJacquetSubquotients_rankZero normalizedAbs_eq_one_iff normalizedJacquetEquivalence normalizedJacquetSubquotient normalizedRefinedInductionFunctor_subsingleton padicAssociatedGeometricPieces padicLeviFiltrationNoQuasicuspidalSubquotients padicProperRefinedInduction parabolic_le_normalizer_unipotentSubgroup rankZero_jacquetInductionEquiv refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full totalConjugatingCount twoBlockAssociatedCuspidalInductionFactors twoBlockAssociatedCuspidalInductionFactors_of_hypotheses
open Langlands.GeneralLinear
open Langlands.CuspidalSupport.JacquetLength hiding count count_bot count_strictMono count_top count_top_eq_ker_add_range haveSameJordanHolderFactors_of_hypotheses isIrreducible_transport jacquetLength jacquetLength_congr jacquetLength_eq_add_of_exact jacquetLength_eq_zero_of_subsingleton jacquetLength_induced_le jacquetLength_le jacquetLength_step jacquetLength_top nonempty_equiv_of_count_eq_one nonempty_equiv_of_jacquetLength_eq_one normalizedJacquetEquiv one_le_jacquetLength_of_isSubquotient one_le_jacquetLength_stepQuotient stepQuotient subtypeMap subtypeMap_injective topEquiv
open Langlands.AllFieldBZ.CuspidalSupport.JacquetLength hiding isIrreducible_transport
universe uF uV uW

/-- **BZ77 §2.16(1), two-block case, from the remaining inputs.** The
two-block factor matching for associated irreducible cuspidal data holds,
provided the nonassociated vanishing and associated filtration statements for
Jacquet modules of quasicuspidal induction hold in positive rank for both
carrier universes, and associated irreducible cuspidal data give nonzero
intertwiners in both directions. -/
theorem twoBlockAssociatedCuspidalInductionFactors_of_hypotheses
    (hnon : ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
      (n : ℕ), 0 < n → NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (hnon' : ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
      (n : ℕ), 0 < n → NonassociatedJacquetSubquotientsTheorem.{uF, uW} F T n)
    (hfilt : ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
      (n : ℕ), 0 < n → AssociatedJacquetFiltrationTheorem.{uF, uV} F T n)
    (hfilt' : ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
      (n : ℕ), 0 < n → AssociatedJacquetFiltrationTheorem.{uF, uW} F T n)
    (hHom : AssociatedCuspidalInductionHomTheorem.{uF, uV, uW})
    (hHom' : AssociatedCuspidalInductionHomTheorem.{uF, uW, uV}) :
    TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW} := by
  intro F T n hn
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro B C σ τ hB2 hσ hσc hτ hτc hassoc
  have hL : LevisAssociated (F := F.Carrier) B C := by
    obtain ⟨w, hw, _⟩ := hassoc
    exact ⟨⟨w, hw⟩⟩
  obtain ⟨A, hA⟩ := hHom F T n hn B C σ τ hσ hσc hτ hτc hassoc
  obtain ⟨A', hA'⟩ := hHom' F T n hn C B τ σ hτ hτc hσ hσc hassoc.symm
  exact Langlands.AllFieldBZ.CuspidalSupport.JacquetLength.haveSameJordanHolderFactors_of_hypotheses T (hnon F T n hn) (hnon' F T n hn)
    (hfilt F T n hn) (hfilt' F T n hn) B C hL hB2 σ τ hσ hσc.2 hτ hτc.2 A A' hA hA'

/-- **BZ77 §2.16(1), two-block case.** For associated irreducible cuspidal
data on a two-block Levi, the normalized inductions have the same
Jordan–Hölder factors with multiplicities. -/
theorem twoBlockAssociatedCuspidalInductionFactors :
    TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW} :=
  twoBlockAssociatedCuspidalInductionFactors_of_hypotheses
    (fun F T n _ => nonassociatedJacquetSubquotients F T n)
    (fun F T n _ => nonassociatedJacquetSubquotients F T n)
    (fun F T n _ => associatedJacquetFiltration F T n)
    (fun F T n _ => associatedJacquetFiltration F T n)
    associatedCuspidalInductionHomTheorem
    associatedCuspidalInductionHomTheorem

end Langlands.AllFieldBZ.CuspidalSupport
