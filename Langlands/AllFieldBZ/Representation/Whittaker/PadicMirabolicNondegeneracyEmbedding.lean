import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalEmbeddingProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.FixedSupportDetectedEquiv
import Langlands.AllFieldBZ.Representation.Whittaker.PadicMirabolicNondegeneracyOrder

/-!
# All-field version of `Langlands.Representation.Whittaker.PadicMirabolicNondegeneracyEmbedding`

Port to an arbitrary nonarchimedean local field (`Langlands.AllFieldBZ.LocalFieldPackage`)
of the p-adic draft module `Langlands.Representation.Whittaker.PadicMirabolicNondegeneracyEmbedding`, which is not published.
See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy
open CategoryTheory
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.Derivative hiding CuspidalProductDetectedConstituentData GeneralLinearDerivativeExactnessStatement GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing LeftMixedProductHomogeneity MirabolicDerivativeDetection MirabolicHighestDerivativePairingStatement MirabolicProductMinusCompatibilityStatement MirabolicProductRestrictionStatement OrderedCuspidalProductNoDegenerateSubmodules PartialDerivativeJacquetComparisonStatement RightMixedProductDerivativeFiltrationStatement RightMixedProductPhiMinusDetection binaryNormalizedProductLeftZeroSwapIso binaryNormalizedProductSwapZeroIso binaryRightZeroDerivativeIso chooseCuspidalProductDetectedConstituent cuspidalProductTopDerivativeLineEquiv finiteProductTopDerivativeLineEquiv generalLinearDerivative generalLinearDerivativeExactness generalLinearDerivativeLeibnizFiltration generalLinearDerivativeLeibnizFiltration_left_zero generalLinearDerivativeLeibnizFiltration_pos generalLinearDerivativeLeibnizFiltration_right_zero generalLinearDerivativeLeibnizFiltration_zero generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_mapsShortExact generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_mapsShortExact generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap generalLinearRestriction_mapsShortExact hasNonzeroDerivative_iff hasNonzeroDerivative_of_isHomogeneous isGluedFromFamily_repRankCast isHomogeneous_of_subsingleton isoRankCastOfEquiv le_level_of_hasNonzeroDerivative leftMixedProductDerivative leftMixedProductDerivativeIso leftMixedProductDerivativeVanishing leftMixedProductHomogeneity leftMixedProduct_rankCast leibnizPiece leibnizPiece_obj leibnizPiece_zero leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizRestrictedProductSourceIso leibnizRestrictionDerivativeExact leibnizRestrictionDerivativeQuotient leibnizRestrictionDerivativeSubobject leibnizRestrictionQuotientPiece leibnizRestrictionQuotientPieceIso leibnizRestrictionQuotient_glued leibnizRestrictionQuotient_subsingleton leibnizRestrictionSubobjectPiece leibnizRestrictionSubobjectSourceIso leibnizRestrictionSubobject_glued leibnizSource leibnizSourceLeftZeroIso leibnizSourceLeftZeroPieceIso leibnizSourceRightZeroIso leibnizSourceRightZeroPieceIso leibnizSource_glued_pos leibnizSource_zero leibnizZeroFirstSmoothPieceIso level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeAdjunction mirabolicDerivativeAdjunction_comp_left mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrderAdjunction mirabolicDerivativeOfOrderAdjunction_comp_left mirabolicDerivativeOfOrderAdjunction_unit mirabolicDerivativeOfOrderAdjunction_unit_comp mirabolicDerivativeOfOrderRightAdjoint mirabolicDerivativeOfOrderUnit mirabolicDerivativeOfOrderUnitKer mirabolicDerivativeOfOrderUnit_injective mirabolicDerivativeOfOrderUnit_injective_of_forall mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp mirabolicDerivativeOfOrder_map_injective mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivativeRightAdjoint mirabolicDerivative_eq mirabolicDerivative_mapsShortExact mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicHighestDerivativePairing mirabolicProductMinusCompatibility mirabolicProductRestriction mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCastHomEquiv mirabolicRankCastHomEquiv_comp_left mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl mirabolicRankCast_symm_comp mirabolicRankCast_trans orderedCuspidalProductNoDegenerateSubmodules partialDerivative partialDerivativeJacquetComparison partialDerivativeMk partialDerivativeMk_surjective partialDerivativeMk_unipotent partialDerivative_action_mk partialDerivative_map_mk phiHatPlusIterate phiHatPlusIterateAdjunction phiHatPlusIterateAdjunction_comp_left phiHatPlusIterateAdjunction_succ phiMinusIterate phiMinusIterate_mapsShortExact phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero phiMinus_rankCast positiveTwoBlockNormalizedJacquet rightMixedDerivativePiece rightMixedDerivativeSource rightMixedProductDerivativeFiltration rightMixedProductDerivativeFiltration_zero rightMixedProductPhiMinusDetection subsingleton_mirabolicDerivativeOfOrder_unit_ker topDerivativeLineEquiv topProductIso topProductTensorEquiv
open Langlands.AllFieldBZ.Derivative
open Langlands.Derivative.OrderedCuspidalProductNondegeneracy hiding Good HeadExclusion Ordered binaryLineIso binaryShapeIso caseTwo_false exists_injective_of_rankCast finrank_binaryProduct_rank_zero finrank_generalLinearDerivative_order finrank_generalLinearRankCast finrank_generalLinearRankCast_top finrank_graded_of_length_one finrank_topLeibnizPiece finrank_top_binaryProduct generalLinearRankCast_comp_obj generalLinearRankCast_map_injective generalLinearRankCast_symm_obj good_of_iso good_of_supercuspidal good_product good_single good_step good_universeLift_of_supercuspidal hasNonzeroDerivative_eq_of_supercuspidal headExclusion_of_ordered headTailBridge level_of_good mirabolicDerivativeOfOrder_rankCast_obj nontrivial_subrepresentation_of_good nontrivial_top_of_good ordered_tail singleFamily_eq singletonProductLiftIso supercuspidalProperty_transport
open Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy
universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- Distinct cuspidal data have distinct rank-indexed classes. -/
theorem sigma_ne_of_ne (ρ σ : T.CuspidalDatum.{uV, uF}) (h : ρ ≠ σ) :
    letI := T.topology
    (⟨ρ.rank, ρ.cls⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
      ⟨σ.rank, σ.cls⟩ := by
  let := T.topology
  intro hs
  apply h
  rcases ρ with ⟨r, hr, c⟩
  rcases σ with ⟨r', hr', c'⟩
  simp only [Sigma.mk.injEq] at hs
  obtain ⟨rfl, hc⟩ := hs
  simp only [heq_eq_eq] at hc
  subst hc
  rfl

/-- An irreducible representation of `GL_(n+1)(F)` with nonzero top derivative is a
subrepresentation of a good representation: one whose mirabolic restriction is
homogeneous and whose top derivative is one-dimensional. -/
theorem exists_good_embedding
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier))
    (hX : letI := T.topology; X.IsIrreducible)
    (hJX : letI := T.topology
      Nontrivial ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj X)) :
    letI := T.topology
    ∃ (P : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)) (j : X ⟶ P),
      Function.Injective (SmoothRep.hom j) ∧ Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.Good T ψ P := by
  classical
  let := T.topology
  -- a supercuspidal embedding, and a good reordering of its factors
  obtain ⟨k, ρ, hsub⟩ := glSupercuspidalEmbedding.{uV, uF} F T (n + 1) (Nat.succ_pos n) X hX
  obtain ⟨h, A, hA, hXA⟩ := hsub
  obtain ⟨e, he⟩ := exists_ordered_perm T ρ
  let ρ' : Fin k → T.CuspidalDatum.{uV, uF} := fun i => ρ (e i)
  let A' : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ' i).rank) :=
    fun i => A (e i)
  have hA' : ∀ i, (ρ' i).IsRepresentedBy (A' i) := fun i => hA (e i)
  have h' : ∑ i, (ρ' i).rank = n + 1 := by
    rw [Equiv.sum_comp e (fun i => (ρ i).rank)]
    exact h
  let B := T.cuspidalShape ρ' h'
  let P := T.cuspidalProductInduced ρ' h' A'
  have hord : Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.Ordered T B A' := by
    intro i j hij
    have hne := sigma_ne_of_ne T (ρ' j) ((ρ' i).twist 1) (he i j hij)
    change (⟨(ρ' j).rank, (A' j).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
      ⟨(ρ' i).rank, T.supercuspidalClassRealPowerTwist (ρ' i).rank 1 (A' i).isoClass⟩
    rw [hA' j, hA' i]
    exact hne
  obtain ⟨l, hl⟩ : ∃ l, k = l + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun hk => ?_
    subst hk
    simp at h'
  have hgood : Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.Good T ψ P := Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.good_product T ψ l B hl A' hord n rfl
  -- an irreducible subrepresentation of the good product
  have hPnt : Nontrivial P :=
    Langlands.AllFieldBZ.Derivative.LevelCalculus.nontrivial_of_hasNonzeroDerivative T ψ ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T n).obj P)
      ⟨⟨Nat.succ_pos n, le_rfl⟩, Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_top_of_good T ψ P hgood⟩
  have hfin : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier))
      P.representation.asModule :=
    Classification.irreducibleProductFiniteLength F T (n + 1) (Nat.succ_pos n) B
      (fun i => (A' i).obj) (fun i => (A' i).property.1)
  have : IsArtinian (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier))
      P.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  have : Nontrivial P.representation.asModule := hPnt
  obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le
    (⊤ : Submodule (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier))
      P.representation.asModule)).resolve_left top_ne_bot
  let S : Subrepresentation P.representation := Subrepresentation.ofSubmodule' N
  let Y := SmoothRep.subrepresentation P S
  let iY : Y ⟶ P := SmoothRep.subtype P S
  have hiY : Function.Injective (SmoothRep.hom iY) := SmoothRep.subtype_injective P S
  have hY : Y.IsIrreducible := by
    let jN : Y.representation.asModule →ₗ[MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier)] N :=
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (SmoothRep.hom iY)).codRestrict N (fun v => v.property)
    have hjN : Function.Bijective jN :=
      ⟨fun _ _ hxy => Subtype.ext (congrArg Subtype.val hxy),
        fun v => ⟨⟨v.val, v.property⟩, rfl⟩⟩
    apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
    exact (jN.isSimpleModule_iff_of_bijective hjN).mpr (isSimpleModule_iff_isAtom.mpr hN)
  have hYnt : Nontrivial Y := by
    let := hY
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier))
      Y.representation.asModule
  -- `Y` has nonzero top derivative, by homogeneity of the good product
  have hJY : Nontrivial ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj Y) := by
    obtain ⟨hk, hnt⟩ := (Langlands.AllFieldBZ.Derivative.hasNonzeroDerivative_of_isHomogeneous T ψ (Nat.succ_pos n) hgood.1
      (Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.level_of_good T ψ P hgood) ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T n).map iY) hiY hYnt).1
    rw [Langlands.AllFieldBZ.Derivative.RestrictionBridge.generalLinearDerivative_succ_obj_eq T ψ le_rfl hk Y]
    exact hnt
  -- `X` and `Y` have the same supercuspidal support
  have hsY : T.IsSupercuspidalSupport Y (List.ofFn ρ' : Multiset _) :=
    ⟨k, ρ', rfl, LocalFieldPackage.TopologicalData.IsCuspidalSubrepresentation.isCuspidalConstituent
      ⟨h', A', hA', hY, SmoothRep.hom iY, hiY⟩⟩
  have hsX : T.IsSupercuspidalSupport X (List.ofFn ρ' : Multiset _) := by
    refine ⟨k, ρ, ?_, LocalFieldPackage.TopologicalData.IsCuspidalSubrepresentation.isCuspidalConstituent ⟨h, A, hA, hXA⟩⟩
    exact Multiset.coe_eq_coe.mpr (Equiv.Perm.ofFn_comp_perm e ρ).symm
  let E := CuspidalSupport.fixedSupportDetectedEquiv T ψ (Nat.succ_pos n) X Y _ hsX hsY hJX hJY
  refine ⟨P, SmoothRep.ofHom ((SmoothRep.hom iY).comp E.toIntertwiningMap), ?_, hgood⟩
  exact hiY.comp E.injective

end Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy
