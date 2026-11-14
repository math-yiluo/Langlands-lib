import Langlands.AllFieldBZ.Representation.Whittaker.PadicMirabolicNondegeneracyEmbedding
import Langlands.AllFieldBZ.Representation.Whittaker.TopDerivativeDual

/-!
# All-field version of `Langlands.Representation.Whittaker.PadicMirabolicNondegeneracy`

Port to an arbitrary nonarchimedean local field (`Langlands.AllFieldBZ.LocalFieldPackage`)
of the p-adic draft module `Langlands.Representation.Whittaker.PadicMirabolicNondegeneracy`, which is not published.
See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy
open CategoryTheory
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.Derivative hiding CuspidalProductDetectedConstituentData GeneralLinearDerivativeExactnessStatement GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing LeftMixedProductHomogeneity MirabolicDerivativeDetection MirabolicHighestDerivativePairingStatement MirabolicProductMinusCompatibilityStatement MirabolicProductRestrictionStatement OrderedCuspidalProductNoDegenerateSubmodules PartialDerivativeJacquetComparisonStatement RightMixedProductDerivativeFiltrationStatement RightMixedProductPhiMinusDetection binaryNormalizedProductLeftZeroSwapIso binaryNormalizedProductSwapZeroIso binaryRightZeroDerivativeIso chooseCuspidalProductDetectedConstituent cuspidalProductTopDerivativeLineEquiv finiteProductTopDerivativeLineEquiv generalLinearDerivative generalLinearDerivativeExactness generalLinearDerivativeLeibnizFiltration generalLinearDerivativeLeibnizFiltration_left_zero generalLinearDerivativeLeibnizFiltration_pos generalLinearDerivativeLeibnizFiltration_right_zero generalLinearDerivativeLeibnizFiltration_zero generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_mapsShortExact generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_mapsShortExact generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap generalLinearRestriction_mapsShortExact hasNonzeroDerivative_iff hasNonzeroDerivative_of_isHomogeneous isGluedFromFamily_repRankCast isHomogeneous_of_subsingleton isoRankCastOfEquiv le_level_of_hasNonzeroDerivative leftMixedProductDerivative leftMixedProductDerivativeIso leftMixedProductDerivativeVanishing leftMixedProductHomogeneity leftMixedProduct_rankCast leibnizPiece leibnizPiece_obj leibnizPiece_zero leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizRestrictedProductSourceIso leibnizRestrictionDerivativeExact leibnizRestrictionDerivativeQuotient leibnizRestrictionDerivativeSubobject leibnizRestrictionQuotientPiece leibnizRestrictionQuotientPieceIso leibnizRestrictionQuotient_glued leibnizRestrictionQuotient_subsingleton leibnizRestrictionSubobjectPiece leibnizRestrictionSubobjectSourceIso leibnizRestrictionSubobject_glued leibnizSource leibnizSourceLeftZeroIso leibnizSourceLeftZeroPieceIso leibnizSourceRightZeroIso leibnizSourceRightZeroPieceIso leibnizSource_glued_pos leibnizSource_zero leibnizZeroFirstSmoothPieceIso level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeAdjunction mirabolicDerivativeAdjunction_comp_left mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrderAdjunction mirabolicDerivativeOfOrderAdjunction_comp_left mirabolicDerivativeOfOrderAdjunction_unit mirabolicDerivativeOfOrderAdjunction_unit_comp mirabolicDerivativeOfOrderRightAdjoint mirabolicDerivativeOfOrderUnit mirabolicDerivativeOfOrderUnitKer mirabolicDerivativeOfOrderUnit_injective mirabolicDerivativeOfOrderUnit_injective_of_forall mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp mirabolicDerivativeOfOrder_map_injective mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivativeRightAdjoint mirabolicDerivative_eq mirabolicDerivative_mapsShortExact mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicHighestDerivativePairing mirabolicProductMinusCompatibility mirabolicProductRestriction mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCastHomEquiv mirabolicRankCastHomEquiv_comp_left mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl mirabolicRankCast_symm_comp mirabolicRankCast_trans orderedCuspidalProductNoDegenerateSubmodules partialDerivative partialDerivativeJacquetComparison partialDerivativeMk partialDerivativeMk_surjective partialDerivativeMk_unipotent partialDerivative_action_mk partialDerivative_map_mk phiHatPlusIterate phiHatPlusIterateAdjunction phiHatPlusIterateAdjunction_comp_left phiHatPlusIterateAdjunction_succ phiMinusIterate phiMinusIterate_mapsShortExact phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero phiMinus_rankCast positiveTwoBlockNormalizedJacquet rightMixedDerivativePiece rightMixedDerivativeSource rightMixedProductDerivativeFiltration rightMixedProductDerivativeFiltration_zero rightMixedProductPhiMinusDetection subsingleton_mirabolicDerivativeOfOrder_unit_ker topDerivative topDerivativeLineEquiv topDerivative_eq topDerivative_zero topProductIso topProductTensorEquiv
open Langlands.AllFieldBZ.Derivative
open Langlands.Jacquet.Localization
open Langlands.Derivative.OrderedCuspidalProductNondegeneracy hiding Good HeadExclusion Ordered binaryLineIso binaryShapeIso caseTwo_false exists_injective_of_rankCast finrank_binaryProduct_rank_zero finrank_generalLinearDerivative_order finrank_generalLinearRankCast finrank_generalLinearRankCast_top finrank_graded_of_length_one finrank_topLeibnizPiece finrank_top_binaryProduct generalLinearRankCast_comp_obj generalLinearRankCast_map_injective generalLinearRankCast_symm_obj good_of_iso good_of_supercuspidal good_product good_single good_step good_universeLift_of_supercuspidal hasNonzeroDerivative_eq_of_supercuspidal headExclusion_of_ordered headTailBridge level_of_good mirabolicDerivativeOfOrder_rankCast_obj nontrivial_subrepresentation_of_good nontrivial_top_of_good ordered_tail singleFamily_eq singletonProductLiftIso supercuspidalProperty_transport
open Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy
universe uF uV

variable {F : LocalFieldPackage.{uF}}

/-! ### The top derivative and the full upper coinvariants -/

/-- Rank transport of a mirabolic representation does not change whether its full upper
coinvariants are nonzero. -/
theorem nontrivial_coinvariants_rankCast (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ)
    {N M : ℕ} (h : N = M)
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) :
    let := T.topology
    Nontrivial (Coinvariants ((Langlands.AllFieldBZ.Derivative.mirabolicRankCast T h).obj B).representation
        (Mirabolic.upperUnipotent M F.Carrier) (TopLocalization.mirabolicUpperCharacter ψ M)) ↔
      Nontrivial (Coinvariants B.representation (Mirabolic.upperUnipotent N F.Carrier)
        (TopLocalization.mirabolicUpperCharacter ψ N)) := by
  let := T.topology
  subst h
  rw [Langlands.AllFieldBZ.Derivative.mirabolicRankCast_refl]
  rfl

/-- The top derivative of a mirabolic representation is nonzero exactly when its full upper
coinvariants are nonzero. -/
theorem hasNonzeroDerivative_top_iff (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ)
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) :
    let := T.topology
    Langlands.AllFieldBZ.Derivative.HasNonzeroDerivative T ψ B (N + 1) ↔
      Nontrivial (Coinvariants B.representation (Mirabolic.upperUnipotent N F.Carrier)
        (TopLocalization.mirabolicUpperCharacter ψ.complex N)) := by
  let := T.topology
  have hk : 0 < N + 1 ∧ N + 1 ≤ N + 1 := ⟨Nat.succ_pos N, le_rfl⟩
  have h1 : Langlands.AllFieldBZ.Derivative.HasNonzeroDerivative T ψ B (N + 1) ↔
      Nontrivial ((Langlands.AllFieldBZ.Derivative.mirabolicDerivativeOfOrder T ψ N (N + 1) hk).obj B) :=
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨hk, h⟩⟩
  have h2 : Nontrivial ((Langlands.AllFieldBZ.Derivative.mirabolicDerivativeOfOrder T ψ N (N + 1) hk).obj B) ↔
      Nontrivial ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T (Nat.sub_self (N + 1))).obj
        ((Langlands.AllFieldBZ.Derivative.mirabolicDerivativeOfOrder T ψ N (N + 1) hk).obj B)) :=
    (Langlands.AllFieldBZ.Derivative.RestrictionBridge.nontrivial_generalLinearRankCast_iff T _ _).symm
  have h3 : (Langlands.AllFieldBZ.Derivative.generalLinearRankCast T (Nat.sub_self (N + 1))).obj
        ((Langlands.AllFieldBZ.Derivative.mirabolicDerivativeOfOrder T ψ N (N + 1) hk).obj B) =
      (Langlands.AllFieldBZ.Derivative.mirabolicDerivative T ψ 0 N).obj
        ((Langlands.AllFieldBZ.Derivative.mirabolicRankCast T (Nat.zero_add N).symm).obj B) :=
    congrArg (fun J => J.obj B) (Langlands.AllFieldBZ.Derivative.mirabolicDerivativeOfOrder_top T ψ N hk)
  have h4 := LevelCalculus.nontrivial_iff_of_iso
    ((Langlands.AllFieldBZ.Derivative.TopLocalization.mirabolicLocalizationIso T ψ N).app
      ((Langlands.AllFieldBZ.Derivative.mirabolicRankCast T (Nat.zero_add N).symm).obj B))
  rw [h1, h2, h3, ← h4]
  exact nontrivial_coinvariants_rankCast T ψ.complex (Nat.zero_add N).symm B

/-- The mirabolic upper character used by the top localization is the standard Whittaker
character transported along the mirabolic upper-unipotent identification. -/
theorem mirabolicUpperCharacter_eq_standardCharacter (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    TopLocalization.mirabolicUpperCharacter ψ.complex n =
      (Langlands.Whittaker.standardCharacter ψ n).comp Mirabolic.upperUnipotentEquiv.toMonoidHom := by
  let := T.topology
  rw [TopLocalization.mirabolicUpperCharacter, Langlands.Whittaker.entrywiseCharacter_eq_standardCharacter]

/-! ### Theorem 4.9 -/

/-- **Bernstein–Zelevinsky, Theorem 4.9, over packaged nonarchimedean local fields.** An
irreducible admissible
generic representation of `GL_(n+1)(F)` has no nonzero mirabolic subrepresentation whose
standard full upper-unipotent character quotient vanishes. -/
theorem mirabolicNondegeneracy (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    letI := T.topology
    Langlands.Whittaker.IsGeneric ψ n π →
    ∀ U : Subrepresentation (π.comp (mirabolic n F.Carrier).subtype),
      Subsingleton
        (Coinvariants U.toRepresentation (Mirabolic.upperUnipotent n F.Carrier)
          ((Langlands.Whittaker.standardCharacter ψ n).comp Mirabolic.upperUnipotentEquiv.toMonoidHom)) →
      U = ⊥ := by
  classical
  let := T.topology
  have := T.generalLinearTopologicalGroup (n + 1)
  intro hgen U hU
  obtain ⟨hirr, hadm, hfun⟩ := hgen
  -- the representation as a smooth representation in the saturated universe
  let X0 : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier) := SmoothRep.of π hadm.1
  let X := SmoothRep.universeLift.{uF} X0
  have hX : X.IsIrreducible := (SmoothRep.isIrreducible_universeLift_iff X0).2 hirr
  -- its top derivative is nonzero
  have hJX : Nontrivial ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj X) := by
    apply (hasStandardFunctional_iff_nontrivial_topDerivative T ψ n X).1
    obtain ⟨ℓ, hℓ⟩ := hfun
    let ℓ'val : Module.Dual ℂ X :=
      { toFun := fun x => ℓ.val (ULift.down x)
        map_add' := fun x y => map_add ℓ.val x.down y.down
        map_smul' := fun c x => map_smul ℓ.val c x.down }
    have hmem : ℓ'val ∈ Langlands.Whittaker.functionals (upperUnipotent (n + 1) F.Carrier)
        (Langlands.Whittaker.standardCharacter ψ n) X.representation := by
      intro u x
      exact ℓ.property u (ULift.down x)
    refine ⟨⟨ℓ'val, hmem⟩, fun h => hℓ ?_⟩
    ext x
    exact congrArg (fun f : Module.Dual ℂ X => f (ULift.up x)) h
  -- an embedding into a good product
  obtain ⟨P, j, hj, hgood⟩ := exists_good_embedding T ψ n X hX hJX
  -- the subrepresentation, transported to the lifted restriction
  let R := (Langlands.AllFieldBZ.Derivative.generalLinearRestriction T n).obj X
  let U' : Subrepresentation R.representation :=
    { toSubmodule := U.toSubmodule.comap
        (ULift.moduleEquiv : ULift.{uF} V ≃ₗ[ℂ] V).toLinearMap
      apply_mem_toSubmodule := fun g v hv => U.apply_mem_toSubmodule g hv }
  apply Subrepresentation.ext
  change U.toSubmodule = ⊥
  rw [Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  let W := SmoothRep.subrepresentation R U'
  have hWnt : Nontrivial W := by
    refine ⟨⟨⟨ULift.up v, hv⟩, 0, fun h => hv0 ?_⟩⟩
    exact congrArg (fun x : W => ULift.down (Subtype.val x)) h
  let iW : W ⟶ (Langlands.AllFieldBZ.Derivative.generalLinearRestriction T n).obj P :=
    SmoothRep.subtype R U' ≫ (Langlands.AllFieldBZ.Derivative.generalLinearRestriction T n).map j
  have hiW : Function.Injective (SmoothRep.hom iW) :=
    hj.comp (SmoothRep.subtype_injective R U')
  -- homogeneity forces nonzero full upper coinvariants
  have hWtop := (Langlands.AllFieldBZ.Derivative.hasNonzeroDerivative_of_isHomogeneous T ψ (Nat.succ_pos n) hgood.1
    (Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.level_of_good T ψ P hgood) iW hiW hWnt).1
  have hWco := (hasNonzeroDerivative_top_iff T ψ n W).1 hWtop
  let f : W ≃ₗ[ℂ] U.toSubmodule :=
    { toFun := fun x => ⟨x.val.down, x.property⟩
      invFun := fun y => ⟨ULift.up y.val, y.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E := transportEquiv W.representation U.toRepresentation
    (Mirabolic.upperUnipotent n F.Carrier) (Mirabolic.upperUnipotent n F.Carrier)
    (TopLocalization.mirabolicUpperCharacter ψ.complex n)
    ((Langlands.Whittaker.standardCharacter ψ n).comp Mirabolic.upperUnipotentEquiv.toMonoidHom)
    (MulEquiv.refl _) f (fun _ _ => rfl)
    (fun u => by rw [mirabolicUpperCharacter_eq_standardCharacter T ψ n]; rfl)
  exact (not_nontrivial_iff_subsingleton.2 hU) (@Equiv.nontrivial _ _ E.symm.toEquiv hWco)

end Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy
