import Langlands.AllFieldBZ.Representation.Derivative.MirabolicHighestDerivativeDescent
import Langlands.AllFieldBZ.Representation.Derivative.MixedProductDerivativeStatement
import Langlands.Representation.Derivative.RightMixedProductPhiMinusDetectionProof

/-!
# All-field port of `Langlands.Representation.Derivative.RightMixedProductPhiMinusDetectionProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.RightMixedProductPhiMinusDetectionProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing MirabolicDerivativeDetection RightMixedProductPhiMinusDetection generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero rightMixedProductPhiMinusDetection
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedProduct
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV

private theorem _root_.Langlands.Derivative.radicalElement_mul_last {R : Type*} [CommRing R] {n : ℕ}
    (c : Fin n → R) (g : mirabolic n R) (i : Fin n) :
    ((radicalElement c : mirabolic n R) * g).val.val i.castSucc (Fin.last n) =
      g.val.val i.castSucc (Fin.last n) + c i := by
  change ((radicalElement c).val.val.val * g.val.val) _ _ = _
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, g.property (Fin.last n)]

private theorem _root_.Langlands.Derivative.inverse_entry_of_same_right_coset {R : Type*} [CommRing R]
    (k r : ℕ) (c : Fin ((k + 1) + r) → R) (g : mirabolic ((k + 1) + r) R)
    (hq : Induction.quotientMap (rightSubgroup (k + 1) r R) g =
      Induction.quotientMap (rightSubgroup (k + 1) r R)
        ((radicalElement c : mirabolic ((k + 1) + r) R)⁻¹)) :
    (g⁻¹).val.val (rightIndex (k + 1) r (Sum.inr 0)) (Fin.last ((k + 1) + r)) =
      c ⟨r, by omega⟩ := by
  let v : mirabolic ((k + 1) + r) R := radicalElement c
  have hh : g * v ∈ rightSubgroup (k + 1) r R := by
    have h := QuotientGroup.rightRel_apply.mp (Quotient.exact hq.symm)
    simpa [v] using h
  let h : rightSubgroup (k + 1) r R := ⟨g * v, hh⟩
  have hg : g⁻¹ = v * (h : mirabolic ((k + 1) + r) R)⁻¹ := by
    simp [h]
  rw [hg]
  have hi : rightIndex (k + 1) r (Sum.inr 0) =
      (⟨r, by omega⟩ : Fin ((k + 1) + r)).castSucc := by
    apply Fin.ext
    simp
  rw [hi, radicalElement_mul_last]
  have hz := (mem_rightSubgroup_iff_entry (h⁻¹).val).mp (h⁻¹).property 0 (Fin.last r)
  change ((h : mirabolic ((k + 1) + r) R)⁻¹).val.val
    (rightIndex (k + 1) r (Sum.inr 0)) (rightIndex (k + 1) r (Sum.inl (Fin.last r))) = 0 at hz
  rw [rightIndex_last, hi] at hz
  rw [hz, zero_add]

private theorem _root_.Langlands.Derivative.not_isCompact_field (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    letI := T.topology
    ¬ IsCompact (Set.univ : Set F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have : Infinite F.Carrier := T.infinite
  intro hc
  let : CompactSpace F.Carrier := isCompact_univ_iff.mp hc
  have : Finite F.Carrier := DivisionRing.finite_of_compactSpace_of_t2Space
  exact not_finite F.Carrier

private theorem _root_.Langlands.Derivative.radical_triviality_rankCast {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {a m : ℕ} (h : a = m + 1) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier),
      Subsingleton ((Mirabolic.phiMinus T ψ m).obj ((mirabolicRankCast T h).obj X)) →
      ∀ (u : radical a F.Carrier) (v : X),
        X.representation (u : mirabolic a F.Carrier) v = v := by
  subst a
  exact Mirabolic.radical_acts_trivially_of_phiMinus T ψ m

private theorem _root_.Langlands.Derivative.eval_one_eq_zero_of_radical_invariant {F : LocalFieldPackage.{uF}} (T : F.TopologicalData) (k r : ℕ) :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
      (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
      (f : (T.rightMixedProductFunctor (k + 1) r).obj (B, A)),
      (∀ u : radical ((k + 1) + r) F.Carrier,
        T.rightMixedEval (B, A) f (u : mirabolic ((k + 1) + r) F.Carrier)⁻¹ =
          T.rightMixedEval (B, A) f 1) →
      T.rightMixedEval (B, A) f 1 = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have := T.generalLinearTopologicalGroup ((k + 1) + r + 1)
  have := T.generalLinearLocallyCompactSpace ((k + 1) + r + 1)
  have := GeneralLinear.Mirabolic.locallyCompactSpace
    (F := F.Carrier) (n := (k + 1) + r)
  intro B A f hfix
  by_contra hne
  obtain ⟨C, hC, hqC⟩ := QuotientIntegration.leftQuotient_exists_isCompact_image
    (rightSubgroup (k + 1) r F.Carrier) rightSubgroup_isClosed
    (T.rightMixedEval_isCompact_quotientSupport (B, A) f)
  let entryInv : mirabolic ((k + 1) + r) F.Carrier → F.Carrier := fun g =>
    (g⁻¹).val.val (rightIndex (k + 1) r (Sum.inr 0)) (Fin.last ((k + 1) + r))
  have hentry : Continuous entryInv :=
    (GeneralLinear.Mirabolic.entry _ _).continuous.comp continuous_inv
  have hall : entryInv '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    let c : Fin ((k + 1) + r) → F.Carrier := fun _ => t
    have hs : Induction.quotientMap (rightSubgroup (k + 1) r F.Carrier)
        ((radicalElement c : mirabolic ((k + 1) + r) F.Carrier)⁻¹) ∈
        Induction.quotientSupport (rightSubgroup (k + 1) r F.Carrier)
          (T.rightMixedEval (B, A) f) := by
      refine ⟨_, ?_, rfl⟩
      change T.rightMixedEval (B, A) f _ ≠ 0
      rw [hfix]
      exact hne
    rw [← hqC] at hs
    obtain ⟨g, hg, hqg⟩ := hs
    exact ⟨g, hg, inverse_entry_of_same_right_coset k r c g hqg⟩
  exact not_isCompact_field F T (hall ▸ hC.image hentry)

/-- BZ77 4.13(d): every nonzero invariant subspace of a right mixed product with
positive general linear rank has nonzero normalized `Φ⁻`. -/
theorem rightMixedProductPhiMinusDetection (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    RightMixedProductPhiMinusDetection.{uF, uV} F T := by
  let := T.topology
  classical
  intro ψ k r B A U hU
  by_contra hn
  have hs := not_nontrivial_iff_subsingleton.mp hn
  have hrad := radical_triviality_rankCast T ψ (Nat.add_right_comm k 1 r)
    (SmoothRep.subrepresentation _ U) hs
  apply hU
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · intro f hf
    change f = 0
    apply T.rightMixedEval_injective (B, A)
    funext x
    change T.rightMixedEval (B, A) f x = 0
    let v : U := U.toRepresentation x ⟨f, hf⟩
    have hvfix : ∀ u : radical ((k + 1) + r) F.Carrier,
        T.rightMixedEval (B, A) (v : (T.rightMixedProductFunctor (k + 1) r).obj (B, A))
            (u : mirabolic ((k + 1) + r) F.Carrier)⁻¹ =
          T.rightMixedEval (B, A) v.val 1 := by
      intro u
      have h := congrArg
        (fun w : U => T.rightMixedEval (B, A) w.val 1) (hrad (u⁻¹) v)
      change T.rightMixedEval (B, A) v.val
        (1 * (u : mirabolic ((k + 1) + r) F.Carrier)⁻¹) =
          T.rightMixedEval (B, A) v.val 1 at h
      simpa only [one_mul] using h
    have hv0 := eval_one_eq_zero_of_radical_invariant T k r B A v.val hvfix
    change T.rightMixedEval (B, A) f (1 * x) = 0 at hv0
    simpa only [one_mul] using hv0
  · exact bot_le

end Langlands.AllFieldBZ.Derivative
