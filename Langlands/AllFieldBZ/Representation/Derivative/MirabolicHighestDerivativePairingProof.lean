import Langlands.AllFieldBZ.Representation.Derivative.MirabolicHighestDerivativeDescent
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicHighestDerivativePairingStatement
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing
import Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding character_dotProduct_eq_one character_mul_eq_one coe_latticeBox coordinateCharacter coordinateCharacter_apply coordinateCharacter_eq_of_sub_mem coordinateCharacter_eq_one coordinateCharacter_zero derivativeDetection determinantNorm_eq_determinantWeight determinantNorm_levi determinantNorm_radical eq_zero_of_forall_characterAverage_eq_zero eq_zero_of_forall_mem_relations exists_coefficient_support_of_mem exists_coinvariantPairing_nondegenerate exists_forall_characterAverage_eq_zero exists_integral_character_ne_zero exists_lastRow_perturbation exists_latticeBox_fixes exists_latticeBox_subset exists_mem_latticeBox exists_mk_radicalRelations_eq exists_mulVec_eq_add exists_ne_zero_mem_additiveLattice exists_open_subgroup_coefficient exists_transferPairing_nondegenerate finite_latticeBox_quotient highestDerivativePairing_cast highestDerivativePairing_core inv_mem_additiveLattice_of_notMem isCompact_latticeBox isCompact_radicalBox isOpen_ker_coordinateCharacter isOpen_ker_phiMinusCharacter isOpen_ker_psiMinusCharacter isOpen_latticeBox ker_psiMinusQuotient latticeBox latticeBox_mono levi_inv_mem_relations mem_latticeBox mem_latticeBox_of_forall_character_eq_one mem_radicalBox mem_relations_of_transferIntegral_eq_zero mirabolicHighestDerivativePairing_of_phiMinusStep phiMinus phiMinusCharacter phiMinusCharacter_mul_mul_determinantWeight phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient phiMinus_nondegeneratePairing psiMinus psiMinusCharacter psiMinusDescendedForm psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient psiMinus_nondegeneratePairing radicalBox radicalBox_mono radicalPartMap radicalPartMap_covariance radicalPartMap_injective radicalPartMap_mk radicalPartMap_surjective radical_acts_trivially_of_phiMinus radical_acts_trivially_zero relations_one_eq_bot subsingleton_of_forall_mirabolicDerivative subsingleton_of_forall_mirabolicDerivativeOfOrder subsingleton_of_psiMinus_phiMinus subsingleton_of_psiMinus_zero subsingleton_rankCast_mirabolicDerivative_congr subsingleton_rankCast_phiMinus
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
open scoped NNReal
universe uF uV uW

section Assembly
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A rank transport of `Φ⁻ X` is `Φ⁻` of the transported `X`, so a vanishing derivative
of `X` with one more `Φ⁻` step is a vanishing derivative of `Φ⁻ X`. -/
theorem subsingleton_rankCast_phiMinus {a n' i : ℕ} (h : a = n' + i)
    (h' : a + 1 = n' + (i + 1)) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (a + 1) F.Carrier),
      Subsingleton ((mirabolicRankCast T h' ⋙ mirabolicDerivative T ψ n' (i + 1)).obj X) →
      Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n' i).obj
        ((Mirabolic.phiMinus T ψ a).obj X)) := by
  subst h
  exact fun _ hX => hX

/-- The induction on the number `j` of `Φ⁻` steps, given the `Φ⁻` pairing step. -/
theorem highestDerivativePairing_core
    (hΦ : letI := T.topology
      ∀ (m : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
        (B : SmoothRep.{0, uF, uW} ℂ (mirabolic (m + 1) F.Carrier))
        (β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (m + 1 + 1)) g.val : ℝ≥0) : ℝ) : ℂ))),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        ∃ γ : InvariantBilinear.forms ((Mirabolic.phiMinus T ψ m).obj A).representation
            ((Mirabolic.phiMinus T ψ m).obj B).representation
            (fun h => ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ)),
          ∀ v : (Mirabolic.phiMinus T ψ m).obj A,
            (∀ w : (Mirabolic.phiMinus T ψ m).obj B, γ.val v w = 0) → v = 0)
    (j : ℕ) :
    letI := T.topology
    ∀ (n : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic (n + j) F.Carrier)),
      (∀ (n' i : ℕ) (h : n + j = n' + i), n' < n →
        Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n' i).obj A)) →
      ∀ β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (n + j + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        ∃ γ : InvariantBilinear.forms ((mirabolicDerivative T ψ n j).obj A).representation
            ((mirabolicDerivative T ψ n j).obj B).representation (fun _ => (1 : ℂ)),
          ∀ v : (mirabolicDerivative T ψ n j).obj A,
            (∀ w : (mirabolicDerivative T ψ n j).obj B, γ.val v w = 0) → v = 0 := by
  let := T.topology
  induction j with
  | zero =>
    intro n A B hhigh β hβ
    have hrad : ∀ (u : radical n F.Carrier) (v : A),
        A.representation (u : mirabolic n F.Carrier) v = v := by
      cases n with
      | zero => exact radical_acts_trivially_zero T A
      | succ m =>
        refine radical_acts_trivially_of_phiMinus T ψ m A ?_
        refine subsingleton_of_forall_mirabolicDerivative T ψ m _ fun n' i h => ?_
        subst h
        exact hhigh n' (i + 1) rfl (by omega)
    obtain ⟨γ, hγ⟩ := psiMinus_nondegeneratePairing T n A B hrad β hβ
    exact ⟨γ, hγ⟩
  | succ j ih =>
    intro n A B hhigh β hβ
    obtain ⟨β', hβ'⟩ := hΦ (n + j) A B β hβ
    refine ih n ((Mirabolic.phiMinus T ψ (n + j)).obj A) ((Mirabolic.phiMinus T ψ (n + j)).obj B)
      (fun n' i h hlt => ?_) β' hβ'
    exact subsingleton_rankCast_phiMinus T ψ h (by omega) A (hhigh n' (i + 1) (by omega) hlt)

/-- The core induction, after an arbitrary rank transport `N = n + j`. -/
theorem highestDerivativePairing_cast
    (hΦ : letI := T.topology
      ∀ (m : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
        (B : SmoothRep.{0, uF, uW} ℂ (mirabolic (m + 1) F.Carrier))
        (β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (m + 1 + 1)) g.val : ℝ≥0) : ℝ) : ℂ))),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        ∃ γ : InvariantBilinear.forms ((Mirabolic.phiMinus T ψ m).obj A).representation
            ((Mirabolic.phiMinus T ψ m).obj B).representation
            (fun h => ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ)),
          ∀ v : (Mirabolic.phiMinus T ψ m).obj A,
            (∀ w : (Mirabolic.phiMinus T ψ m).obj B, γ.val v w = 0) → v = 0)
    {N n j : ℕ} (h : N = n + j) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic N F.Carrier)),
      (∀ (n' i : ℕ) (h' : N = n' + i), n' < n →
        Subsingleton ((mirabolicRankCast T h' ⋙ mirabolicDerivative T ψ n' i).obj A)) →
      ∀ β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        ∃ γ : InvariantBilinear.forms
            ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj A).representation
            ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj B).representation
            (fun _ => (1 : ℂ)),
          ∀ v : (mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj A,
            (∀ w : (mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj B,
              γ.val v w = 0) → v = 0 := by
  subst h
  exact highestDerivativePairing_core T ψ hΦ j n

end Assembly
/-- Proposition 3.8 from the `Φ⁻` pairing step for every character. -/
theorem mirabolicHighestDerivativePairing_of_phiMinusStep (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
    (hΦ : letI := T.topology
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (m : ℕ)
        (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
        (B : SmoothRep.{0, uF, uW} ℂ (mirabolic (m + 1) F.Carrier))
        (β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (m + 1 + 1)) g.val : ℝ≥0) : ℝ) : ℂ))),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        ∃ γ : InvariantBilinear.forms ((Mirabolic.phiMinus T ψ m).obj A).representation
            ((Mirabolic.phiMinus T ψ m).obj B).representation
            (fun h => ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ)),
          ∀ v : (Mirabolic.phiMinus T ψ m).obj A,
            (∀ w : (Mirabolic.phiMinus T ψ m).obj B, γ.val v w = 0) → v = 0) :
    MirabolicHighestDerivativePairingStatement.{uF, uV, uW} F T := by
  let := T.topology
  intro ψ N A B k hk _ hhigh β hβ
  refine highestDerivativePairing_cast T ψ (hΦ ψ) (Langlands.Derivative.mirabolic_rank_eq_of_order hk) A B ?_ β hβ
  intro n' i h' hlt
  have hj : 0 < i + 1 ∧ i + 1 ≤ N + 1 := by omega
  exact subsingleton_rankCast_mirabolicDerivative_congr T ψ (Langlands.Derivative.mirabolic_rank_eq_of_order hj) h'
    (by omega) (by omega) A (hhigh (i + 1) hj (by omega))

end Langlands.AllFieldBZ.Derivative.Mirabolic
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous MirabolicDerivativeDetection MirabolicHighestDerivativePairingStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicHighestDerivativePairing mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
universe uF uV uW

/-- Bernstein–Zelevinsky (1977), Proposition 3.8: the highest derivative of `A` keeps a
left-nondegenerate pairing. -/
theorem mirabolicHighestDerivativePairing (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) : MirabolicHighestDerivativePairingStatement.{uF, uV, uW} F T :=
  Mirabolic.mirabolicHighestDerivativePairing_of_phiMinusStep F T fun ψ m =>
    Mirabolic.phiMinus_nondegeneratePairing T ψ m

end Langlands.AllFieldBZ.Derivative
