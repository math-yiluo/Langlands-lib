-- MANUAL
import Langlands.AllFieldBZ.Group.GL.CompactOpen
import Langlands.AllFieldBZ.Group.GL.CountabilityProof
import Langlands.AllFieldBZ.Group.GL.UpperBruhatPivotProof
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalDerivativesStatement
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTopDerivative
import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.AllFieldBZ.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Classification.SupercuspidalDerivativesProof
import Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalDerivativesProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalDerivativesProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Classification.SupercuspidalDerivativesProof
open Langlands.Classification.SupercuspidalDerivativesProof hiding finrank_generalLinearDerivativePositive_top finrank_generalLinearDerivative_top finrank_top_of_multiplicityOne multiplicityOne_of_topologicalData
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.Derivative hiding generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero
open Langlands.AllFieldBZ.Derivative
open Langlands.Derivative.Mirabolic hiding character_dotProduct_eq_one character_mul_eq_one coe_latticeBox coordinateCharacter coordinateCharacter_apply coordinateCharacter_eq_of_sub_mem coordinateCharacter_eq_one coordinateCharacter_zero eq_zero_of_forall_characterAverage_eq_zero exists_forall_characterAverage_eq_zero exists_latticeBox_subset exists_mem_latticeBox exists_ne_zero_mem_additiveLattice finite_latticeBox_quotient inv_mem_additiveLattice_of_notMem isCompact_latticeBox isCompact_radicalBox isOpen_ker_coordinateCharacter isOpen_ker_phiMinusCharacter isOpen_ker_psiMinusCharacter isOpen_latticeBox ker_psiMinusQuotient latticeBox latticeBox_mono levi_inv_mem_relations mem_latticeBox mem_latticeBox_of_forall_character_eq_one mem_radicalBox phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient radicalBox radicalBox_mono subsingleton_of_psiMinus_phiMinus
open Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
open Langlands.Classification.SupercuspidalDerivativeVanishing hiding isSupercuspidal_rankCast iterateQuotient iterateQuotient_surjective phiMinusCharacter_eq_one psiMinusQuotient_iterateQuotient_invariant subsingleton_generalLinearDerivative subsingleton_generalLinearDerivativePositive
open Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing
open Langlands.Classification.SupercuspidalTopDerivative hiding comp_topQuotient_mem_glFunctionals generalLinearRestriction_rankCast_heq isIrreducible_rankCast nontrivial_generalLinearDerivativePositive_top nontrivial_generalLinearDerivative_top nontrivial_phiMinusIterate nontrivial_rankCast phiMinusCharacter_eq_one_of_upper phiMinusIterate_obj_succ_bottom phiMinusQuotient_eq_of_eq_radical_mul_successor phiMinus_obj_heq psiMinusQuotient_iterateQuotient_upper psiMinusQuotient_zero_injective topQuotient topQuotient_surjective
open Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative
universe uF uV

variable {F : LocalFieldPackage.{uF}}

/-- Whittaker multiplicity one for `A` makes a nonzero top derivative one-dimensional. -/
theorem finrank_top_of_multiplicityOne (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier),
      (∀ ℓ₁ ℓ₂ : Whittaker.glFunctionals ψ (0 + n) A.representation, ℓ₁.val ≠ 0 →
        ∃! c : ℂ, ℓ₂ = c • ℓ₁) →
      Nontrivial ((Langlands.AllFieldBZ.Derivative.generalLinearDerivativePositive T ψ 0 n).obj A) →
        Module.finrank ℂ ((Langlands.AllFieldBZ.Derivative.generalLinearDerivativePositive T ψ 0 n).obj A) = 1 := by
  let _ := T.topology
  intro A hM hD
  obtain ⟨x, hx⟩ := exists_ne (0 : (Langlands.AllFieldBZ.Derivative.generalLinearDerivativePositive T ψ 0 n).obj A)
  obtain ⟨f₀, hf₀⟩ := not_forall.mp (mt (Module.forall_dual_apply_eq_zero_iff ℂ x).mp hx)
  have hsurj := Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.topQuotient_surjective T ψ n A
  refine finrank_eq_one_of_dual f₀ (fun h => hf₀ (by rw [h]; rfl)) fun f => ?_
  let ℓ₀ : Whittaker.glFunctionals ψ (0 + n) A.representation :=
    ⟨f₀ ∘ₗ Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.topQuotient T ψ n A, Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.comp_topQuotient_mem_glFunctionals T ψ n A f₀⟩
  let ℓ : Whittaker.glFunctionals ψ (0 + n) A.representation :=
    ⟨f ∘ₗ Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.topQuotient T ψ n A, Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.comp_topQuotient_mem_glFunctionals T ψ n A f⟩
  have hℓ₀ : ℓ₀.val ≠ 0 := by
    intro h0
    obtain ⟨y, rfl⟩ := hsurj x
    exact hf₀ (LinearMap.congr_fun h0 y)
  obtain ⟨c, hc, -⟩ := hM ℓ₀ ℓ hℓ₀
  refine ⟨c, LinearMap.ext fun z => ?_⟩
  obtain ⟨y, rfl⟩ := hsurj z
  exact LinearMap.congr_fun (congrArg Subtype.val hc) y

/-- The published Whittaker multiplicity one, stated for the canonical normed topology,
holds for `T.topology`. -/
theorem multiplicityOne_of_topologicalData (T : F.TopologicalData) :
    letI := T.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
      IsAdmissible π → Representation.IsIrreducible π →
      ∀ ℓ₁ ℓ₂ : Whittaker.glFunctionals ψ n π, ℓ₁.val ≠ 0 →
        ∃! c : ℂ, ℓ₂ = c • ℓ₁ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact Langlands.Whittaker.localFieldMultiplicityOne.{uF, uV} F.Carrier

/-- The top derivative `GL_(0+n+1) → GL_0` of an irreducible supercuspidal representation
is one-dimensional. -/
theorem finrank_generalLinearDerivativePositive_top (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier),
      A.IsIrreducible → IsSupercuspidal A.representation →
        Module.finrank ℂ ((Langlands.AllFieldBZ.Derivative.generalLinearDerivativePositive T ψ 0 n).obj A) = 1 := by
  let _ := T.topology
  intro A hirr hsc
  exact finrank_top_of_multiplicityOne T ψ n A
    (multiplicityOne_of_topologicalData T (0 + n) A ψ A.representation hsc.1 hirr)
    (Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.nontrivial_generalLinearDerivativePositive_top T ψ n A hsc
      (nontrivial_of_isIrreducible A.representation hirr))

/-- BZ77 §4.4, top derivative: the derivative of order `n + 1` of an irreducible
supercuspidal representation of `GL_(n+1)` is one-dimensional. -/
theorem finrank_generalLinearDerivative_top (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      A.IsIrreducible → IsSupercuspidal A.representation →
        Module.finrank ℂ ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj A) = 1 := by
  let _ := T.topology
  intro A hirr hsc
  have key : ∀ (m : ℕ) (hm : m = 0) (h : n + 1 = m + n + 1),
      Module.finrank ℂ ((Langlands.AllFieldBZ.Derivative.generalLinearDerivativePositive T ψ m n).obj
        ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h).obj A)) = 1 := by
    intro m hm h
    subst hm
    exact finrank_generalLinearDerivativePositive_top T ψ n _
      (Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.isIrreducible_rankCast T h A hirr) (Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.isSupercuspidal_rankCast T h A hsc)
  exact key (n + 1 - (n + 1)) (Nat.sub_self _) (rank_eq_of_succ_le le_rfl)

end Langlands.AllFieldBZ.Classification.SupercuspidalDerivativesProof
namespace Langlands.AllFieldBZ.Classification
open Langlands.Classification hiding SupercuspidalDerivatives supercuspidalDerivatives
universe uF uW

/-- BZ77 §4.4: an irreducible supercuspidal representation of `GL_(n+1)` has vanishing
derivatives of every order strictly between `0` and `n + 1`, and a one-dimensional top
derivative. -/
theorem supercuspidalDerivatives (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    SupercuspidalDerivatives.{uF, uW} F T := by
  let _ := T.topology
  intro ψ n A hirr hsc
  refine ⟨fun k hk hpos hlt => ?_, ?_⟩
  · exact SupercuspidalDerivativeVanishing.subsingleton_generalLinearDerivative T ψ (n + 1) k hk
      hpos hlt A hsc
  · exact SupercuspidalDerivativesProof.finrank_generalLinearDerivative_top T ψ n A hirr hsc

end Langlands.AllFieldBZ.Classification
