import Langlands.AllFieldBZ.Representation.Derivative.MirabolicDerivativeDetectionProof
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicMinusExactnessStatement
import Langlands.Representation.Derivative.LevelCalculus

/-!
# All-field port of `Langlands.Representation.Derivative.LevelCalculus`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LevelCalculus` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous MirabolicDerivativeDetection generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV

variable {F : LocalFieldPackage.{uF}}

namespace LevelCalculus
open Langlands.Derivative.LevelCalculus hiding hasNonzeroDerivative_iff_of_iso hasNonzeroDerivative_level hasNonzeroDerivative_of_injective hasNonzeroDerivative_succ_iff hasNonzeroDerivative_succ_iff_cast isHomogeneous_of_forall_injective isHomogeneous_of_iso level_eq_level_phiMinus_succ level_eq_of_isHomogeneous level_eq_of_iso level_le_level_phiMinus_succ level_le_max_of_isShortExact level_le_of_imp level_le_of_injective level_le_one_of_subsingleton_phiMinus level_mirabolicRankCast level_pos mapsShortExact_mirabolicDerivative mapsShortExact_mirabolicDerivativeOfOrder mapsShortExact_mirabolicRankCast mapsShortExact_phiMinusIterate mirabolicDerivative_succ_cast_obj nontrivial_mirabolicDerivative_cast_congr nontrivial_of_hasNonzeroDerivative nontrivial_phiMinus_iff
/-! ## Maps of smooth representations -/

section Maps
variable {G : Type*} [Group G] [TopologicalSpace G]

end Maps
/-! ## Exact functors -/

section Exact
variable {G : Type*} [Group G] [TopologicalSpace G] {H : Type*} [Group H] [TopologicalSpace H]
  {K : Type*} [Group K] [TopologicalSpace K]

open Langlands.Derivative.Mirabolic hiding MinusExactnessStatement character_dotProduct_eq_one character_mul_eq_one coe_latticeBox coordinateCharacter coordinateCharacter_apply coordinateCharacter_eq_of_sub_mem coordinateCharacter_eq_one coordinateCharacter_zero derivativeDetection eq_zero_of_forall_characterAverage_eq_zero exists_forall_characterAverage_eq_zero exists_latticeBox_subset exists_mem_latticeBox exists_ne_zero_mem_additiveLattice finite_latticeBox_quotient inv_mem_additiveLattice_of_notMem isCompact_latticeBox isCompact_radicalBox isOpen_ker_coordinateCharacter isOpen_ker_phiMinusCharacter isOpen_ker_psiMinusCharacter isOpen_latticeBox ker_psiMinusQuotient latticeBox latticeBox_mono levi_inv_mem_relations mem_latticeBox mem_latticeBox_of_forall_character_eq_one mem_radicalBox phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient radicalBox radicalBox_mono radical_acts_trivially_zero relations_one_eq_bot subsingleton_of_forall_mirabolicDerivative subsingleton_of_forall_mirabolicDerivativeOfOrder subsingleton_of_psiMinus_phiMinus subsingleton_of_psiMinus_zero subsingleton_rankCast_mirabolicDerivative_congr
open Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.GeneralLinear.Mirabolic
end Exact
/-! ## Exactness of the derivative functors -/

section DerivativeExact
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

open Langlands.Derivative.Mirabolic hiding MinusExactnessStatement character_dotProduct_eq_one character_mul_eq_one coe_latticeBox coordinateCharacter coordinateCharacter_apply coordinateCharacter_eq_of_sub_mem coordinateCharacter_eq_one coordinateCharacter_zero derivativeDetection eq_zero_of_forall_characterAverage_eq_zero exists_forall_characterAverage_eq_zero exists_latticeBox_subset exists_mem_latticeBox exists_ne_zero_mem_additiveLattice finite_latticeBox_quotient inv_mem_additiveLattice_of_notMem isCompact_latticeBox isCompact_radicalBox isOpen_ker_coordinateCharacter isOpen_ker_phiMinusCharacter isOpen_ker_psiMinusCharacter isOpen_latticeBox ker_psiMinusQuotient latticeBox latticeBox_mono levi_inv_mem_relations mem_latticeBox mem_latticeBox_of_forall_character_eq_one mem_radicalBox phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient radicalBox radicalBox_mono radical_acts_trivially_zero relations_one_eq_bot subsingleton_of_forall_mirabolicDerivative subsingleton_of_forall_mirabolicDerivativeOfOrder subsingleton_of_psiMinus_phiMinus subsingleton_of_psiMinus_zero subsingleton_rankCast_mirabolicDerivative_congr
open Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.GeneralLinear.Mirabolic
theorem mapsShortExact_mirabolicRankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    MapsShortExactIntertwiners (mirabolicRankCast.{uF, uV} T h) := by
  let _ := T.topology
  subst h
  exact mapsShortExact_id

theorem mapsShortExact_phiMinusIterate (hE : Langlands.AllFieldBZ.Derivative.Mirabolic.MinusExactnessStatement.{uF, uV} F T) (n : ℕ) :
    ∀ k : ℕ, letI := T.topology
      MapsShortExactIntertwiners (phiMinusIterate.{uF, uV} T ψ n k) := by
  let _ := T.topology
  intro k
  induction k with
  | zero => exact mapsShortExact_id
  | succ k ih => exact mapsShortExact_comp (hE.2.2.2 (n + k) ψ) ih

theorem mapsShortExact_mirabolicDerivative (hE : Langlands.AllFieldBZ.Derivative.Mirabolic.MinusExactnessStatement.{uF, uV} F T)
    (n k : ℕ) :
    letI := T.topology
    MapsShortExactIntertwiners (mirabolicDerivative.{uF, uV} T ψ n k) := by
  let _ := T.topology
  exact mapsShortExact_comp (mapsShortExact_phiMinusIterate T ψ hE n k) (hE.2.2.1 n)

theorem mapsShortExact_mirabolicDerivativeOfOrder (hE : Langlands.AllFieldBZ.Derivative.Mirabolic.MinusExactnessStatement.{uF, uV} F T)
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    MapsShortExactIntertwiners (mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk) := by
  let _ := T.topology
  exact mapsShortExact_comp (mapsShortExact_mirabolicRankCast T _)
    (mapsShortExact_mirabolicDerivative T ψ hE _ _)

end DerivativeExact
/-! ## Level -/

section Level
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem hasNonzeroDerivative_level {N : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      level T ψ A ≠ 0 → HasNonzeroDerivative T ψ A (level T ψ A) := by
  intro A
  classical
  change Nat.findGreatest (HasNonzeroDerivative T ψ A) (N + 1) ≠ 0 →
    HasNonzeroDerivative T ψ A (Nat.findGreatest (HasNonzeroDerivative T ψ A) (N + 1))
  exact fun h => Nat.findGreatest_of_ne_zero rfl h

theorem level_le_of_imp {N : ℕ} :
    letI := T.topology
    ∀ A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      (∀ k, HasNonzeroDerivative T ψ A k → HasNonzeroDerivative T ψ B k) →
        level T ψ A ≤ level T ψ B := by
  intro A B h
  by_cases h0 : level T ψ A = 0
  · rw [h0]
    exact Nat.zero_le _
  · exact le_level_of_hasNonzeroDerivative T ψ B (h _ (hasNonzeroDerivative_level T ψ A h0))

theorem hasNonzeroDerivative_iff_of_iso {N : ℕ} :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (_ : A ≅ B) (k : ℕ),
      HasNonzeroDerivative T ψ A k ↔ HasNonzeroDerivative T ψ B k := by
  let _ := T.topology
  intro A B e k
  exact ⟨fun ⟨hk, h⟩ =>
      ⟨hk, (nontrivial_iff_of_iso ((mirabolicDerivativeOfOrder T ψ N k hk).mapIso e)).mp h⟩,
    fun ⟨hk, h⟩ =>
      ⟨hk, (nontrivial_iff_of_iso ((mirabolicDerivativeOfOrder T ψ N k hk).mapIso e)).mpr h⟩⟩

theorem level_eq_of_iso {N : ℕ} :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (_ : A ≅ B),
      level T ψ A = level T ψ B := by
  let _ := T.topology
  intro A B e
  exact le_antisymm (level_le_of_imp T ψ A B fun k => (hasNonzeroDerivative_iff_of_iso T ψ e k).mp)
    (level_le_of_imp T ψ B A fun k => (hasNonzeroDerivative_iff_of_iso T ψ e k).mpr)

theorem level_mirabolicRankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier),
      level T ψ ((mirabolicRankCast T h).obj A) = level T ψ A := by
  subst h
  intro A
  rfl

theorem nontrivial_of_hasNonzeroDerivative {N k : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      HasNonzeroDerivative T ψ A k → Nontrivial A := by
  let _ := T.topology
  rintro A ⟨hk, h⟩
  by_contra hA
  rw [not_nontrivial_iff_subsingleton] at hA
  have := mirabolicDerivativeOfOrder_obj_subsingleton T ψ N k hk A hA
  exact not_subsingleton _ this

/-- The published detection theorem, in the form used below. -/
theorem level_pos {N : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) [Nontrivial A], 0 < level T ψ A :=
  fun A hA => mirabolicDerivativeDetection.{uF, uV} F T ψ N A hA

/-! ### Injections and short exact sequences, under exactness -/

variable (hE : Mirabolic.MinusExactnessStatement.{uF, uV} F T)
include hE

theorem hasNonzeroDerivative_of_injective {N : ℕ} :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (f : A ⟶ B),
      Function.Injective (SmoothRep.hom f) →
        ∀ k, HasNonzeroDerivative T ψ A k → HasNonzeroDerivative T ψ B k := by
  let _ := T.topology
  rintro A B f hf k ⟨hk, h⟩
  refine ⟨hk, ?_⟩
  exact (map_injective_of_exact (mapsShortExact_mirabolicDerivativeOfOrder T ψ hE N k hk) f
    hf).nontrivial

theorem level_le_of_injective {N : ℕ} :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (f : A ⟶ B),
      Function.Injective (SmoothRep.hom f) → level T ψ A ≤ level T ψ B :=
  fun f hf => level_le_of_imp T ψ _ _ (hasNonzeroDerivative_of_injective T ψ hE f hf)

theorem level_le_max_of_isShortExact {N : ℕ} :
    letI := T.topology
    ∀ {A B C : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} {i : A ⟶ B} {q : B ⟶ C},
      IsShortExact i q → level T ψ B ≤ max (level T ψ A) (level T ψ C) := by
  let _ := T.topology
  intro A B C i q h
  by_cases h0 : level T ψ B = 0
  · rw [h0]
    exact Nat.zero_le _
  obtain ⟨hk, hn⟩ := hasNonzeroDerivative_level T ψ B h0
  have hJ := isShortExact_map (mapsShortExact_mirabolicDerivativeOfOrder T ψ hE N _ hk) h
  by_contra hlt
  rw [not_le, max_lt_iff] at hlt
  have hA : Subsingleton ((mirabolicDerivativeOfOrder T ψ N _ hk).obj A) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hA
    have := le_level_of_hasNonzeroDerivative T ψ A ⟨hk, hA⟩
    omega
  have hC : Subsingleton ((mirabolicDerivativeOfOrder T ψ N _ hk).obj C) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hC
    have := le_level_of_hasNonzeroDerivative T ψ C ⟨hk, hC⟩
    omega
  exact not_subsingleton _ (subsingleton_of_isShortExact hJ)

end Level
/-! ## One `Φ⁻` step shifts derivative orders by one -/

section Shift
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem nontrivial_mirabolicDerivative_cast_congr {N n n' j j' : ℕ} (hn : n = n') (hj : j = j')
    (h : N = n + j) (h' : N = n' + j') :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      Nontrivial ((mirabolicDerivative T ψ n j).obj ((mirabolicRankCast T h).obj A)) ↔
        Nontrivial ((mirabolicDerivative T ψ n' j').obj ((mirabolicRankCast T h').obj A)) := by
  subst hn hj
  intro A
  rfl

/-- The order-`(j+1)` derivative, read through any decomposition `N = n + j`. -/
theorem hasNonzeroDerivative_succ_iff_cast {N n j : ℕ} (h : N = n + j) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      HasNonzeroDerivative T ψ A (j + 1) ↔
        Nontrivial ((mirabolicDerivative T ψ n j).obj ((mirabolicRankCast T h).obj A)) := by
  intro A
  constructor
  · rintro ⟨hk, hA⟩
    exact (nontrivial_mirabolicDerivative_cast_congr T ψ (by omega) (by omega) _ h A).mp hA
  · intro hA
    exact ⟨⟨by omega, by omega⟩,
      (nontrivial_mirabolicDerivative_cast_congr T ψ (by omega) (by omega) h _ A).mp hA⟩

theorem mirabolicDerivative_succ_cast_obj {M n j : ℕ} (h : M + 1 = n + (j + 1))
    (h' : M = n + j) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      (mirabolicDerivative T ψ n (j + 1)).obj ((mirabolicRankCast T h).obj A) =
        (mirabolicDerivative T ψ n j).obj
          ((mirabolicRankCast T h').obj ((Mirabolic.phiMinus T ψ M).obj A)) := by
  subst h'
  intro A
  rfl

/-- One `Φ⁻` step lowers every positive derivative order by one. -/
theorem hasNonzeroDerivative_succ_iff {M : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier)) {k : ℕ}, 0 < k →
      (HasNonzeroDerivative T ψ A (k + 1) ↔
        HasNonzeroDerivative T ψ ((Mirabolic.phiMinus T ψ M).obj A) k) := by
  intro A k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  by_cases hj : j ≤ M
  · obtain ⟨n, hn⟩ : ∃ n, M = n + j := ⟨M - j, by omega⟩
    have h : M + 1 = n + (j + 1) := by omega
    rw [hasNonzeroDerivative_succ_iff_cast T ψ h, mirabolicDerivative_succ_cast_obj T ψ h hn,
      ← hasNonzeroDerivative_succ_iff_cast T ψ hn]
  · constructor
    · rintro ⟨hk, -⟩
      omega
    · rintro ⟨hk, -⟩
      omega

theorem level_le_level_phiMinus_succ {M : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      level T ψ A ≤ level T ψ ((Mirabolic.phiMinus T ψ M).obj A) + 1 := by
  intro A
  by_cases h0 : level T ψ A ≤ 1
  · omega
  have hA := hasNonzeroDerivative_level T ψ A (by omega)
  obtain ⟨k, hk⟩ : ∃ k, level T ψ A = k + 1 := ⟨level T ψ A - 1, by omega⟩
  rw [hk] at hA ⊢
  have := le_level_of_hasNonzeroDerivative T ψ _
    ((hasNonzeroDerivative_succ_iff T ψ A (by omega)).mp hA)
  omega

/-- If `Φ⁻ A` has a positive level, `A` has exactly one more. -/
theorem level_eq_level_phiMinus_succ {M : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      0 < level T ψ ((Mirabolic.phiMinus T ψ M).obj A) →
        level T ψ A = level T ψ ((Mirabolic.phiMinus T ψ M).obj A) + 1 := by
  intro A hpos
  apply le_antisymm (level_le_level_phiMinus_succ T ψ A)
  apply le_level_of_hasNonzeroDerivative T ψ A
  exact (hasNonzeroDerivative_succ_iff T ψ A hpos).mpr
    (hasNonzeroDerivative_level T ψ _ hpos.ne')

theorem level_le_one_of_subsingleton_phiMinus {M : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      Subsingleton ((Mirabolic.phiMinus T ψ M).obj A) → level T ψ A ≤ 1 := by
  intro A hA
  have := level_le_level_phiMinus_succ T ψ A
  rw [level_eq_zero_of_subsingleton T ψ _ hA] at this
  exact this

/-- With detection, `Φ⁻ A ≠ 0` exactly when `A` has level at least two. -/
theorem nontrivial_phiMinus_iff {M : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      Nontrivial ((Mirabolic.phiMinus T ψ M).obj A) ↔ 1 < level T ψ A := by
  intro A
  constructor
  · intro hA
    rw [level_eq_level_phiMinus_succ T ψ A (level_pos T ψ _)]
    have := level_pos T ψ ((Mirabolic.phiMinus T ψ M).obj A)
    omega
  · intro hA
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have := level_le_one_of_subsingleton_phiMinus T ψ A hn
    omega

end Shift
/-! ## Homogeneity through injective intertwiners -/

section Homogeneous
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem level_eq_of_isHomogeneous {N : ℕ} :
    letI := T.topology
    ∀ {W X : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)}, IsHomogeneous T ψ X →
      ∀ (f : W ⟶ X), Function.Injective (SmoothRep.hom f) → Nontrivial W →
        level T ψ W = level T ψ X := by
  let _ := T.topology
  intro W X hX f hf hW
  rw [level_eq_of_iso T ψ (isoRange f hf)]
  exact hX _ (range_ne_bot f hf)

theorem isHomogeneous_of_forall_injective {N : ℕ} :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) (c : ℕ),
      (∀ (W : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) (f : W ⟶ X),
        Function.Injective (SmoothRep.hom f) → Nontrivial W → level T ψ W = c) →
      IsHomogeneous T ψ X := by
  let _ := T.topology
  intro X c h
  by_cases hX : Nontrivial X
  · have hc : level T ψ X = c := h X (𝟙 X) (fun _ _ hxy => hxy) hX
    intro U hU
    rw [hc]
    exact h _ (SmoothRep.subtype X U) (SmoothRep.subtype_injective X U)
      (subrepresentation_nontrivial U hU)
  · rw [not_nontrivial_iff_subsingleton] at hX
    exact isHomogeneous_of_subsingleton T ψ X hX

theorem isHomogeneous_of_iso {N : ℕ} :
    letI := T.topology
    ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (_ : X ≅ Y),
      IsHomogeneous T ψ X → IsHomogeneous T ψ Y := by
  let _ := T.topology
  intro X Y e hX
  apply isHomogeneous_of_forall_injective T ψ Y (level T ψ X)
  intro W f hf hW
  exact level_eq_of_isHomogeneous T ψ hX (f ≫ e.inv)
    ((iso_hom_injective e.symm).comp hf) hW

end Homogeneous
end LevelCalculus
end Langlands.AllFieldBZ.Derivative
