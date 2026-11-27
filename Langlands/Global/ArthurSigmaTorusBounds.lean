import Langlands.LinearAlgebra.ArthurSigmaRootBounds
import Langlands.Global.ArthurSiegelNormMinimality
import Langlands.Global.AdelicPositiveTorusLogHeightBound
import Langlands.Global.AdelicNormOneRootBox

/-! # Root and height bounds on the torus in Arthur's truncated sigma region -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory NumberField
open scoped Classical CategoryTheory.MonObj NNReal

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces ArthurRelative PositiveRealTorus RepresentationGrowth

section Coordinates

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)

local notation "Δ" => simpleFinset ν hG hi
local notation "indexOf" => standardIndex hG hi ν
local notation "b₀" => ArthurRelative.base hG hi hν D
local notation "P" => rootPairing hG hi D
local notation "I" => RelativeRoot.indivisibleRoots i
local notation "σ₀" => ArthurRelative.sigma hG hi ν D

include hν in
/-- The truncated sigma bounds expressed in the original torus character space. -/
theorem relativeSigmaRootBounds (R S : Finset (characterLattice T)) (hRS : R ⊆ S) (hS : S ⊆ Δ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ H : V T, ∀ B₁ B₂ : ℝ, 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ α ∈ R, -B₁ ≤ eval T α H) →
      (∀ α ∈ R, ArthurRelative.weight hG hi ν D (R : Set (characterLattice T)) α H ≤ 0) →
      σ₀ (R : Set (characterLattice T)) S H = 1 →
      (∀ α ∈ S \ R, eval T α H ≤ B₂) →
      (∀ α ∈ S \ R, 0 < eval T α H) ∧ ∀ α ∈ Δ, |eval T α H| ≤ c * (B₁ + B₂) := by
  let := finite_indivisibleRoots hG hi
  have hRSto := standardIndex_mono hG hi ν (show (R : Set (characterLattice T)) ⊆ S from hRS)
  have hSto := standardIndex_subset_support hG hi D hν (S : Set (characterLattice T))
  obtain ⟨c, hc, hbound⟩ := ArthurCombinatorics.arthurSigmaRootBounds b₀
    (indexOf (R : Set (characterLattice T))) (indexOf (S : Set (characterLattice T))) hRSto hSto
  refine ⟨c, hc, fun H B₁ B₂ hB₁ hB₂ hlo hwt hσ hhi => ?_⟩
  let Z := toCorootSpan hG hi D H
  have hRoot (α : I) : (P).root' α Z = eval T α H := by
    have he := eval_sub_toCorootSpan hG hi D α.2.1 H
    rw [map_sub, sub_eq_zero] at he
    rw [he, eval_eq_pair]
    rfl
  have hs : ArthurCombinatorics.sigma P (b₀).support (indexOf (R : Set (characterLattice T)))
      (indexOf (S : Set (characterLattice T))) Z = 1 := by
    unfold ArthurRelative.sigma at hσ
    rwa [standardIndex_simpleRelativeRoots hG hi D hν] at hσ
  have hSub {α : I} (hα : α ∈ indexOf (S : Set (characterLattice T)) \
      indexOf (R : Set (characterLattice T))) : (α : characterLattice T) ∈ S \ R := by
    obtain ⟨hαS, hαR⟩ := Finset.mem_sdiff.mp hα
    obtain ⟨hαΔ, hαS'⟩ := (mem_standardIndex hG hi ν).mp hαS
    exact Finset.mem_sdiff.mpr ⟨hαS', fun h => hαR ((mem_standardIndex hG hi ν).mpr ⟨hαΔ, h⟩)⟩
  obtain ⟨hpositive, habs⟩ := hbound Z B₁ B₂ hB₁ hB₂
    (fun α hα => hRoot α ▸ hlo α ((mem_standardIndex hG hi ν).mp hα).2)
    (fun α hα => by
      rw [← weight_coe hG hi ν D (R : Set (characterLattice T)) α H]
      exact hwt α ((mem_standardIndex hG hi ν).mp hα).2)
    hs (fun α hα => (hRoot α).symm ▸ hhi α (hSub hα))
  refine ⟨?_, ?_⟩
  · intro α hα
    obtain ⟨hαS, hαR⟩ := Finset.mem_sdiff.mp hα
    have hαΔ := (mem_simpleFinset hG hi).mp (hS hαS)
    let α₀ : I := ⟨α, simpleRelativeRoots_subset_indivisibleRoots hG hi ν hαΔ⟩
    rw [← hRoot α₀]
    have hα₀ : α₀ ∈ indexOf (S : Set (characterLattice T)) \ indexOf (R : Set (characterLattice T)) :=
      Finset.mem_sdiff.mpr ⟨(mem_standardIndex hG hi ν).mpr ⟨hαΔ, hαS⟩,
        fun h => hαR ((mem_standardIndex hG hi ν).mp h).2⟩
    exact hpositive α₀ hα₀
  · intro α hα
    have hαΔ := (mem_simpleFinset hG hi).mp hα
    let α₀ : I := ⟨α, simpleRelativeRoots_subset_indivisibleRoots hG hi ν hαΔ⟩
    rw [← hRoot α₀]
    have hα₀ : α₀ ∈ (b₀).support := (mem_support_base hG hi hν D).mpr hαΔ
    exact habs α₀ hα₀

end Coordinates

section Torus

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  {K : Subgroup (AdelicGroupPoints F G)}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (D : RelativeRootReflectionData i) (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "Δ" => simpleFinset ν hG hi
local notation "H₀(" a ")" => height hi hK hρ (positiveTorusMap F i a)
local notation "σ₀" => ArthurRelative.sigma hG hi ν D

/-- The torus coordinates of the truncated lower Siegel region on which the
relative sigma cutoff is one, with ambient norm one imposed. -/
def sigmaTorusRegion (R S : Finset (characterLattice T)) (T₁ Tp : V T) :
    Set (intrinsicSubgroup F T) :=
  {a | a ∈ siegelChamber hi hK hρ R T₁ ∧
    (∀ α ∈ R, ArthurRelative.weight hG hi ν D (R : Set (characterLattice T)) α (H₀(a) - Tp) ≤ 0) ∧
    σ₀ (R : Set (characterLattice T)) S (H₀(a) - Tp) = 1 ∧
    positiveTorusMap F i a ∈ normOneSubgroup F G}

include hν in
/-- A uniform lower bound for the simple roots in the upper Levi, and an
exponential height bound in any nonnegative upper bound for the active roots. -/
theorem sigmaTorusRegion_bounds {N : ℕ} (ρ : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (R S : Finset (characterLattice T)) (hRS : R ⊆ S) (hS : S ⊆ Δ) (T₁ Tp : V T) :
    ∃ B C r : ℝ, 0 ≤ B ∧ 1 ≤ C ∧ 0 ≤ r ∧
      ∀ a ∈ sigmaTorusRegion hG hi D hK hρ R S T₁ Tp,
        (∀ α ∈ S, -B ≤ logNormHom F T a.val α) ∧
        ∀ Q : ℝ, 0 ≤ Q → (∀ α ∈ S \ R, logNormHom F T a.val α ≤ Q) →
          adelicHeight F G ρ (positiveTorusMap F i a) ≤ C * Real.exp (r * Q) := by
  classical
  obtain ⟨c, hc, hcoord⟩ := relativeSigmaRootBounds hG hi hν D R S hRS hS
  let B := ∑ α ∈ Δ, (|eval T α T₁| + |eval T α Tp|)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  have hT (α : characterLattice T) (hα : α ∈ Δ) :
      |eval T α T₁| + |eval T α Tp| ≤ B :=
    Finset.single_le_sum (f := fun α => |eval T α T₁| + |eval T α Tp|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hα
  have hspan := simpleRelativeRoots_restrictedCharacters_ratSpan_eq_top F G T i ν hG hi hν
  obtain ⟨C₀, r₀, hC₀, hr₀, hheight⟩ := adelicPositiveTorusLogHeightBound i ρ _
    hi.isSplitSubtorus.1 hspan hN
  let B₀ := (2 * c + 1) * B
  have hB₀ : 0 ≤ B₀ := by positivity
  let C := C₀ * Real.exp (r₀ * B₀)
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le hC₀
    (Real.one_le_exp (mul_nonneg hr₀ hB₀))
  refine ⟨B, C, r₀ * c, hB, hC, mul_nonneg hr₀ hc, ?_⟩
  intro a ha
  obtain ⟨hach, hawt, hasig, hanorm⟩ := ha
  have hlog (α : characterLattice T) : eval T α (H₀(a)) = logNormHom F T a.val α :=
    eval_height_positiveTorusMap hi hK hρ α a
  have hi₁ (α : characterLattice T) (hα : α ∈ R) : -B ≤ eval T α (H₀(a) - Tp) := by
    have h := hach α hα
    rw [map_sub] at h ⊢
    have ht := hT α (hS (hRS hα))
    linarith [neg_le_abs (eval T α T₁), le_abs_self (eval T α Tp)]
  have hi₂ {Q : ℝ} (hQ : ∀ α ∈ S \ R, logNormHom F T a.val α ≤ Q)
      (α : characterLattice T) (hα : α ∈ S \ R) : eval T α (H₀(a) - Tp) ≤ Q + B := by
    rw [map_sub, hlog]
    have ht := hT α (hS (Finset.mem_sdiff.mp hα).1)
    linarith [hQ α hα, abs_nonneg (eval T α T₁), neg_le_abs (eval T α Tp)]
  let Q₀ := ∑ α ∈ S \ R, |logNormHom F T a.val α|
  have hQ₀ : 0 ≤ Q₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hq₀ (α : characterLattice T) (hα : α ∈ S \ R) : logNormHom F T a.val α ≤ Q₀ :=
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun α => |logNormHom F T a.val α|) (fun _ _ => abs_nonneg _) hα)
  have hpos := (hcoord (H₀(a) - Tp) B (Q₀ + B) hB (add_nonneg hQ₀ hB) hi₁ hawt hasig (hi₂ hq₀)).1
  refine ⟨?_, fun Q hQ hmax => ?_⟩
  · intro α hα
    rw [← hlog]
    have ht := hT α (hS hα)
    by_cases hαR : α ∈ R
    · have h := hach α hαR
      rw [map_sub] at h
      linarith [neg_le_abs (eval T α T₁), abs_nonneg (eval T α Tp)]
    · have h := hpos α (Finset.mem_sdiff.mpr ⟨hα, hαR⟩)
      rw [map_sub] at h
      linarith [neg_le_abs (eval T α Tp), abs_nonneg (eval T α T₁)]
  · have hb := (hcoord (H₀(a) - Tp) B (Q + B) hB (add_nonneg hQ hB) hi₁ hawt hasig (hi₂ hmax)).2
    have hav : positiveTorusMap F i a = map F T.toGrp G i a.val := by
      change map F T.toGrp G (CommGroupScheme.groupHom (𝟙 T) ≫ i) a.val = _
      rw [show CommGroupScheme.groupHom (𝟙 T) = 𝟙 T.toGrp from rfl, Category.id_comp]
    rw [hav] at hanorm ⊢
    have htbound : ∀ α ∈ simpleRelativeRoots i ν ∪ Set.range (torusCharacterRestrict i),
        |logNormHom F T a.val α| ≤ B₀ + c * Q := by
      intro α hα
      rcases hα with hα | ⟨χ, rfl⟩
      · have hα' := (mem_simpleFinset hG hi).mpr hα
        have ht := hT α hα'
        have he : eval T α (H₀(a) - Tp) + eval T α Tp = eval T α (H₀(a)) := by
          rw [map_sub, sub_add_cancel]
        calc
          |logNormHom F T a.val α| = |eval T α (H₀(a) - Tp) + eval T α Tp| := by rw [he, hlog]
          _ ≤ |eval T α (H₀(a) - Tp)| + |eval T α Tp| := abs_add_le _ _
          _ ≤ c * (B + (Q + B)) + B :=
            add_le_add (hb α hα') (le_trans (le_add_of_nonneg_left (abs_nonneg _)) ht)
          _ = B₀ + c * Q := by dsimp [B₀]; ring
      · change |Real.log ((normCharacter F T (torusCharacterRestrict i χ) a.val : ℝ≥0) : ℝ)| ≤ _
        rw [normCharacter_restrict_eq_one_of_map_mem_normOne F G T i hanorm χ]
        simp only [Units.val_one, NNReal.coe_one, Real.log_one, abs_zero]
        exact add_nonneg hB₀ (mul_nonneg hc hQ)
    calc
      _ ≤ C₀ * Real.exp (r₀ * (B₀ + c * Q)) := hheight a _ (add_nonneg hB₀ (mul_nonneg hc hQ)) htbound
      _ = C * Real.exp ((r₀ * c) * Q) := by rw [mul_add, Real.exp_add, mul_assoc r₀ c, ← mul_assoc]

end Torus

end Langlands.Global.ArthurTruncation
