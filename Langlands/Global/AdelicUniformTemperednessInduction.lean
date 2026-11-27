import Langlands.Global.AdelicUniformTemperednessHeights
import Langlands.Global.AdelicUniformTemperednessDecay

/-! # The induction over standard parabolics in the uniform temperedness criterion

For a family of continuous `G(F)`-invariant functions whose constant terms satisfy torus shift
equations of order `m`, grow at most exponentially in the torus coordinates, and whose
constant-term steps have derivatives with the same growth, the constant term along every
standard parabolic is bounded at `u ϖ` by `C (2m ‖u‖ + 3)^{2m} δ_T(u)^{1/2}` on every
chamber `{u : all root coordinates ≥ -θ}`. The proof is by induction on the number of simple
roots in the index, removing one root at a time. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry NumberField Set
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints PositiveRealTorus AdelicSiegelFactors

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {𝓕 : StandardParabolicFamily F G}

local notation "A" => AdelicGroupPoints F G
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν

theorem positiveMap_id (a : intrinsicSubgroup F 𝓕.T) :
    positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T) a = torusPoint (𝓕 := 𝓕) a.val := by
  change map F 𝓕.T.toGrp G (CommGroupScheme.groupHom (𝟙 𝓕.T) ≫ 𝓕.i) a.val =
    map F 𝓕.T.toGrp G 𝓕.i a.val
  congr 2

theorem TorusFrame.norm_crd_le (Fr : TorusFrame 𝓕) [Fintype Δ]
    (u : AdelicGroupPoints F 𝓕.T.toGrp) {a b : ℝ} (ha : 0 ≤ a) (hb : ‖(Fr.crd u).2‖ ≤ b)
    (hroot : ∀ α : Δ, |(Fr.crd u).1 α| ≤ a) : ‖Fr.crd u‖ ≤ max a b :=
  norm_prod_le_iff.mpr ⟨((pi_norm_le_iff_of_nonneg ha).mpr fun α => by
    rw [Real.norm_eq_abs]; exact hroot α).trans (le_max_left _ _), hb.trans (le_max_right _ _)⟩

theorem TorusFrame.abs_root_le (Fr : TorusFrame 𝓕) [Fintype Δ]
    (u : AdelicGroupPoints F 𝓕.T.toGrp) (α : Δ) : |(Fr.crd u).1 α| ≤ ‖Fr.crd u‖ :=
  (norm_le_pi_norm (Fr.crd u).1 α).trans (norm_fst_le (Fr.crd u))

theorem TorusFrame.normCharacter_eq_exp (Fr : TorusFrame 𝓕)
    (u : AdelicGroupPoints F 𝓕.T.toGrp) (α : Δ) :
    ((normCharacter F 𝓕.T α.val u : ℝ≥0) : ℝ) = Real.exp (Fr.step α * (Fr.crd u).1 α) := by
  rw [← Fr.characterLog_root, ← log_normCharacter, Real.exp_log (normCharacter_pos u α.val)]

theorem pow_le_pow_two_mul (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ((m : ℝ) * x + 3) ^ m ≤ (2 * (m : ℝ) * x + 3) ^ (2 * m) := by
  have h1 : 1 ≤ 2 * (m : ℝ) * x + 3 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  calc ((m : ℝ) * x + 3) ^ m ≤ (2 * (m : ℝ) * x + 3) ^ m := by
        gcongr
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
    _ ≤ (2 * (m : ℝ) * x + 3) ^ (2 * m) := pow_le_pow_right₀ h1 (by omega)

section Claim

variable (Fr : TorusFrame 𝓕) {d : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)
  {Idx' : Type} (g : Idx' → ContinuousRationalFunctions F G) (S : Set Idx') (m : ℕ)
  (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "Jw" => Fin (Module.finrank ℝ W)
local notation "basisG" => Module.finBasis ℝ W
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G

/-- **The induction over standard indices.** -/
theorem constantTerm_chamber_bound [Fintype Δ]
    (hL : IsOpen (L : Set Gf))
    (hsm : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hG
      ∀ x ∈ S, ∀ c : Gf, ContMDiff IG IC ∞ (fun y : G∞ => evaluate F G (g x) (pair F G y c)))
    (hlev : ∀ x ∈ S, ∀ l ∈ L, ∀ y, evaluate F G (g x) (y * ofFinite F G l) = evaluate F G (g x) y)
    (hsh : ∀ J J' : Idx, J'.1 ⊆ J.1 → ∀ x ∈ S,
      HasTorusShiftEquations 𝓕 J.1 m (𝓕.constantTerm J' (evaluate F G (g x))))
    (hgr : ∀ Ω : Set A, IsCompact Ω → ∃ M K : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ ∀ J : Idx, ∀ x ∈ S,
      ∀ u ∈ intrinsicSubgroup F 𝓕.T, ∀ ϖ ∈ Ω,
        ‖𝓕.constantTerm J (evaluate F G (g x)) (torusPoint (𝓕 := 𝓕) u * ϖ)‖ ≤
          M * Real.exp (K * ‖Fr.crd u‖))
    (hdgr : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      ∃ K : ℝ, 0 ≤ K ∧ ∀ Ω : Set A, IsCompact Ω → ∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ (J : Idx) (α : characterLattice 𝓕.T), ∀ x ∈ S, ∀ u ∈ intrinsicSubgroup F 𝓕.T,
      ∀ k ∈ Ω, ∀ s : List Jw, s.length = n →
        ‖adelicIteratedDirectionalValue hG (s.map basisG)
          (𝓕.constantTermStep J α (evaluate F G (g x))) (torusPoint (𝓕 := 𝓕) u * k)‖ ≤
            M * Real.exp (K * ‖Fr.crd u‖)) :
    ∀ (J : Idx) (Ω : Set A), IsCompact Ω → ∀ θ : ℝ, 0 ≤ θ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ S, ∀ u ∈ intrinsicSubgroup F 𝓕.T, (∀ α : Δ, -θ ≤ (Fr.crd u).1 α) → ∀ ϖ ∈ Ω,
        ‖𝓕.constantTerm J (evaluate F G (g x)) (torusPoint (𝓕 := 𝓕) u * ϖ)‖ ≤
          C * (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) * Real.sqrt (torusModulus 𝓕 u) := by
  suffices H : ∀ n : ℕ, ∀ J : Idx, J.1.ncard = n → ∀ (Ω : Set A), IsCompact Ω → ∀ θ : ℝ,
      0 ≤ θ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ S, ∀ u ∈ intrinsicSubgroup F 𝓕.T, (∀ α : Δ, -θ ≤ (Fr.crd u).1 α) → ∀ ϖ ∈ Ω,
        ‖𝓕.constantTerm J (evaluate F G (g x)) (torusPoint (𝓕 := 𝓕) u * ϖ)‖ ≤
          C * (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) * Real.sqrt (torusModulus 𝓕 u) from
    fun J => H _ J rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro J hJn Ω hΩ θ hθ
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_torusModulus_bounds Fr
  obtain ⟨M, K, hM, hK, hgrΩ⟩ := hgr Ω hΩ
  obtain ⟨Kd, hKd, hdgrK⟩ := hdgr
  -- Case 1 constant
  set B₀ : ℝ := θ + 2 with hB₀
  set C₁ : ℝ := 3 ^ m * (Real.exp (Λ * (B₀ + θ + 1)) * (M * Real.exp (K * (B₀ + θ + 2))))
    with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  -- data for Case 2
  set stepSum : ℝ := ∑ α : Δ, Fr.step α with hstepSum
  have hstep_le : ∀ α : Δ, Fr.step α ≤ stepSum := fun α =>
    Finset.single_le_sum (f := fun α => Fr.step α) (fun α _ => (Fr.step_pos α).le)
      (Finset.mem_univ α)
  set dF : ℝ := (Module.finrank ℚ F : ℝ) with hdF
  have hdF : 0 < dF := degree_pos F
  set b : ℝ≥0ˣ := expUnit (-(stepSum * (θ + 1))) with hb
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (∑ α : Δ, (Λ + Kd + 1) * dF / Fr.step α)
  have hn₀α : ∀ α : Δ, Λ + Kd + 1 ≤ n₀ * Fr.step α / dF := by
    intro α
    have h1 : (Λ + Kd + 1) * dF / Fr.step α ≤ n₀ :=
      (Finset.single_le_sum (f := fun α => (Λ + Kd + 1) * dF / Fr.step α)
        (fun α _ => by have := Fr.step_pos α; positivity) (Finset.mem_univ α)).trans hn₀
    rw [div_le_iff₀ (Fr.step_pos α)] at h1
    rw [le_div_iff₀ hdF]
    linarith
  set Yf : Set Gf := finite F G '' Ω with hYf
  have hYfc : IsCompact Yf := hΩ.image (finite F G).continuous
  have hdecay : ∀ α : Δ, ∃ K' : Set A, IsCompact K' ∧ Ω ⊆ K' ∧ ∃ C : ℝ, 0 ≤ C ∧ _ :=
    fun α => exists_constantTermStep_decay 𝓕 hG (𝟙 𝓕.T) J α.2 L hL b n₀ Ω hΩ Yf hYfc
  choose K' hK' hΩK' Cdec hCdec hdec using hdecay
  have hMd : ∀ α : Δ, ∃ Md : ℝ, 0 ≤ Md ∧ _ := fun α => hdgrK (K' α) (hK' α) n₀
  choose Md hMd0 hMdb using hMd
  have hIH : ∀ α : Δ, α.1 ∈ J.1 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ S, ∀ u ∈ intrinsicSubgroup F 𝓕.T, (∀ α : Δ, -θ ≤ (Fr.crd u).1 α) → ∀ ϖ ∈ Ω,
        ‖𝓕.constantTerm (𝓕.removeSimpleRoot J α.1) (evaluate F G (g x)) (torusPoint (𝓕 := 𝓕) u * ϖ)‖ ≤
          C * (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) * Real.sqrt (torusModulus 𝓕 u) := by
    intro α hα
    refine ih _ ?_ _ rfl Ω hΩ θ hθ
    rw [← hJn]
    have hfin : J.1.Finite := (Set.toFinite (simpleRelativeRoots 𝓕.i 𝓕.ν)).subset J.2
    change (J.1 ∩ (Δ \ {α.1})).ncard < J.1.ncard
    have : J.1 ∩ (Δ \ {α.1}) = J.1 \ {α.1} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, J.2 h.1, h.2⟩⟩
    rw [this]
    exact Set.ncard_sdiff_singleton_lt_of_mem hα hfin
  choose C₂ hC₂0 hC₂ using hIH
  set Cα : Δ → ℝ := fun α => if h : α.1 ∈ J.1 then
    3 ^ (2 * m) * (Cdec α * Md α * Real.exp ((Λ + Kd) * (θ + 2) + n₀ * Fr.step α / dF)) +
      C₂ α h else 0 with hCα
  have hCα0 : ∀ α, 0 ≤ Cα α := by
    intro α
    simp only [hCα]
    split_ifs with h
    · have := hCdec α
      have := hMd0 α
      have := hC₂0 α h
      positivity
    · exact le_rfl
  refine ⟨C₁ + ∑ α : Δ, Cα α, add_nonneg hC₁0 (Finset.sum_nonneg fun α _ => hCα0 α), ?_⟩
  intro x hx u hu hθu ϖ hϖ
  have hsqrt0 : 0 ≤ Real.sqrt (torusModulus 𝓕 u) := Real.sqrt_nonneg _
  have hpow1 : 1 ≤ (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) :=
    one_le_pow₀ (by nlinarith [norm_nonneg (Fr.crd u), Nat.cast_nonneg (α := ℝ) m])
  have hP0 : 0 ≤ (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) := le_trans zero_le_one hpow1
  by_cases hcase : ∀ β : Δ, β.1 ∈ J.1 → (Fr.crd u).1 β ≤ B₀
  · -- Case 1: the roots in `J` are bounded
    have hJb : ∀ β : Δ, β.val ∈ J.1 → |(Fr.crd u).1 β| ≤ B₀ := by
      intro β hβ
      rw [abs_le]
      constructor <;> linarith [hθu β, hcase β hβ]
    have hmain := norm_le_of_hasTorusShiftEquations_chamber Fr hΛ0 (fun y => (hΛ y).1) J.2
      (hsh J J le_rfl x hx) hu ϖ (by positivity) hθ hJb hθu
      (B := M * Real.exp (K * (B₀ + θ + 2))) (by positivity) (by
        intro u' hu' hJ' hO' hC'
        refine (hgrΩ J x hx u' hu' ϖ hϖ).trans ?_
        gcongr
        refine (Fr.norm_crd_le u' (a := B₀ + θ + 1) (by positivity) hC' fun α => ?_).trans ?_
        · by_cases hα : α.1 ∈ J.1
          · have h1 := hJ' α hα
            have h2 := hJb α hα
            rw [abs_le] at h1 h2 ⊢
            constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
          · have := hO' α hα
            rw [abs_le]
            constructor <;> linarith [this.1, this.2]
        · exact max_le (by linarith) (by linarith))
    have hcmp := pow_le_pow_two_mul m (norm_nonneg (Fr.crd u))
    calc _ ≤ 3 ^ m * ((m : ℝ) * ‖Fr.crd u‖ + 3) ^ m * Real.sqrt (torusModulus 𝓕 u) *
          (Real.exp (Λ * (B₀ + θ + 1)) * (M * Real.exp (K * (B₀ + θ + 2)))) := hmain
      _ = C₁ * ((m : ℝ) * ‖Fr.crd u‖ + 3) ^ m * Real.sqrt (torusModulus 𝓕 u) := by
          rw [hC₁]; ring
      _ ≤ C₁ * (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) * Real.sqrt (torusModulus 𝓕 u) := by
          gcongr
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun α _ => hCα0 α)
  · -- Case 2: some root in `J` is large; remove a maximal one
    simp only [not_forall, not_le, exists_prop] at hcase
    obtain ⟨β₀, hβ₀J, hβ₀⟩ := hcase
    have hJne : (Finset.univ.filter fun β : Δ => β.1 ∈ J.1).Nonempty :=
      ⟨β₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβ₀J⟩⟩
    obtain ⟨α₀, hα₀mem, hα₀max⟩ := Finset.exists_max_image _ (fun β : Δ => (Fr.crd u).1 β) hJne
    have hα₀J : α₀.1 ∈ J.1 := (Finset.mem_filter.mp hα₀mem).2
    set ρ := (Fr.crd u).1 α₀ with hρ
    have hρB : B₀ < ρ := lt_of_lt_of_le hβ₀
      (hα₀max β₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβ₀J⟩))
    have hρ0 : 0 ≤ ρ := by linarith
    have hJb : ∀ β : Δ, β.val ∈ J.1 → |(Fr.crd u).1 β| ≤ ρ := by
      intro β hβ
      have h1 := hα₀max β (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβ⟩)
      rw [abs_le]
      constructor <;> linarith [hθu β]
    -- the step
    set step := 𝓕.constantTermStep J α₀.1 (evaluate F G (g x)) with hstepdef
    have hshift : HasTorusShiftEquations 𝓕 J.1 (m + m) step :=
      (hsh J J le_rfl x hx).sub
        (hsh J (𝓕.removeSimpleRoot J α₀.1) (Set.inter_subset_left) x hx)
    set B₂ : ℝ := Cdec α₀ * Real.exp (-(n₀ * Fr.step α₀ * (ρ - 1) / dF)) *
      (Md α₀ * Real.exp (Kd * (ρ + θ + 2))) with hB₂
    have hB₂0 : 0 ≤ B₂ := by
      have := hCdec α₀
      have := hMd0 α₀
      positivity
    have hnear : ∀ u' ∈ intrinsicSubgroup F 𝓕.T,
        (∀ β : Δ, β.val ∈ J.1 → |(Fr.crd u').1 β - (Fr.crd u).1 β| ≤ 1) →
        (∀ α : Δ, α.val ∉ J.1 → -θ - 1 ≤ (Fr.crd u').1 α ∧ (Fr.crd u').1 α ≤ 1) →
        ‖(Fr.crd u').2‖ ≤ 1 → ‖step (torusPoint (𝓕 := 𝓕) u' * ϖ)‖ ≤ B₂ := by
      intro u' hu' hJ' hO' hC'
      have hcoord : ∀ α : Δ, -θ - 1 ≤ (Fr.crd u').1 α ∧ |(Fr.crd u').1 α| ≤ ρ + θ + 1 := by
        intro α
        by_cases hα : α.1 ∈ J.1
        · have h1 := hJ' α hα
          have h2 := hJb α hα
          rw [abs_le] at h1 h2 ⊢
          refine ⟨by linarith [h1.1, hθu α], by linarith [h1.1, h1.2, h2.1, h2.2],
            by linarith [h1.1, h1.2, h2.1, h2.2]⟩
        · have := hO' α hα
          refine ⟨this.1, ?_⟩
          rw [abs_le]
          constructor <;> linarith [this.1, this.2]
      have hnorm : ‖Fr.crd u'‖ ≤ ρ + θ + 2 :=
        (Fr.norm_crd_le u' (a := ρ + θ + 1) (by positivity) hC'
          fun α => (hcoord α).2).trans (max_le (by linarith) (by linarith))
      have hα₀' : ρ - 1 ≤ (Fr.crd u').1 α₀ := by
        have := hJ' α₀ hα₀J
        rw [abs_le] at this
        linarith [this.1]
      have hchamber : (⟨u', hu'⟩ : intrinsicSubgroup F 𝓕.T) ∈
          weakSimpleRootChamber F 𝓕.T 𝓕.T (𝟙 𝓕.T) G 𝓕.i 𝓕.ν b := by
        intro α hα
        rw [Category.id_comp]
        have hval : ((normCharacter F 𝓕.T α u' : ℝ≥0) : ℝ) =
            Real.exp (Fr.step ⟨α, hα⟩ * (Fr.crd u').1 ⟨α, hα⟩) :=
          Fr.normCharacter_eq_exp u' ⟨α, hα⟩
        have hle : ((b : ℝ≥0) : ℝ) ≤ ((normCharacter F 𝓕.T α u' : ℝ≥0) : ℝ) := by
          rw [hval, hb, coe_expUnit]
          refine Real.exp_le_exp.mpr ?_
          have h1 := (hcoord ⟨α, hα⟩).1
          have h2 := hstep_le ⟨α, hα⟩
          have h3 := Fr.step_pos ⟨α, hα⟩
          nlinarith
        exact_mod_cast hle
      have hfin : finite F G (positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T) ⟨u', hu'⟩ * ϖ) ∈ Yf := by
        rw [map_mul, finite_positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T) 𝓕.isSplitTorus_T, one_mul]
        exact ⟨ϖ, hϖ, rfl⟩
      have hd := hdec α₀ (g x) (hsm x hx) (hlev x hx) ⟨u', hu'⟩ hchamber ϖ hϖ hfin
        (Md α₀ * Real.exp (Kd * ‖Fr.crd u'‖)) (by have := hMd0 α₀; positivity)
        (fun k' hk' _ s hs => by
          rw [positiveMap_id]
          exact hMdb α₀ J α₀.1 x hx u' hu' k' hk' s hs)
      rw [positiveMap_id] at hd
      refine hd.trans ?_
      have hdecay_le : relativeCharacterDecay (𝟙 𝓕.T) α₀.1 ⟨u', hu'⟩ ^ n₀ ≤
          Real.exp (-(n₀ * Fr.step α₀ * (ρ - 1) / dF)) := by
        have hrel : relativeCharacterDecay (𝟙 𝓕.T) α₀.1 ⟨u', hu'⟩ =
            Real.exp (-(Fr.step α₀ * (Fr.crd u').1 α₀) / dF) := by
          rw [relativeCharacterDecay, Category.id_comp]
          change ((normCharacter F 𝓕.T α₀.1 u' : ℝ≥0) : ℝ) ^ (-1 / dF) = _
          rw [Fr.normCharacter_eq_exp u' α₀, ← Real.exp_mul]
          congr 1
          ring
        rw [hrel, ← Real.exp_nat_mul]
        refine Real.exp_le_exp.mpr ?_
        have hs := Fr.step_pos α₀
        have h3 : (n₀ : ℝ) * Fr.step α₀ * (ρ - 1) ≤ n₀ * (Fr.step α₀ * (Fr.crd u').1 α₀) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left hα₀' (by positivity)
        have hfinal : (n₀ : ℝ) * Fr.step α₀ * (ρ - 1) / dF ≤
            n₀ * (Fr.step α₀ * (Fr.crd u').1 α₀) / dF :=
          div_le_div_of_nonneg_right h3 hdF.le
        have e1 : (n₀ : ℝ) * (-(Fr.step α₀ * (Fr.crd u').1 α₀) / dF) =
            -(n₀ * (Fr.step α₀ * (Fr.crd u').1 α₀) / dF) := by ring
        rw [e1]
        linarith
      have hexp_le : Real.exp (Kd * ‖Fr.crd u'‖) ≤ Real.exp (Kd * (ρ + θ + 2)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnorm hKd)
      rw [hB₂]
      have := hCdec α₀
      have := hMd0 α₀
      gcongr
    have hmain := norm_le_of_hasTorusShiftEquations_chamber Fr hΛ0 (fun y => (hΛ y).1) J.2
      hshift hu ϖ hρ0 hθ hJb hθu hB₂0 hnear
    have hsplit : 𝓕.constantTerm J (evaluate F G (g x)) (torusPoint (𝓕 := 𝓕) u * ϖ) =
        step (torusPoint (𝓕 := 𝓕) u * ϖ) +
          𝓕.constantTerm (𝓕.removeSimpleRoot J α₀.1) (evaluate F G (g x)) (torusPoint (𝓕 := 𝓕) u * ϖ) := by
      simp only [hstepdef, constantTermStep, Pi.sub_apply, sub_add_cancel]
    have hIHb := hC₂ α₀ hα₀J x hx u hu hθu ϖ hϖ
    -- bound the exponential factor
    have hfac : Real.exp (Λ * (ρ + θ + 1)) * B₂ ≤
        Cdec α₀ * Md α₀ * Real.exp ((Λ + Kd) * (θ + 2) + n₀ * Fr.step α₀ / dF) := by
      rw [hB₂]
      have hexp : Real.exp (Λ * (ρ + θ + 1)) * (Real.exp (-(n₀ * Fr.step α₀ * (ρ - 1) / dF)) *
          Real.exp (Kd * (ρ + θ + 2))) ≤
          Real.exp ((Λ + Kd) * (θ + 2) + n₀ * Fr.step α₀ / dF) := by
        rw [← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have h1 := hn₀α α₀
        have h2 : (n₀ : ℝ) * Fr.step α₀ * (ρ - 1) / dF =
            (n₀ * Fr.step α₀ / dF) * ρ - n₀ * Fr.step α₀ / dF := by ring
        rw [h2]
        nlinarith
      have := hCdec α₀
      have := hMd0 α₀
      have heq : Real.exp (Λ * (ρ + θ + 1)) *
            (Cdec α₀ * Real.exp (-(n₀ * Fr.step α₀ * (ρ - 1) / dF)) *
              (Md α₀ * Real.exp (Kd * (ρ + θ + 2))))
          = Cdec α₀ * Md α₀ * (Real.exp (Λ * (ρ + θ + 1)) *
              (Real.exp (-(n₀ * Fr.step α₀ * (ρ - 1) / dF)) *
                Real.exp (Kd * (ρ + θ + 2)))) := by ring
      rw [heq]
      gcongr
    have hCαα₀ : Cα α₀ = 3 ^ (2 * m) * (Cdec α₀ * Md α₀ *
        Real.exp ((Λ + Kd) * (θ + 2) + n₀ * Fr.step α₀ / dF)) + C₂ α₀ hα₀J := by
      simp only [hCα, hα₀J, dite_true]
    have hsum : Cα α₀ ≤ C₁ + ∑ α : Δ, Cα α := by
      have h1 : Cα α₀ ≤ ∑ α : Δ, Cα α :=
        Finset.single_le_sum (f := Cα) (fun α _ => hCα0 α) (Finset.mem_univ α₀)
      linarith
    rw [show m + m = 2 * m by omega] at hmain
    have hmain' : ‖step (torusPoint (𝓕 := 𝓕) u * ϖ)‖ ≤ 3 ^ (2 * m) *
        (Cdec α₀ * Md α₀ * Real.exp ((Λ + Kd) * (θ + 2) + n₀ * Fr.step α₀ / dF)) *
        (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) * Real.sqrt (torusModulus 𝓕 u) := by
      have hc : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
      rw [hc] at hmain
      calc ‖step (torusPoint (𝓕 := 𝓕) u * ϖ)‖ ≤ 3 ^ (2 * m) * (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) *
            Real.sqrt (torusModulus 𝓕 u) * (Real.exp (Λ * (ρ + θ + 1)) * B₂) := hmain
        _ ≤ 3 ^ (2 * m) * (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) *
            Real.sqrt (torusModulus 𝓕 u) *
              (Cdec α₀ * Md α₀ * Real.exp ((Λ + Kd) * (θ + 2) + n₀ * Fr.step α₀ / dF)) := by
            gcongr
        _ = _ := by ring
    rw [hsplit]
    calc _ ≤ ‖step (torusPoint (𝓕 := 𝓕) u * ϖ)‖ +
          ‖𝓕.constantTerm (𝓕.removeSimpleRoot J α₀.1) (evaluate F G (g x))
            (torusPoint (𝓕 := 𝓕) u * ϖ)‖ := norm_add_le _ _
      _ ≤ 3 ^ (2 * m) * (Cdec α₀ * Md α₀ *
            Real.exp ((Λ + Kd) * (θ + 2) + n₀ * Fr.step α₀ / dF)) *
            (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) * Real.sqrt (torusModulus 𝓕 u) +
          C₂ α₀ hα₀J * (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) *
            Real.sqrt (torusModulus 𝓕 u) := add_le_add hmain' hIHb
      _ = Cα α₀ * (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) * Real.sqrt (torusModulus 𝓕 u) := by
          rw [hCαα₀]; ring
      _ ≤ _ := by
          have := mul_nonneg hP0 hsqrt0
          rw [mul_assoc, mul_assoc (C₁ + _)]
          exact mul_le_mul_of_nonneg_right hsum this

end Claim

end Langlands.Global.StandardParabolicFamily
