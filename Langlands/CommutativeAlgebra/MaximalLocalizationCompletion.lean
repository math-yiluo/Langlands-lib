import Langlands.CommutativeAlgebra.SquareSurjectivePowers
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Tactic.LinearCombination

/-! # The completion of a ring at a maximal ideal and maps to complete local rings -/

universe u v

open IsLocalRing

namespace Langlands.CommutativeAlgebra.MaximalLocalizationCompletion

section Localization

variable {S : Type u} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal]

/-- Elements outside a maximal ideal are invertible modulo each of its powers. -/
theorem exists_mul_sub_one_mem_pow {w : S} (hw : w ∉ 𝔪) (n : ℕ) :
    ∃ w' : S, w * w' - 1 ∈ 𝔪 ^ n := by
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv ‹_› hw
  refine ⟨y * ∑ k ∈ Finset.range n, i ^ k, ?_⟩
  have hg := geom_sum_mul i n
  have : w * (y * ∑ k ∈ Finset.range n, i ^ k) - 1 = -(i ^ n) := by
    linear_combination (∑ k ∈ Finset.range n, i ^ k) * hyi - hg
  rw [this]
  exact neg_mem (Ideal.pow_mem_pow hi n)

/-- A power of a maximal ideal is saturated with respect to its complement. -/
theorem mem_pow_of_mul_mem_pow {w s : S} (hw : w ∉ 𝔪) {n : ℕ} (h : w * s ∈ 𝔪 ^ n) :
    s ∈ 𝔪 ^ n := by
  obtain ⟨w', hw'⟩ := exists_mul_sub_one_mem_pow 𝔪 hw n
  have : s = w' * (w * s) - (w * w' - 1) * s := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_right _ _ hw')

/-- Elements of the localization are congruent to elements of `S` modulo every power
of its maximal ideal. -/
theorem exists_sub_algebraMap_mem_pow (p : Localization.AtPrime 𝔪) (n : ℕ) :
    ∃ s : S, p - algebraMap S (Localization.AtPrime 𝔪) s ∈
      maximalIdeal (Localization.AtPrime 𝔪) ^ n := by
  obtain ⟨⟨a, w⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl p
  obtain ⟨w', hw'⟩ := exists_mul_sub_one_mem_pow 𝔪 w.2 n
  refine ⟨a * w', ?_⟩
  have hspec := IsLocalization.mk'_spec (Localization.AtPrime 𝔪) a w
  have h1 : IsLocalization.mk' (Localization.AtPrime 𝔪) a w -
      algebraMap S (Localization.AtPrime 𝔪) (a * w') =
      IsLocalization.mk' (Localization.AtPrime 𝔪) a w *
        algebraMap S (Localization.AtPrime 𝔪) (-(↑w * w' - 1)) := by
    simp only [map_neg, map_sub, map_one, map_mul]
    linear_combination (algebraMap S (Localization.AtPrime 𝔪) w') * hspec
  rw [h1]
  refine Ideal.mul_mem_left _ _ ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (neg_mem hw')

/-- The preimage in `S` of a power of the maximal ideal of the localization is the
corresponding power of `𝔪`. -/
theorem mem_pow_of_algebraMap_mem_pow {s : S} {n : ℕ}
    (h : algebraMap S (Localization.AtPrime 𝔪) s ∈ maximalIdeal (Localization.AtPrime 𝔪) ^ n) :
    s ∈ 𝔪 ^ n := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow] at h
  obtain ⟨⟨⟨a, ha⟩, w⟩, hx⟩ :=
    (IsLocalization.mem_map_algebraMap_iff 𝔪.primeCompl (Localization.AtPrime 𝔪)).mp h
  rw [← map_mul] at hx
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists 𝔪.primeCompl (Localization.AtPrime 𝔪)).mp hx
  have hcw : ((c * w : 𝔪.primeCompl) : S) ∉ 𝔪 := (c * w).2
  refine mem_pow_of_mul_mem_pow 𝔪 hcw ?_
  have : ((c * w : 𝔪.primeCompl) : S) * s = c * a := by
    rw [Submonoid.coe_mul, ← hc]; ring
  rw [this]
  exact Ideal.mul_mem_left _ _ ha

end Localization

section Completion

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The kernel of the evaluation of the completion at stage `n` is the `n`-th power of
its maximal ideal. -/
theorem ker_evalₐ (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) n).toRingHom =
      maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
  ext s
  change AdicCompletion.evalₐ _ n s = 0 ↔ _
  let e : (R ⧸ ((maximalIdeal R) ^ n • ⊤ : Ideal R)) ≃ₐ[R] R ⧸ (maximalIdeal R) ^ n :=
    Ideal.quotientEquivAlgOfEq R (by simp)
  change e (AdicCompletion.eval _ R n s) = 0 ↔ _
  rw [map_eq_zero_iff e e.injective]
  change s ∈ (AdicCompletion.eval _ R n).ker ↔ _
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval (M := R)
    (maximalIdeal R).fg_of_isNoetherianRing]
  simp only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_pow]

/-- Membership in a power of the maximal ideal of the completion is detected at the
corresponding stage. -/
theorem mem_pow_iff_evalₐ_eq_zero (n : ℕ) (x : AdicCompletion (maximalIdeal R) R) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n ↔
      AdicCompletion.evalₐ (maximalIdeal R) n x = 0 := by
  rw [← ker_evalₐ, RingHom.mem_ker]
  rfl

end Completion

section MaximalCompletion

variable {S : Type u} [CommRing S] [IsNoetherianRing S] (𝔪 : Ideal S) [𝔪.IsMaximal]

local notation "P" => Localization.AtPrime 𝔪
local notation "P̂" => AdicCompletion (maximalIdeal (Localization.AtPrime 𝔪))
  (Localization.AtPrime 𝔪)

instance isNoetherianRing_localization : IsNoetherianRing P :=
  IsLocalization.isNoetherianRing 𝔪.primeCompl _ inferInstance

omit [IsNoetherianRing S] in
lemma algebraMap_completion_eq :
    algebraMap S P̂ = (algebraMap P P̂).comp (algebraMap S P) := rfl

/-- Every element of the completion is congruent to an element of `S` modulo every power
of its maximal ideal. -/
theorem exists_sub_algebraMap_mem_pow_completion (x : P̂) (n : ℕ) :
    ∃ s : S, x - algebraMap S P̂ s ∈ maximalIdeal P̂ ^ n := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal P) n x)
  obtain ⟨s, hs⟩ := exists_sub_algebraMap_mem_pow 𝔪 p n
  refine ⟨s, ?_⟩
  rw [mem_pow_iff_evalₐ_eq_zero, map_sub, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of, ← hp, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact hs

/-- The preimage in `S` of a power of the maximal ideal of the completion is the
corresponding power of `𝔪`. -/
theorem mem_pow_of_algebraMap_completion_mem_pow {s : S} {n : ℕ}
    (h : algebraMap S P̂ s ∈ maximalIdeal P̂ ^ n) : s ∈ 𝔪 ^ n := by
  apply mem_pow_of_algebraMap_mem_pow 𝔪
  rw [mem_pow_iff_evalₐ_eq_zero, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem] at h
  exact h

/-- The maximal ideal of the completion is generated by the image of `𝔪`. -/
theorem maximalIdeal_completion_eq_map : maximalIdeal P̂ = 𝔪.map (algebraMap S P̂) := by
  rw [algebraMap_completion_eq, ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal,
    AdicCompletion.maximalIdeal_eq_map]

/-- Powers of `𝔪` map into the powers of the maximal ideal of the completion. -/
theorem algebraMap_mem_pow {s : S} {n : ℕ} (hs : s ∈ 𝔪 ^ n) :
    algebraMap S P̂ s ∈ maximalIdeal P̂ ^ n := by
  rw [maximalIdeal_completion_eq_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hs

end MaximalCompletion

section CompleteTarget

variable {S : Type u} [CommRing S] [IsNoetherianRing S] (𝔪 : Ideal S) [𝔪.IsMaximal]
  {A : Type v} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
  (σA : S →+* A) (hσA : ∀ s, σA s ∈ maximalIdeal A ↔ s ∈ 𝔪)

local notation "P" => Localization.AtPrime 𝔪
local notation "P̂" => AdicCompletion (maximalIdeal (Localization.AtPrime 𝔪))
  (Localization.AtPrime 𝔪)

/-- The map from the localization, which exists since elements outside `𝔪` become
units of the local ring `A`. -/
noncomputable def localizationLift : P →+* A :=
  IsLocalization.lift (M := 𝔪.primeCompl) (g := σA) fun w =>
    notMem_maximalIdeal.mp fun h => w.2 ((hσA w).mp h)

omit [IsNoetherianRing S] [IsAdicComplete (maximalIdeal A) A] in
lemma localizationLift_algebraMap (s : S) :
    localizationLift 𝔪 σA hσA (algebraMap S P s) = σA s :=
  IsLocalization.lift_eq _ _

omit [IsNoetherianRing S] [IsAdicComplete (maximalIdeal A) A] in
lemma localizationLift_pow_le (n : ℕ) :
    maximalIdeal P ^ n ≤ (maximalIdeal A ^ n).comap (localizationLift 𝔪 σA hσA) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, ← Localization.AtPrime.map_eq_maximalIdeal,
    Ideal.map_map]
  refine Ideal.pow_right_mono ?_ n
  rw [Ideal.map_le_iff_le_comap]
  intro s hs
  change localizationLift 𝔪 σA hσA (algebraMap S P s) ∈ maximalIdeal A
  rw [localizationLift_algebraMap]
  exact (hσA s).mpr hs

/-- The stages of the extension to the completion. -/
noncomputable def stageMap (n : ℕ) : P̂ →+* A ⧸ maximalIdeal A ^ n :=
  (Ideal.quotientMap (maximalIdeal A ^ n) (localizationLift 𝔪 σA hσA)
    (localizationLift_pow_le 𝔪 σA hσA n)).comp
    (AdicCompletion.evalₐ (maximalIdeal P) n).toRingHom

omit [IsNoetherianRing S] [IsAdicComplete (maximalIdeal A) A] in
lemma factor_evalₐ {m n : ℕ} (hle : m ≤ n) (x : P̂) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hle)
      (AdicCompletion.evalₐ (maximalIdeal P) n x) =
        AdicCompletion.evalₐ (maximalIdeal P) m x := by
  induction x using AdicCompletion.induction_on with
  | h a =>
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
    exact AdicCompletion.Ideal.mk_eq_mk _ hle a

omit [IsNoetherianRing S] [IsAdicComplete (maximalIdeal A) A] in
lemma stageMap_of_mk {n : ℕ} (x : P̂) (p : P)
    (hp : AdicCompletion.evalₐ (maximalIdeal P) n x = Ideal.Quotient.mk _ p) :
    stageMap 𝔪 σA hσA n x = Ideal.Quotient.mk _ (localizationLift 𝔪 σA hσA p) := by
  simp only [stageMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hp,
    Ideal.quotientMap_mk]

omit [IsNoetherianRing S] [IsAdicComplete (maximalIdeal A) A] in
lemma stageMap_compatible {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal A) hle).comp (stageMap 𝔪 σA hσA n) =
      stageMap 𝔪 σA hσA m := by
  ext x
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal P) n x)
  have hpm : AdicCompletion.evalₐ (maximalIdeal P) m x = Ideal.Quotient.mk _ p := by
    rw [← factor_evalₐ 𝔪 hle, ← hp, Ideal.Quotient.factor_mk]
  rw [RingHom.comp_apply, stageMap_of_mk 𝔪 σA hσA x p hp.symm,
    stageMap_of_mk 𝔪 σA hσA x p hpm]
  rfl

/-- The extension of `σA` to the completion of `S` at `𝔪`. -/
noncomputable def completionLift : P̂ →+* A :=
  IsAdicComplete.liftRingHom (maximalIdeal A) (stageMap 𝔪 σA hσA)
    (stageMap_compatible 𝔪 σA hσA)

lemma mk_completionLift (n : ℕ) (x : P̂) :
    Ideal.Quotient.mk (maximalIdeal A ^ n) (completionLift 𝔪 σA hσA x) =
      stageMap 𝔪 σA hσA n x :=
  IsAdicComplete.mk_liftRingHom _ _ _ n x

/-- The extension restricts to `σA` on `S`. -/
theorem completionLift_algebraMap (s : S) :
    completionLift 𝔪 σA hσA (algebraMap S P̂ s) = σA s := by
  have := congrFun (IsHausdorff.funext' (maximalIdeal A)
    (f := fun s : S => completionLift 𝔪 σA hσA (algebraMap S P̂ s)) (g := σA) fun n s => by
      rw [mk_completionLift, stageMap_of_mk 𝔪 σA hσA _ (algebraMap S P s)
        (by rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]),
        localizationLift_algebraMap]) s
  exact this

/-- The extension carries powers of the maximal ideal into powers of the maximal ideal. -/
theorem completionLift_mem_pow {n : ℕ} {x : P̂} (hx : x ∈ maximalIdeal P̂ ^ n) :
    completionLift 𝔪 σA hσA x ∈ maximalIdeal A ^ n := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, mk_completionLift]
  rw [mem_pow_iff_evalₐ_eq_zero] at hx
  simp only [stageMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hx,
    map_zero]

variable (hsurj : ∀ a, ∃ s, a - σA s ∈ maximalIdeal A ^ 2)
include hsurj

/-- If `σA` is surjective modulo the square of the maximal ideal, the extension to the
completion is surjective. -/
theorem completionLift_surjective : Function.Surjective (completionLift 𝔪 σA hσA) := by
  intro a
  have hcomap : (maximalIdeal A).comap σA = 𝔪 := by ext s; exact hσA s
  have step := SquareSurjectivePowers.exists_mem_pow_sub_mem_pow_succ σA (maximalIdeal A) hsurj
  rw [hcomap] at step
  obtain ⟨s₀, hs₀⟩ := SquareSurjectivePowers.exists_sub_mem_pow σA (maximalIdeal A) hsurj 1 a
  -- a sequence of approximations with increments in increasing powers of `𝔪`
  have next : ∀ (k : ℕ) (s : S), a - σA s ∈ maximalIdeal A ^ (k + 1) →
      ∃ d ∈ 𝔪 ^ (k + 1), a - σA (s + d) ∈ maximalIdeal A ^ (k + 2) := by
    intro k s hs
    obtain ⟨d, hd, hd'⟩ := step (k + 1) (by omega) _ hs
    refine ⟨d, hd, ?_⟩
    have : a - σA (s + d) = a - σA s - σA d := by rw [map_add]; ring
    rwa [this]
  choose D hD hD' using next
  let seq : (k : ℕ) → {s : S // a - σA s ∈ maximalIdeal A ^ (k + 1)} := fun k =>
    Nat.rec ⟨s₀, by simpa using hs₀⟩ (fun k p => ⟨p.1 + D k p.1 p.2, hD' k p.1 p.2⟩) k
  have hseq : ∀ k, (seq (k + 1)).1 = (seq k).1 + D k (seq k).1 (seq k).2 := fun k => rfl
  have hdiff : ∀ m n, m ≤ n → (seq n).1 - (seq m).1 ∈ 𝔪 ^ (m + 1) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hseq]
      have : (seq n).1 + D n (seq n).1 (seq n).2 - (seq m).1 =
          ((seq n).1 - (seq m).1) + D n (seq n).1 (seq n).2 := by ring
      rw [this]
      exact Ideal.add_mem _ ih
        (Ideal.pow_le_pow_right (by omega) (hD n (seq n).1 (seq n).2))
  have hsmul : ∀ (J : Ideal P̂), (J • ⊤ : Submodule P̂ P̂) = J := fun J => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal P̂) inferInstance
    (f := fun k => algebraMap S P̂ (seq k).1) (by
      intro m n hmn
      rw [SModEq.sub_mem, hsmul, ← map_sub]
      have h := Ideal.pow_le_pow_right (Nat.le_succ m) (hdiff m n hmn)
      have h' : (seq m).1 - (seq n).1 ∈ 𝔪 ^ m := by
        rw [← neg_sub]; exact neg_mem h
      exact algebraMap_mem_pow 𝔪 h')
  refine ⟨L, ?_⟩
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal A)]
  intro n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
  have h1 := hL n
  rw [SModEq.sub_mem, hsmul] at h1
  have h2 := completionLift_mem_pow 𝔪 σA hσA h1
  rw [map_sub, completionLift_algebraMap] at h2
  have h3 : a - σA (seq n).1 ∈ maximalIdeal A ^ n :=
    Ideal.pow_le_pow_right (Nat.le_succ n) (seq n).2
  have : completionLift 𝔪 σA hσA L - a = -(σA (seq n).1 - completionLift 𝔪 σA hσA L) -
      (a - σA (seq n).1) := by ring
  rw [this]
  exact Ideal.sub_mem _ (neg_mem h2) h3

/-- The preimage of each power of the maximal ideal under the surjective extension. -/
theorem completionLift_comap_pow (n : ℕ) :
    (maximalIdeal A ^ n).comap (completionLift 𝔪 σA hσA) =
      RingHom.ker (completionLift 𝔪 σA hσA) ⊔ maximalIdeal P̂ ^ n := by
  have hs := completionLift_surjective 𝔪 σA hσA hsurj
  rw [← IsLocalRing.map_maximalIdeal_of_surjective _ hs, ← Ideal.map_pow,
    Ideal.comap_map_of_surjective _ hs, sup_comm]
  rfl

end CompleteTarget

end Langlands.CommutativeAlgebra.MaximalLocalizationCompletion
