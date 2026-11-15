import Langlands.Global.RankinSelberg.EqualAnalyticDominated
import Langlands.Global.RankinSelberg.EqualAnalyticCharacter

/-! # Fourier transforms of Schwartz–Bruhat functions are dominated

For a standard additive character `ψ` and `Φ ∈ S(𝔸^n)`, the Fourier transform
`Φ̂(η) = ∫ Φ(y) ψ(Σ_j y_j η_j) dy` for the covolume-one measure is continuous and dominated:
it vanishes unless the finite coordinates of `η` lie in `d⁻¹ Ô`, and decays faster than every
power of the archimedean coordinates. For a pure tensor the transform factors into an archimedean
Fourier transform of a Schwartz function and a finite-adelic transform; the latter is supported
in `d⁻¹ Ô^n` because the finite factor is invariant under translation by `(N Ô)^n`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped Classical FourierTransform
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable (F : Type u) [Field F] [NumberField F]

local instance fourierDominatedMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance fourierDominatedBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

local instance fourierDominatedFiniteMeasurableSpace : MeasurableSpace (FiniteAdeles F) :=
  borel _

local instance fourierDominatedFiniteBorelSpace : BorelSpace (FiniteAdeles F) := ⟨rfl⟩

local instance fourierDominatedFiniteSecondCountable :
    SecondCountableTopology (FiniteAdeles F) :=
  finiteAdeles_secondCountableTopology F

local instance fourierDominatedAdelesSecondCountable : SecondCountableTopology (Adeles F) :=
  adeles_secondCountableTopology F

local instance fourierDominatedRowSecondCountable (k m : ℕ) :
    SecondCountableTopology (Matrix (Fin k) (Fin m) (Adeles F)) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin m → Adeles F))

local instance fourierDominatedFiniteLocallyCompact : LocallyCompactSpace (FiniteAdeles F) :=
  finiteAdeles_locallyCompactSpace F

/-- The adele `(u, 0)` with archimedean component `u`. -/
def infiniteAdele (u : InfiniteAdeles F) : Adeles F := (u, 0)

/-- The adele `(0, t)` with finite component `t`. -/
def finiteAdele (t : FiniteAdeles F) : Adeles F := (0, t)

theorem addChar_eq_infinite_mul_finite (ψ : AddChar (Adeles F) ℂ) (x : Adeles F) :
    ψ x = ψ (infiniteAdele F x.1) * ψ (finiteAdele F x.2) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  exact Prod.ext (add_zero _).symm (zero_add _).symm

theorem unitExp_eq_fourierChar (t : ℝ) : unitExp t = 𝐞 t := rfl

/-- On the archimedean adeles the scaled standard character is the trace character. -/
theorem standardCharacter_mul_infiniteAdele (b : F) (u : InfiniteAdeles F) :
    standardCharacter F (algebraMap F (Adeles F) b * infiniteAdele F u) =
      (𝐞 (mixedTrace F (mixedEmbedding F b * InfiniteAdeleRing.ringEquiv_mixedSpace F u)) :
        ℂ) := by
  rw [standardCharacter_apply, adelicCharacter_of_integral F _ (by
    rw [adeles_mul_snd, adeles_algebraMap_snd]
    change algebraMap F (FiniteAdeles F) b * 0 ∈ integralFiniteAdeles F
    rw [mul_zero]
    exact zero_mem _)]
  congr 1
  rw [adeles_mul_fst, adeles_algebraMap_fst, infiniteTrace_apply, map_mul,
    ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

/-- The finite-adelic factor `t ↦ ψ(0, t)`. -/
def finiteCharacter (ψ : AddChar (Adeles F) ℂ) (t : FiniteAdeles F) : ℂ :=
  ψ (finiteAdele F t)

theorem finiteCharacter_add (ψ : AddChar (Adeles F) ℂ) (s t : FiniteAdeles F) :
    finiteCharacter F ψ (s + t) = finiteCharacter F ψ s * finiteCharacter F ψ t := by
  unfold finiteCharacter
  rw [← AddChar.map_add_eq_mul]
  congr 1
  exact Prod.ext (add_zero _).symm rfl

theorem standardCharacter_mul_finiteAdele (b : F) (t : FiniteAdeles F) :
    standardCharacter F (algebraMap F (Adeles F) b * finiteAdele F t) =
      (adelicCharacter F (finiteToAdeles F (algebraMap F (FiniteAdeles F) b * t)) : ℂ) := by
  rw [standardCharacter_apply]
  congr 2
  exact Prod.ext (mul_zero _) rfl

/-- **Dual denominator.** If `ψ₀(0, z c) = 1` for every `c ∈ Ô`, then `D z ∈ Ô` for a fixed
nonzero `D ∈ 𝒪`. -/
theorem exists_dual_denominator_finite :
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ z : FiniteAdeles F,
      (∀ c ∈ integralFiniteAdeles F,
        adelicCharacter F (finiteToAdeles F (z * c)) = 1) →
      algebraMap (𝓞 F) (FiniteAdeles F) D * z ∈ integralFiniteAdeles F := by
  obtain ⟨D, hD, hDx⟩ := exists_dual_denominator F
  refine ⟨D, hD, fun z hz => ?_⟩
  set r := finiteShift F z
  have hr := sub_finiteShift_mem F z
  have htr : ∀ c : 𝓞 F, ∃ m : ℤ,
      Algebra.trace ℚ F (r * algebraMap (𝓞 F) F c) = m := by
    intro c
    have hc : algebraMap (𝓞 F) (FiniteAdeles F) c ∈ integralFiniteAdeles F :=
      algebraMap_ringOfIntegers_mem F c
    have h1 := hz _ hc
    have hmem : z * algebraMap (𝓞 F) (FiniteAdeles F) c -
        algebraMap F (FiniteAdeles F) (r * algebraMap (𝓞 F) F c) ∈ integralFiniteAdeles F := by
      rw [map_mul, ← IsScalarTower.algebraMap_apply, ← sub_mul]
      exact mul_mem hr hc
    rw [adelicCharacter_finiteToAdeles F _ _ hmem, unitExp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    refine ⟨-m, ?_⟩
    have : ((Algebra.trace ℚ F (r * algebraMap (𝓞 F) F c) : ℚ) : ℝ) = ((-m : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  obtain ⟨s, hs⟩ := hDx r htr
  have hz' : z = algebraMap F (FiniteAdeles F) r + (z - algebraMap F (FiniteAdeles F) r) := by
    abel
  rw [hz', mul_add]
  refine add_mem ?_ (mul_mem (algebraMap_ringOfIntegers_mem F D) hr)
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeles F), ← map_mul, ← hs,
    ← IsScalarTower.algebraMap_apply]
  exact algebraMap_ringOfIntegers_mem F s

theorem adeles_sum_fst {ι : Type*} (t : Finset ι) (f : ι → Adeles F) :
    (∑ i ∈ t, f i).1 = ∑ i ∈ t, (f i).1 := by
  induction t using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adeles_add_fst, ih]

theorem adeles_sum_snd {ι : Type*} (t : Finset ι) (f : ι → Adeles F) :
    (∑ i ∈ t, f i).2 = ∑ i ∈ t, (f i).2 := by
  induction t using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adeles_add_snd, ih]

/-- The pairing character splits into the archimedean trace character and the finite factor. -/
theorem addChar_rowPairing (ψ : AddChar (Adeles F) ℂ) (b : F)
    (hb : ∀ x, ψ x = standardCharacter F (algebraMap F (Adeles F) b * x)) (n : ℕ)
    (y η : RowVector F n) :
    ψ (∑ j, y 0 j * η 0 j) =
      (𝐞 (mixedTrace F (mixedEmbedding F b *
        ∑ j, archimedeanCoordinates F n y j * archimedeanCoordinates F n η j)) : ℂ) *
      finiteCharacter F ψ (∑ j, finiteCoordinates F n y j * finiteCoordinates F n η j) := by
  have h1 : InfiniteAdeleRing.ringEquiv_mixedSpace F (∑ j, y 0 j * η 0 j).1 =
      ∑ j, archimedeanCoordinates F n y j * archimedeanCoordinates F n η j := by
    rw [adeles_sum_fst, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [adeles_mul_fst, map_mul]
    rfl
  have h2 : (∑ j, y 0 j * η 0 j).2 =
      ∑ j, finiteCoordinates F n y j * finiteCoordinates F n η j := by
    rw [adeles_sum_snd]
    rfl
  rw [addChar_eq_infinite_mul_finite, hb, standardCharacter_mul_infiniteAdele, h1]
  unfold finiteCharacter
  rw [h2]

/-- The Fourier transform of a pure tensor factors. -/
theorem fourierTransform_pure [CompactSpace (AdeleQuotient F)] (n : ℕ)
    (ψ : AddChar (Adeles F) ℂ) (b : F)
    (hb : ∀ x, ψ x = standardCharacter F (algebraMap F (Adeles F) b * x))
    (Φinf : SchwartzMap (ArchRow F n) ℂ) (Φfin : FinRow F n → ℂ) (η : RowVector F n) :
    fourierTransform F n ψ (fun x => Φinf (archimedeanCoordinates F n x) *
        Φfin (finiteCoordinates F n x)) η =
      (rowConstant F n : ℝ) •
        ((∫ e, Φinf e * (𝐞 (mixedTrace F (mixedEmbedding F b *
            ∑ j, e j * archimedeanCoordinates F n η j)) : ℂ)) *
          ∫ a, Φfin a * finiteCharacter F ψ (∑ j, a j * finiteCoordinates F n η j)
            ∂(Measure.addHaar : Measure (FinRow F n))) := by
  unfold fourierTransform
  rw [← integral_rect_tensor F n
    (fun e => Φinf e * (𝐞 (mixedTrace F (mixedEmbedding F b *
      ∑ j, e j * archimedeanCoordinates F n η j)) : ℂ))
    (fun a => Φfin a * finiteCharacter F ψ (∑ j, a j * finiteCoordinates F n η j))]
  congr 1
  funext y
  rw [addChar_rowPairing F ψ b hb]
  ring

theorem finiteCharacter_eq (ψ : AddChar (Adeles F) ℂ) (b : F)
    (hb : ∀ x, ψ x = standardCharacter F (algebraMap F (Adeles F) b * x)) (t : FiniteAdeles F) :
    finiteCharacter F ψ t =
      (adelicCharacter F (finiteToAdeles F (algebraMap F (FiniteAdeles F) b * t)) : ℂ) := by
  rw [finiteCharacter, hb, standardCharacter_mul_finiteAdele]

theorem norm_finiteCharacter (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (t : FiniteAdeles F) : ‖finiteCharacter F ψ t‖ = 1 :=
  hψ.2.2.2 _

/-- The finite-adelic Fourier transform of a locally constant compactly supported function is
supported in `d⁻¹ Ô^n`. -/
theorem exists_finiteFourier_support (n : ℕ) (ψ : AddChar (Adeles F) ℂ) (b : F) (hb0 : b ≠ 0)
    (hb : ∀ x, ψ x = standardCharacter F (algebraMap F (Adeles F) b * x))
    (Φfin : FinRow F n → ℂ) (hlc : IsLocallyConstant Φfin) (hcs : HasCompactSupport Φfin) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ t : FinRow F n,
      (∫ a, Φfin a * finiteCharacter F ψ (∑ j, a j * t j)
        ∂(Measure.addHaar : Measure (FinRow F n))) ≠ 0 →
      ∀ j, algebraMap (𝓞 F) (FiniteAdeles F) d * t j ∈ integralFiniteAdeles F := by
  obtain ⟨N, hN, hinv⟩ := exists_nat_invariant_of_isLocallyConstant F Φfin hlc hcs
  obtain ⟨D, hD, hDz⟩ := exists_dual_denominator_finite F
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 F) b
  have hq0 : algebraMap (𝓞 F) F q ≠ 0 :=
    (IsFractionRing.injective (𝓞 F) F).ne_iff.mpr (nonZeroDivisors.ne_zero hq) |>.trans_eq
      (map_zero _) |> fun h => by simpa using h
  have hp : algebraMap (𝓞 F) F p = b * algebraMap (𝓞 F) F q := by
    rw [← hpq, div_mul_cancel₀ _ hq0]
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact hb0 (by simpa [hq0] using hp.symm)
  refine ⟨D * N * p, by
    refine mul_ne_zero (mul_ne_zero hD ?_) hp0
    exact_mod_cast hN.ne', fun t ht j => ?_⟩
  set f : FinRow F n → ℂ := fun a => Φfin a * finiteCharacter F ψ (∑ l, a l * t l) with hf
  -- the character is trivial on `N Ô t_j`
  have hchar : ∀ c ∈ integralFiniteAdeles F,
      finiteCharacter F ψ ((N : FiniteAdeles F) * c * t j) = 1 := by
    intro c hc
    set u : FinRow F n := Pi.single j ((N : FiniteAdeles F) * c) with hu
    have hu' : ∀ l, ∃ c' ∈ integralFiniteAdeles F, u l = (N : FiniteAdeles F) * c' := by
      intro l
      by_cases hl : l = j
      · subst hl
        exact ⟨c, hc, by simp [hu]⟩
      · exact ⟨0, zero_mem _, by simp [hu, hl]⟩
    have hsum : ∑ l, u l * t l = (N : FiniteAdeles F) * c * t j := by
      rw [Finset.sum_eq_single j]
      · simp [hu]
      · intro l _ hl
        simp [hu, hl]
      · simp
    have hshift : ∀ a, f (a + u) = f a * finiteCharacter F ψ ((N : FiniteAdeles F) * c * t j) := by
      intro a
      simp only [hf]
      rw [hinv a u hu']
      have : ∑ l, (a + u) l * t l = ∑ l, a l * t l + ∑ l, u l * t l := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Pi.add_apply, add_mul]
      rw [this, finiteCharacter_add, hsum]
      ring
    have hint := integral_add_right_eq_self (μ := (Measure.addHaar : Measure (FinRow F n))) f u
    simp_rw [hshift] at hint
    rw [integral_mul_const] at hint
    have hne : ∫ a, f a ∂(Measure.addHaar : Measure (FinRow F n)) ≠ 0 := ht
    have := mul_left_cancel₀ hne (hint.trans (mul_one _).symm)
    exact this
  have hz : ∀ c ∈ integralFiniteAdeles F, adelicCharacter F (finiteToAdeles F
      ((algebraMap F (FiniteAdeles F) b * (N : FiniteAdeles F) * t j) * c)) = 1 := by
    intro c hc
    have h := hchar c hc
    rw [finiteCharacter_eq F ψ b hb, ← Circle.coe_one, Circle.coe_inj] at h
    rw [← h]
    congr 2
    ring
  have hD' := hDz _ hz
  have hpf : algebraMap (𝓞 F) (FiniteAdeles F) p =
      algebraMap F (FiniteAdeles F) b * algebraMap (𝓞 F) (FiniteAdeles F) q := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeles F), hp, map_mul,
      ← IsScalarTower.algebraMap_apply]
  rw [map_mul, map_mul, hpf, map_natCast]
  have : algebraMap (𝓞 F) (FiniteAdeles F) D * (N : FiniteAdeles F) *
      (algebraMap F (FiniteAdeles F) b * algebraMap (𝓞 F) (FiniteAdeles F) q) * t j =
      (algebraMap (𝓞 F) (FiniteAdeles F) D *
        (algebraMap F (FiniteAdeles F) b * (N : FiniteAdeles F) * t j)) *
        algebraMap (𝓞 F) (FiniteAdeles F) q := by ring
  rw [this]
  exact mul_mem hD' (algebraMap_ringOfIntegers_mem F q)

theorem integrable_mul_pairing (n : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) {Φ : RowVector F n → ℂ}
    (hΦ : Integrable Φ (rectangleMeasure F 1 n)) (η : RowVector F n) :
    Integrable (fun y => Φ y * ψ (∑ j, y 0 j * η 0 j)) (rectangleMeasure F 1 n) := by
  refine hΦ.mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun y => (hψ.2.2.2 _).le)
  have hc : Continuous fun y : RowVector F n => ψ (∑ j, y 0 j * η 0 j) :=
    hψ.1.comp (continuous_finsetSum _ fun j _ =>
      (continuous_id.matrix_elem 0 j).mul continuous_const)
  exact hc.aestronglyMeasurable

theorem fourierTransform_add (n : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) {Φ Ψ : RowVector F n → ℂ}
    (hΦ : Integrable Φ (rectangleMeasure F 1 n)) (hΨ : Integrable Ψ (rectangleMeasure F 1 n)) :
    fourierTransform F n ψ (Φ + Ψ) = fourierTransform F n ψ Φ + fourierTransform F n ψ Ψ := by
  funext η
  simp only [fourierTransform, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_pairing F n ψ hψ hΦ η)
    (integrable_mul_pairing F n ψ hψ hΨ η)

theorem fourierTransform_smul (n : ℕ) (ψ : AddChar (Adeles F) ℂ) (c : ℂ)
    (Φ : RowVector F n → ℂ) :
    fourierTransform F n ψ (c • Φ) = c • fourierTransform F n ψ Φ := by
  funext η
  simp only [fourierTransform, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem fourierTransform_zero (n : ℕ) (ψ : AddChar (Adeles F) ℂ) :
    fourierTransform F n ψ 0 = 0 := by
  funext η
  simp [fourierTransform]

/-- The Fourier transform of an integrable function is continuous. -/
theorem continuous_fourierTransform (n : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) {Φ : RowVector F n → ℂ}
    (hΦ : Integrable Φ (rectangleMeasure F 1 n)) : Continuous (fourierTransform F n ψ Φ) := by
  unfold fourierTransform
  refine continuous_of_dominated (bound := fun y => ‖Φ y‖)
    (fun η => (integrable_mul_pairing F n ψ hψ hΦ η).aestronglyMeasurable)
    (fun η => Filter.Eventually.of_forall fun y => ?_) hΦ.norm
    (Filter.Eventually.of_forall fun y => ?_)
  · rw [norm_mul, hψ.2.2.2, mul_one]
  · exact continuous_const.mul (hψ.1.comp (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_id.matrix_elem 0 j)))

/-- The Fourier transform of a pure Schwartz–Bruhat tensor is dominated. -/
theorem isRowDominated_fourierTransform_pure [CompactSpace (AdeleQuotient F)] (n : ℕ)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    {Φ : RowVector F n → ℂ} (hΦ : IsPureSchwartzBruhat F n Φ) :
    IsRowDominated F n (fourierTransform F n ψ Φ) := by
  obtain ⟨b, hb0, hb⟩ := exists_eq_standardCharacter_mul F ψ hψ
  obtain ⟨Φinf, Φfin, hlc, hcs, rfl⟩ := hΦ
  obtain ⟨d, hd, hds⟩ := exists_finiteFourier_support F n ψ b hb0 hb Φfin hlc hcs
  refine ⟨d, hd, fun η hη j => ?_, fun N => ?_⟩
  · rw [fourierTransform_pure F n ψ b hb] at hη
    exact hds _ (right_ne_zero_of_mul (right_ne_zero_of_smul hη)) j
  · have hβ : mixedEmbedding F b * mixedEmbedding F b⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hb0, map_one]
    obtain ⟨C, hC⟩ := exists_archimedeanFourier_decay F n (mixedEmbedding F b)
      (mixedEmbedding F b⁻¹) hβ Φinf N
    set B := ∫ a, ‖Φfin a‖ ∂(Measure.addHaar : Measure (FinRow F n))
    refine ⟨(rowConstant F n : ℝ) * C * B, fun η => ?_⟩
    rw [fourierTransform_pure F n ψ b hb, norm_smul, norm_mul]
    have hBle : ‖∫ a, Φfin a * finiteCharacter F ψ (∑ j, a j * finiteCoordinates F n η j)
        ∂(Measure.addHaar : Measure (FinRow F n))‖ ≤ B := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      congr 1
      funext a
      rw [norm_mul, norm_finiteCharacter F ψ hψ, mul_one]
    have hB0 : 0 ≤ B := integral_nonneg fun a => norm_nonneg _
    have hc0 : 0 ≤ ‖((rowConstant F n : ℝ))‖ := norm_nonneg _
    have hCη := hC (archimedeanCoordinates F n η)
    have hC0 : 0 ≤ C := le_trans (by positivity) hCη
    calc (1 + ‖archimedeanCoordinates F n η‖) ^ N *
          (‖((rowConstant F n : ℝ))‖ * (‖∫ e, Φinf e * (𝐞 (mixedTrace F (mixedEmbedding F b *
            ∑ j, e j * archimedeanCoordinates F n η j)) : ℂ)‖ *
          ‖∫ a, Φfin a * finiteCharacter F ψ (∑ j, a j * finiteCoordinates F n η j)
            ∂(Measure.addHaar : Measure (FinRow F n))‖)) =
        ‖((rowConstant F n : ℝ))‖ * ((1 + ‖archimedeanCoordinates F n η‖) ^ N *
          ‖∫ e, Φinf e * (𝐞 (mixedTrace F (mixedEmbedding F b *
            ∑ j, e j * archimedeanCoordinates F n η j)) : ℂ)‖) *
          ‖∫ a, Φfin a * finiteCharacter F ψ (∑ j, a j * finiteCoordinates F n η j)
            ∂(Measure.addHaar : Measure (FinRow F n))‖ := by ring
      _ ≤ ‖((rowConstant F n : ℝ))‖ * C * B := by gcongr
      _ = (rowConstant F n : ℝ) * C * B := by
        rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]

/-- The Fourier transform of a Schwartz–Bruhat function is continuous and dominated. -/
theorem fourierTransform_properties [CompactSpace (AdeleQuotient F)] (n : ℕ)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    {Φ : RowVector F n → ℂ} (hΦ : Φ ∈ schwartzBruhat F n) :
    Continuous (fourierTransform F n ψ Φ) ∧ IsRowDominated F n (fourierTransform F n ψ Φ) := by
  refine ⟨continuous_fourierTransform F n ψ hψ (schwartzBruhat_properties F n hΦ).2.1, ?_⟩
  induction hΦ using Submodule.span_induction with
  | mem Φ h => exact isRowDominated_fourierTransform_pure F n ψ hψ h
  | zero => rw [fourierTransform_zero]; exact isRowDominated_zero n
  | add Φ Ψ hΦm hΨm hΦ hΨ =>
    rw [fourierTransform_add F n ψ hψ (schwartzBruhat_properties F n hΦm).2.1
      (schwartzBruhat_properties F n hΨm).2.1]
    exact hΦ.add hΨ
  | smul c Φ _ hΦ =>
    rw [fourierTransform_smul]
    exact hΦ.smul c

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
