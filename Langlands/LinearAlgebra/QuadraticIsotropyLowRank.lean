import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.LinearAlgebra.QuadraticIsotropyApproximation
import Langlands.LinearAlgebra.QuadraticIsotropyCoordinates
import Langlands.LinearAlgebra.QuadraticNormLocalGlobal

/-! # Diagonal local isotropy under extension and in low ranks -/

noncomputable section

universe u v

open NumberField QuadraticMap Filter
open scoped NumberField NumberField.LiesOver

namespace Langlands.QuadraticIsotropy

/-- A diagonal form has a nonzero zero at every actual completion of its number field. -/
abbrev DiagonalLocallyIsotropic (F : Type u) [Field F] [NumberField F]
    {n : ℕ} (w : Fin n → F) : Prop :=
  ∀ p : Global.Place F, ¬ (weightedSumSquares (Global.placeCompletion F p)
    (fun i => algebraMap F (Global.placeCompletion F p) (w i))).Anisotropic

private theorem weightedSumSquares_eq_sum {K : Type*} [CommRing K] {n : ℕ}
    (w x : Fin n → K) : weightedSumSquares K w x = ∑ i, w i * x i ^ 2 := by
  simp [weightedSumSquares_apply, pow_two]

private theorem isotropic_map {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) {w : Fin n → K} (h : ¬ (weightedSumSquares K w).Anisotropic) :
    ¬ (weightedSumSquares L (fun i => f (w i))).Anisotropic := by
  obtain ⟨x, hx, hz⟩ := (not_anisotropic_iff_exists _).mp h
  apply (not_anisotropic_iff_exists _).mpr
  refine ⟨fun i => f (x i), ?_, ?_⟩
  · intro hzero
    apply hx
    funext i
    exact f.injective (by simpa only [Pi.zero_apply, map_zero] using congrFun hzero i)
  · have hf := congrArg f hz
    simpa only [weightedSumSquares_eq_sum, map_sum, map_mul, map_pow, map_zero] using hf

/-- An extension of number fields preserves local isotropy of a diagonal form. -/
theorem locallyIsotropic_map {F : Type u} [Field F] [NumberField F]
    (E : Type v) [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {w : Fin n → F} (h : DiagonalLocallyIsotropic F w) :
    DiagonalLocallyIsotropic E (fun i => algebraMap F E (w i)) := by
  intro place
  rcases place with p | q
  · let p₀ := p.comap (algebraMap F E)
    have hp := h (.inl p₀)
    change ¬ (weightedSumSquares p₀.Completion
      (fun i => algebraMap F p₀.Completion (w i))).Anisotropic at hp
    have he := isotropic_map (Global.AdelicFunctoriality.infiniteCompletionMap (algebraMap F E) p) hp
    change ¬ (weightedSumSquares p.Completion
      (fun i => algebraMap E p.Completion (algebraMap F E (w i)))).Anisotropic
    simpa only [p₀, Global.AdelicFunctoriality.infiniteCompletionMap_coe] using he
  · let q₀ := q.under (𝓞 F)
    have hq := h (.inr q₀)
    change ¬ (weightedSumSquares (q₀.adicCompletion F)
      (fun i => algebraMap F (q₀.adicCompletion F) (w i))).Anisotropic at hq
    have he := isotropic_map (Global.AdelicFunctoriality.FiniteExtension.completionMap q₀ q) hq
    change ¬ (weightedSumSquares (q.adicCompletion E)
      (fun i => algebraMap E (q.adicCompletion E) (algebraMap F E (w i)))).Anisotropic
    simpa only [Global.AdelicFunctoriality.FiniteExtension.completionMap_coe] using he

section Algebra

variable {K : Type*} [Field K]

private theorem isotropic_fin_two_iff (w : Fin 2 → K) (h₀ : w 0 ≠ 0) :
    ¬ (weightedSumSquares K w).Anisotropic ↔ IsSquare (-w 1 / w 0) := by
  have eval (z : Fin 2 → K) :
      weightedSumSquares K w z = w 0 * (z 0 ^ 2 - (-w 1 / w 0) * z 1 ^ 2) := by
    rw [weightedSumSquares_eq_sum, Fin.sum_univ_two]
    field_simp
    ring
  constructor
  · intro h
    obtain ⟨z, hz, he⟩ := (not_anisotropic_iff_exists _).mp h
    have hne : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
      by_contra! hn
      apply hz
      funext i
      fin_cases i
      · exact hn.1
      · exact hn.2
    rw [eval] at he
    exact QuadraticNormEquation.isSquare_of_binary_zero hne ((mul_eq_zero.mp he).resolve_left h₀)
  · intro h
    obtain ⟨s, hs⟩ := h.exists_sq
    refine (not_anisotropic_iff_exists _).mpr ⟨![s, 1], ?_, ?_⟩
    · intro he
      exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun he (1 : Fin 2))
    · rw [eval]
      simp [hs]

/-- In dimension three, normalizing by the first coefficient turns isotropy into a norm equation. -/
theorem isotropic_fin_three_iff [CharZero K] (w : Fin 3 → K) (h₀ : w 0 ≠ 0) (h₁ : w 1 ≠ 0) :
    ¬ (weightedSumSquares K w).Anisotropic ↔
      ∃ x y : K, x ^ 2 - (-w 1 / w 0) * y ^ 2 = -w 2 / w 0 := by
  have eval (z : Fin 3 → K) : weightedSumSquares K w z =
      w 0 * (z 0 ^ 2 - (-w 1 / w 0) * z 1 ^ 2 - (-w 2 / w 0) * z 2 ^ 2) := by
    rw [weightedSumSquares_eq_sum, Fin.sum_univ_three]
    field_simp
    ring
  constructor
  · intro h
    obtain ⟨z, hz, he⟩ := (not_anisotropic_iff_exists _).mp h
    have hne : z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 := by
      by_contra! hn
      apply hz
      funext i
      fin_cases i
      · exact hn.1
      · exact hn.2.1
      · exact hn.2.2
    rw [eval] at he
    exact QuadraticNormEquation.exists_eq_of_ternary_zero (div_ne_zero (neg_ne_zero.mpr h₁) h₀)
      hne (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left h₀))
  · rintro ⟨x, y, he⟩
    refine (not_anisotropic_iff_exists _).mpr ⟨![x, y, 1], ?_, ?_⟩
    · intro hz
      exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun hz (2 : Fin 3))
    · rw [eval]
      simp [he]

end Algebra

section NumberField

variable {F : Type u} [Field F] [NumberField F]

theorem not_locallyIsotropic_fin_zero (w : Fin 0 → F) : ¬ DiagonalLocallyIsotropic F w := by
  intro h
  let p : InfinitePlace F := Classical.choice inferInstance
  exact h (.inl p) (fun x _ => Subsingleton.elim x 0)

theorem not_locallyIsotropic_fin_one (w : Fin 1 → F) (hw : ∀ i, w i ≠ 0) :
    ¬ DiagonalLocallyIsotropic F w := by
  intro h
  let p : InfinitePlace F := Classical.choice inferInstance
  have hp := h (.inl p)
  change ¬ (weightedSumSquares p.Completion
    (fun i => algebraMap F p.Completion (w i))).Anisotropic at hp
  apply hp
  intro z hz
  rw [weightedSumSquares_eq_sum, Fin.sum_univ_one] at hz
  have hzero := (mul_eq_zero.mp hz).resolve_left ((map_ne_zero _).2 (hw 0))
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  exact hi.symm ▸ sq_eq_zero_iff.mp hzero

/-- Reflection of squares from the finite completions gives the binary case. -/
theorem isotropic_fin_two (w : Fin 2 → F) (hw : ∀ i, w i ≠ 0)
    (h : DiagonalLocallyIsotropic F w) : ¬ (weightedSumSquares F w).Anisotropic := by
  apply (isotropic_fin_two_iff w (hw 0)).mpr
  apply QuadraticNormLocalGlobal.isSquare_of_all_finite
  intro q
  have hq := h (.inr q)
  let a : Fin 2 → q.adicCompletion F := fun i => algebraMap F (q.adicCompletion F) (w i)
  have hw₀ : a 0 ≠ 0 := (map_ne_zero _).2 (hw 0)
  simpa only [a, map_neg, map_div₀] using (isotropic_fin_two_iff a hw₀).mp hq

private theorem exists_local_norm_of_isotropic {A : Type*} [Field A] [Algebra F A]
    (w : Fin 3 → F) (hw : ∀ i, w i ≠ 0)
    (h : ¬ (weightedSumSquares A (fun i => algebraMap F A (w i))).Anisotropic) :
    ∃ x y : A, x ^ 2 - algebraMap F A (-w 1 / w 0) * y ^ 2 = algebraMap F A (-w 2 / w 0) := by
  let : CharZero A := Algebra.charZero_of_charZero F A
  have he := (isotropic_fin_three_iff _ ((map_ne_zero _).2 (hw 0)) ((map_ne_zero _).2 (hw 1))).mp h
  simpa only [map_div₀, map_neg] using he

/-- The local-to-global quadratic norm equation gives the ternary case. -/
theorem isotropic_fin_three (norm : QuadraticNormLocalGlobalStatement.{u})
    (w : Fin 3 → F) (hw : ∀ i, w i ≠ 0) (h : DiagonalLocallyIsotropic F w) :
    ¬ (weightedSumSquares F w).Anisotropic := by
  apply (isotropic_fin_three_iff w (hw 0) (hw 1)).mpr
  exact norm (div_ne_zero (neg_ne_zero.mpr (hw 1)) (hw 0))
    (div_ne_zero (neg_ne_zero.mpr (hw 2)) (hw 0))
    (fun q => exists_local_norm_of_isotropic w hw (h (.inr q)))
    (fun p => exists_local_norm_of_isotropic w hw (h (.inl p)))

/-- A diagonal form with at least three nonzero coefficients is isotropic at
almost every finite place. -/
theorem eventually_isotropic_diagonal {n : ℕ} (w : Fin (n + 3) → F) (hw : ∀ i, w i ≠ 0) :
    ∀ᶠ q : Global.FinitePlace F in cofinite,
      ¬ (weightedSumSquares (Global.FiniteCompletion F q)
        (fun i => algebraMap F (Global.FiniteCompletion F q) (w i))).Anisotropic := by
  induction n with
  | zero =>
    filter_upwards [QuadraticNormLocalGlobal.eventually_exists_eq
      (div_ne_zero (neg_ne_zero.mpr (hw 1)) (hw 0))
      (div_ne_zero (neg_ne_zero.mpr (hw 2)) (hw 0))] with q h
    let A := Global.FiniteCompletion F q
    let : CharZero A := Algebra.charZero_of_charZero F A
    apply (isotropic_fin_three_iff _ ((map_ne_zero _).2 (hw 0)) ((map_ne_zero _).2 (hw 1))).mpr
    simpa only [map_div₀, map_neg] using h
  | succ n ih =>
    filter_upwards [ih (Fin.tail w) (fun i => hw i.succ)] with q h
    let A := Global.FiniteCompletion F q
    let c : Fin ((n + 3) + 1) → A := fun i => algebraMap F A (w i)
    change ¬ (weightedSumSquares A c).Anisotropic
    rw [← Fin.cons_self_tail c]
    obtain ⟨z, hz, hzq⟩ := (not_anisotropic_iff_exists _).mp h
    refine (not_anisotropic_iff_exists _).mpr ⟨Fin.cons 0 z, ?_, ?_⟩
    · intro he
      apply hz
      funext i
      simpa using congrFun he i.succ
    · rw [weightedSumSquares_cons]
      have hzq' : weightedSumSquares A (Fin.tail c) z = 0 := hzq
      simp [hzq']

end NumberField

/-- The four-dimensional case of diagonal local-to-global isotropy. -/
def NumberFieldDiagonalRankFourIsotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (w : Fin 4 → F), (∀ i, w i ≠ 0) →
    DiagonalLocallyIsotropic F w → ¬ (weightedSumSquares F w).Anisotropic

/-- Quadratic norm descent and the rank-four case give diagonal isotropy in every dimension. -/
theorem diagonalIsotropy_of_norm_and_rankFour
    (norm : QuadraticNormLocalGlobalStatement.{u})
    (rankFour : NumberFieldDiagonalRankFourIsotropyStatement.{u}) :
    NumberFieldDiagonalQuadraticIsotropyStatement.{u} := by
  intro F _ _ n
  induction n with
  | zero =>
    intro w _ h
    exact (not_locallyIsotropic_fin_zero w h).elim
  | succ n ih =>
    intro w hw h
    rcases n with _ | _ | _ | _ | k
    · exact (not_locallyIsotropic_fin_one w hw h).elim
    · exact isotropic_fin_two w hw h
    · exact isotropic_fin_three norm w hw h
    · exact rankFour F w hw h
    · let tail := Fin.tail (Fin.tail w)
      let a := w 0
      let b := Fin.tail w 0
      have hw' : w = Fin.cons a (Fin.cons b tail) := by simp only [a, b, tail, Fin.cons_self_tail]
      rw [hw']
      apply diagonal_isotropic_of_tail_cofinite a b (hw 0) (hw (Fin.succ 0)) tail
        (eventually_isotropic_diagonal tail (fun i => hw i.succ.succ))
      · intro p
        have hp := h p
        let A := Global.placeCompletion F p
        change ¬ (weightedSumSquares A (algebraMap F A ∘ w)).Anisotropic at hp
        rw [hw', Fin.comp_cons, Fin.comp_cons] at hp
        exact hp
      · intro c hc hl
        apply ih (Fin.cons c tail) (fun j => Fin.cases hc (fun i => hw i.succ.succ) j)
        intro p
        let A := Global.placeCompletion F p
        change ¬ (weightedSumSquares A (algebraMap F A ∘ Fin.cons c tail)).Anisotropic
        rw [Fin.comp_cons]
        exact hl p

end Langlands.QuadraticIsotropy
