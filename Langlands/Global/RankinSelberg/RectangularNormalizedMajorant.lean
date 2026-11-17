import Langlands.Global.RankinSelberg.RectangularGaugeNormalization
import Langlands.Global.RankinSelberg.AdelicRowMajorant

/-! # Joint Schwartz majorants after determinant normalization -/

noncomputable section
universe u
open NumberField
open scoped Classical Matrix.Norms.Elementwise NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open PrimitiveAdelicHeight Langlands.GeneralLinear.RectangularIwasawa EqualAnalytic

variable (F : Type u) [Field F] [NumberField F]

/-- The fixed nonnegative simple-root powers left after determinant
normalization of the gauge weight. -/
def rectangularRootPowerWeight (r : ℕ) (τ : ℝ) (c : Fin (r + 1) → Ideles F) : ℝ :=
  ∏ i : Fin r,
    (((IdeleAbsoluteValue.full F (gaugeSimpleRootIdeles F r c i) : ℝ≥0) : ℝ) ^
      ((i.val : ℝ) * τ))

private theorem rootPowerWeight_le_polynomial
    {r : ℕ} (c : Fin (r + 1) → Ideles F) (τ : ℝ) (hτ : 0 ≤ τ)
    (q : 𝓞 F) (hq : q ≠ 0)
    (hsupp : ∀ i : Fin r,
      algebraMap (𝓞 F) (FiniteAdeles F) q *
        ((gaugeSimpleRootIdeles F r c i : Ideles F) : Adeles F).2 ∈ integralFiniteAdeles F) :
    rectangularRootPowerWeight F r τ c ≤
      (1 + ‖archimedeanAdeleProjection F (diagonal F (q : F))‖) ^
          (Module.finrank ℚ F * (⌈(r : ℝ) * τ⌉₊ * r)) *
        (1 + ‖archimedeanCoordinates F r (gaugeSimpleRootRow F r c)‖) ^
          (Module.finrank ℚ F * (⌈(r : ℝ) * τ⌉₊ * r)) := by
  let Y := archimedeanCoordinates F r (gaugeSimpleRootRow F r c)
  let Q : ℝ := 1 + ‖archimedeanAdeleProjection F (diagonal F (q : F))‖
  let T : ℝ := 1 + ‖Y‖
  let M : ℕ := ⌈(r : ℝ) * τ⌉₊
  let B : ℝ := (Q * T) ^ Module.finrank ℚ F
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    linarith [norm_nonneg (archimedeanAdeleProjection F (diagonal F (q : F)))]
  have hT : 1 ≤ T := by dsimp [T]; linarith [norm_nonneg Y]
  have hB : 1 ≤ B := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hQ hT)
  have hqF : (q : F) ≠ 0 := by exact_mod_cast hq
  have hnorm (i : Fin r) :
      ((IdeleAbsoluteValue.full F (gaugeSimpleRootIdeles F r c i) : ℝ≥0) : ℝ) ≤ B := by
    have hi : algebraMap F (FiniteAdeles F) (q : F) *
        (gaugeSimpleRootIdeles F r c i : Adeles F).2 ∈ integralFiniteAdeles F := by
      rw [← IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeles F)]
      exact hsupp i
    apply (full_idele_norm_le_of_denominator F _ (q : F) hqF hi).trans
    have harch : ideleArchimedeanNorm F (gaugeSimpleRootIdeles F r c i) ≤ T :=
      (norm_le_pi_norm Y i).trans (by dsimp [T]; linarith)
    calc
      _ ≤ Q ^ Module.finrank ℚ F * T ^ Module.finrank ℚ F := by
        apply mul_le_mul
        · apply pow_le_pow_left₀ (norm_nonneg _)
          dsimp [Q]
          linarith
        · exact pow_le_pow_left₀ (norm_nonneg _) harch _
        · exact pow_nonneg (norm_nonneg _) _
        · exact pow_nonneg (zero_le_one.trans hQ) _
      _ = B := by dsimp [B]; rw [mul_pow]
  have hweight (i : Fin r) :
      (((IdeleAbsoluteValue.full F (gaugeSimpleRootIdeles F r c i) : ℝ≥0) : ℝ) ^
          ((i.val : ℝ) * τ)) ≤ B ^ M := by
    have hiτ : 0 ≤ (i.val : ℝ) * τ := mul_nonneg (Nat.cast_nonneg _) hτ
    have hiM : (i.val : ℝ) * τ ≤ (M : ℝ) :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast i.isLt.le) hτ).trans
        (Nat.le_ceil _)
    calc
      _ ≤ B ^ ((i.val : ℝ) * τ) :=
        Real.rpow_le_rpow (NNReal.coe_nonneg _) (hnorm i) hiτ
      _ ≤ B ^ (M : ℝ) := Real.rpow_le_rpow_of_exponent_le hB hiM
      _ = B ^ M := Real.rpow_natCast _ _
  unfold rectangularRootPowerWeight
  calc
    _ ≤ ∏ _i : Fin r, B ^ M :=
      Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _)
        (fun i _ => hweight i)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, B, ← pow_mul,
        mul_pow, Q, T, M, Y, Nat.mul_assoc]

private theorem joint_polynomial_estimate
    (X Y B A N : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hA : 0 ≤ A) (hN : 0 ≤ N) (E : ℕ)
    (hx : X ≤ A * (1 + Y) ^ E)
    (hb : B ≤ Y * (N * (1 + X)) ^ 2) :
    X ≤ (A + (N * (1 + A)) ^ 2 + 1) * (1 + Y) ^ (2 * E + 1) ∧
      B ≤ (A + (N * (1 + A)) ^ 2 + 1) * (1 + Y) ^ (2 * E + 1) := by
  let T : ℝ := 1 + Y
  let K : ℝ := N * (1 + A)
  have hT : 1 ≤ T := by dsimp [T]; linarith
  have hP : 1 ≤ T ^ E := one_le_pow₀ hT
  have hxp : 1 + X ≤ (1 + A) * T ^ E := by
    calc
      _ ≤ 1 + A * T ^ E := by dsimp only [T]; linarith
      _ ≤ T ^ E + A * T ^ E := by linarith
      _ = _ := by ring
  have hn : N * (1 + X) ≤ K * T ^ E := by
    calc
      _ ≤ N * ((1 + A) * T ^ E) := mul_le_mul_of_nonneg_left hxp hN
      _ = _ := by dsimp [K]; ring
  have hB : B ≤ K ^ 2 * T ^ (2 * E + 1) := by
    calc
      _ ≤ Y * (N * (1 + X)) ^ 2 := hb
      _ ≤ T * (K * T ^ E) ^ 2 := by
        apply mul_le_mul
        · dsimp [T]
          linarith
        · exact pow_le_pow_left₀ (mul_nonneg hN (by linarith)) hn 2
        · exact sq_nonneg _
        · exact zero_le_one.trans hT
      _ = _ := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm E 2, pow_succ]
        ring
  constructor
  · apply hx.trans
    calc
      _ ≤ A * T ^ (2 * E + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega)) hA
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (N * (1 + A))])
        (pow_nonneg (zero_le_one.trans hT) _)
  · apply hB.trans
    exact mul_le_mul_of_nonneg_right
      (by change (N * (1 + A)) ^ 2 ≤ _; linarith) (pow_nonneg (zero_le_one.trans hT) _)

private structure MajorantParameter (F : Type u) [Field F] [NumberField F] (t d : ℕ) where
  leading : Fin (t + 1) → Ideles F
  rectangle : Matrix (Fin d) (Fin (t + 1)) (Adeles F)
  unipotent : AdelicGL F (t + 1 + d + 1)
  compact : AdelicGL F (t + 1 + d + 1)
  correction : Fin (t + 1 + d + 1) → Ideles F
  unitriangular : IsUnitriangular unipotent.val
  compact_mem : compact ∈ standardCompact F (t + 1 + d + 1)
  factorization : GeneralLinear.lowerBlockLocalization 1 1 rectangle 1 =
    unipotent * diagonalGL correction * compact

private def majorantDiagonal {t d : ℕ} (p : MajorantParameter F t d) :
    Fin (t + 1 + d + 1) → Ideles F :=
  rectangularCorrectedDiagonal F p.leading p.correction

private def majorantRootRow {t d : ℕ} (p : MajorantParameter F t d) :
    RowVector F (t + 1 + d) :=
  gaugeSimpleRootRow F (t + 1 + d) (majorantDiagonal F p)

private def majorantJointRow {t d : ℕ} (p : MajorantParameter F t d) :
    RowVector F (t + 1 + d * (t + 1)) :=
  rectangularJointRow F (gaugeBlockRootIdeles F t p.leading) p.rectangle

private theorem majorant_joint_geometry (t d : ℕ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ p : MajorantParameter F t d,
      ‖archimedeanCoordinates F (t + 1 + d * (t + 1)) (majorantJointRow F p)‖ ≤
        G * (1 + ‖archimedeanCoordinates F (t + 1 + d) (majorantRootRow F p)‖) ^
          (2 * (d * (d + 1)) + 1) := by
  let A : ℝ := ((d + 1).factorial : ℝ)
  let N : ℝ := ((t + 1 + d + 1 : ℕ) : ℝ)
  let G : ℝ := A + (N * (1 + A)) ^ 2 + 1
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hG : 0 ≤ G := by dsimp [G]; positivity
  refine ⟨G, hG, ?_⟩
  intro p
  let X := rectangleArchimedeanCoordinates F d (t + 1) p.rectangle
  let Y := archimedeanCoordinates F (t + 1 + d) (majorantRootRow F p)
  let B := archimedeanCoordinates F (t + 1)
    (diagonalIdeleRow F (gaugeBlockRootIdeles F t p.leading))
  obtain ⟨V, hV, hfac⟩ := rectangular_corrected_factorization F p.rectangle
    p.unipotent p.compact p.correction p.unitriangular p.factorization p.leading
  have hx := rectangleArchimedeanCoordinates_norm_le F (diagonalGL p.leading) p.rectangle
    V p.compact (majorantDiagonal F p) hV p.compact_mem hfac
  have hx' : ‖X‖ ≤ A * (1 + ‖Y‖) ^ (d * (d + 1)) := by
    change ‖X‖ ≤ (1 + ‖Y‖) ^ (d * (d + 1)) * A at hx
    rwa [mul_comm] at hx
  have hc := diagonal_correction_archimedean_norm_le F p.rectangle p.unipotent p.compact
    p.correction p.unitriangular p.compact_mem p.factorization
  have hb : ‖B‖ ≤ ‖Y‖ * (N * (1 + ‖X‖)) ^ 2 :=
    leading_block_roots_archimedean_norm_le F (show t < t + 1 + d by omega)
      p.leading p.correction (N * (1 + ‖X‖)) (by positivity) hc.1 hc.2
  have hpoly := joint_polynomial_estimate ‖X‖ ‖Y‖ ‖B‖ A N
    (norm_nonneg _) (norm_nonneg _) hA hN (d * (d + 1)) hx' hb
  exact rectangularJointRow_archimedean_norm_le F _ _
    (G * (1 + ‖Y‖) ^ (2 * (d * (d + 1)) + 1))
    (mul_nonneg hG (pow_nonneg (by positivity) _)) hpoly.2 hpoly.1

private theorem majorant_joint_denominator
    {t d : ℕ} (p : MajorantParameter F t d) (q : 𝓞 F) (hq : q ≠ 0)
    (hsupp : ∀ i : Fin (t + 1 + d),
      algebraMap (𝓞 F) (FiniteAdeles F) q *
        finiteCoordinates F (t + 1 + d) (majorantRootRow F p) i ∈ integralFiniteAdeles F) :
    finiteCoordinates F (t + 1 + d * (t + 1)) (majorantJointRow F p) ∈
      SchwartzMajorant.denominatorRows F (t + 1 + d * (t + 1))
        ((q * (q ^ (d * (d + 1))) ^ 2 : 𝓞 F) : F) := by
  let s : FiniteAdeles F := algebraMap (𝓞 F) (FiniteAdeles F) (q ^ (d * (d + 1)))
  have hs : s ∈ integralFiniteAdeles F := algebraMap_ringOfIntegers_mem F _
  obtain ⟨V, hV, hfac⟩ := rectangular_corrected_factorization F p.rectangle
    p.unipotent p.compact p.correction p.unitriangular p.factorization p.leading
  have hx : ∀ i j, s * rectangleFiniteCoordinates F d (t + 1) p.rectangle i j ∈
      integralFiniteAdeles F :=
    rectangular_finite_denominator F (diagonalGL p.leading) p.rectangle V p.compact
      (majorantDiagonal F p) hV p.compact_mem hfac q hq hsupp
  have hc := finite_diagonal_correction_integral_multiple F p.rectangle p.unipotent p.compact
    p.correction p.unitriangular p.compact_mem p.factorization s hs hx
  have hb := leading_block_root_integral_multiple F (show t < t + 1 + d by omega)
    p.leading p.correction (algebraMap (𝓞 F) (FiniteAdeles F) q) s hsupp hc
  have hj := rectangularJointRow_finite_integral_multiple F _ p.rectangle
    (algebraMap (𝓞 F) (FiniteAdeles F) q) s (algebraMap_ringOfIntegers_mem F q) hs hb hx
  intro k
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeles F)]
  simpa only [map_mul, map_pow, s, majorantJointRow] using hj k

/-- A Schwartz function of the actual corrected roots, multiplied by the
fixed positive root powers, has a genuine Schwartz majorant in the
original leading roots and the rectangular entries jointly. -/
theorem exists_normalized_rectangular_joint_majorant
    [CompactSpace (AdeleQuotient F)] (t d : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (Φ : RowVector F (t + 1 + d) → ℂ) (hΦ : Φ ∈ schwartzBruhat F (t + 1 + d)) :
    ∃ Ψ : RowVector F (t + 1 + d * (t + 1)) → ℂ,
      Ψ ∈ schwartzBruhat F (t + 1 + d * (t + 1)) ∧
      ∀ (b : Fin (t + 1) → Ideles F)
        (x : Matrix (Fin d) (Fin (t + 1)) (Adeles F))
        (U K : AdelicGL F (t + 1 + d + 1)) (c : Fin (t + 1 + d + 1) → Ideles F),
        IsUnitriangular U.val → K ∈ standardCompact F (t + 1 + d + 1) →
        GeneralLinear.lowerBlockLocalization 1 1 x 1 = U * diagonalGL c * K →
          rectangularRootPowerWeight F (t + 1 + d) τ (rectangularCorrectedDiagonal F b c) *
              ‖Φ (gaugeSimpleRootRow F (t + 1 + d) (rectangularCorrectedDiagonal F b c))‖ ≤
            ‖Ψ (rectangularJointRow F (gaugeBlockRootIdeles F t b) x)‖ := by
  obtain ⟨q, hq, hsupp, hdecay⟩ := (schwartzBruhat_properties F (t + 1 + d) hΦ).2.2
  let J := MajorantParameter F t d
  let z : J → RowVector F (t + 1 + d * (t + 1)) := majorantJointRow F
  let w : J → ℝ := fun p =>
    rectangularRootPowerWeight F (t + 1 + d) τ (majorantDiagonal F p) *
      ‖Φ (majorantRootRow F p)‖
  let Q : ℝ := 1 + ‖archimedeanAdeleProjection F (diagonal F (q : F))‖
  let P : ℕ := Module.finrank ℚ F * (⌈((t + 1 + d : ℕ) : ℝ) * τ⌉₊ * (t + 1 + d))
  let D : ℕ := 2 * (d * (d + 1)) + 1
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hw : ∀ p, 0 ≤ w p := by
    intro p
    exact mul_nonneg
      (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _))
      (norm_nonneg _)
  have hwbound (p : J) :
      w p ≤ (Q ^ P * (1 + ‖archimedeanCoordinates F (t + 1 + d)
        (majorantRootRow F p)‖) ^ P) * ‖Φ (majorantRootRow F p)‖ := by
    by_cases hp : Φ (majorantRootRow F p) = 0
    · simp only [w, hp, norm_zero, mul_zero, le_refl]
    · have hh := rootPowerWeight_le_polynomial F (majorantDiagonal F p) τ hτ q hq
        (hsupp (majorantRootRow F p) hp)
      exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)
  obtain ⟨G, hG, hgeometry⟩ := majorant_joint_geometry F t d
  have hrapid : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ p, (1 + ‖archimedeanCoordinates F (t + 1 + d * (t + 1)) (z p)‖) ^ N * w p ≤ C := by
    intro N
    obtain ⟨C, hC⟩ := hdecay (D * N + P)
    let A : ℝ := (1 + G) ^ N * Q ^ P
    have hA : 0 ≤ A := mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg hQ _)
    refine ⟨A * max C 0, mul_nonneg hA (le_max_right _ _), ?_⟩
    intro p
    let T : ℝ := 1 + ‖archimedeanCoordinates F (t + 1 + d) (majorantRootRow F p)‖
    have hT : 1 ≤ T := by
      dsimp [T]
      linarith [norm_nonneg (archimedeanCoordinates F (t + 1 + d) (majorantRootRow F p))]
    have hz :
        1 + ‖archimedeanCoordinates F (t + 1 + d * (t + 1)) (z p)‖ ≤ (1 + G) * T ^ D := by
      have hg := hgeometry p
      change ‖archimedeanCoordinates F (t + 1 + d * (t + 1)) (z p)‖ ≤ G * T ^ D at hg
      have hp := one_le_pow₀ (n := D) hT
      nlinarith
    have hdec : T ^ (D * N + P) * ‖Φ (majorantRootRow F p)‖ ≤ max C 0 :=
      (hC (majorantRootRow F p)).trans (le_max_left _ _)
    calc
      _ ≤ ((1 + G) * T ^ D) ^ N *
          ((Q ^ P * T ^ P) * ‖Φ (majorantRootRow F p)‖) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hz N) (hwbound p) (hw p)
          (pow_nonneg (mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hT) _)) _)
      _ = A * (T ^ (D * N + P) * ‖Φ (majorantRootRow F p)‖) := by
        dsimp only [A]
        rw [mul_pow, ← pow_mul, pow_add]
        ring
      _ ≤ A * max C 0 := mul_le_mul_of_nonneg_left hdec hA
  let qjoint : 𝓞 F := q * (q ^ (d * (d + 1))) ^ 2
  have hqjoint : (qjoint : F) ≠ 0 := by
    have hh : qjoint ≠ 0 := mul_ne_zero hq (pow_ne_zero 2 (pow_ne_zero _ hq))
    exact_mod_cast hh
  have hfinite : ∀ p, w p ≠ 0 →
      finiteCoordinates F (t + 1 + d * (t + 1)) (z p) ∈
        SchwartzMajorant.denominatorRows F (t + 1 + d * (t + 1)) (qjoint : F) := by
    intro p hp
    have hpΦ : Φ (majorantRootRow F p) ≠ 0 := by
      intro hh
      apply hp
      simp only [w, hh, norm_zero, mul_zero]
    exact majorant_joint_denominator F p q hq (hsupp (majorantRootRow F p) hpΦ)
  obtain ⟨Ψ, hΨ, hbound, -⟩ :=
    SchwartzMajorant.exists_schwartzBruhat_majorant F z w hw hrapid (qjoint : F) hqjoint hfinite
  refine ⟨Ψ, hΨ, ?_⟩
  intro b x U K c hU hK hfac
  exact hbound ⟨b, x, U, K, c, hU, hK, hfac⟩

end Langlands.Global.RankinSelbergGlobal
