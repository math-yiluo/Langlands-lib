import Langlands.Global.RankinSelberg.EqualAnalyticUnfolding
import Langlands.Global.RankinSelberg.EqualAnalyticThetaBound
import Langlands.Global.RankinSelberg.UnequalAnalyticDecay
import Langlands.Automorphic.OperatorDeterminantSliceMeasure

/-! # Finiteness of integrals over `GL_n(F) \ GL_n(𝔸)` from bounds in Siegel coordinates

Fix a Siegel decomposition `γ g = A(x) q` (`q` in a compact `Q₁`, `x` in a chamber).

* `finite_cover_of_siegel`: there is a measurable set `t` meeting every rational orbit such that
  `∫_t w < ∞` for every `w ≥ 0` with `w(A(x) q) ≤ C e^(-D(x)) e^(-|Σ x|)` on the chamber, where
  `D(x) = Σ |x_i - x̄|`.
* `lintegral_quotient_lt_top_of_siegel`: the same bound for a `GL_n(F)`-invariant `w` on
  `GL_n(𝔸)` gives `∫_(GL_n(F)\GL_n(𝔸)) w < ∞`.
* `exists_region_bound`: a function `|P| |det|^σ V` restricted to `|det| ≥ 1` or `|det| < 1`
  satisfies that bound when `|P|` has chamber decay of rate `A₀`, `V(A(x) q) ≤ K e^(N D) e^(β Σ x)`
  and `σ [F:ℚ] + β` is suitably large or small.
* Theta factors satisfy such bounds (`exists_thetaNorm_chamber_le`,
  `exists_thetaNorm_inverseTranspose_chamber_le`).
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global Langlands.Automorphic
open scoped CategoryTheory.MonObj Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance coverSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance coverSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

/-- The chamber spread `D(x) = Σ |x_i - x̄|`. -/
abbrev spread (x : Fin n → ℝ) : ℝ := ∑ i, |x i - (∑ j, x j) / n|

/-- The archimedean torus element `A(x)`. -/
abbrev torusA (x : Fin n → ℝ) : AdelicGL F n := AdelicGL.ofInfinite F n (torInf F n x)

/-- **A finite cover from a Siegel decomposition.** -/
theorem finite_cover_of_siegel [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
    {Q₁ : Set (AdelicGL F n)} {K : ℝ} (hQ₁ : IsCompact Q₁)
    (hdec : ∀ g : AdelicGL F n, ∃ (c : RationalGL F n) (x : Fin n → ℝ) (q : AdelicGL F n),
        q ∈ Q₁ ∧ AdelicGL.rational F n c * g = torusA (F := F) x * q ∧
          CuspidalL2.Chamber K x) :
    ∃ t : Set (AdelicGL F n), MeasurableSet t ∧
      (∀ g : AdelicGL F n, ∃ c : RationalGL F n, AdelicGL.rational F n c * g ∈ t) ∧
      ∀ (w : AdelicGL F n → ℝ≥0∞) (C : ℝ),
        (∀ x : Fin n → ℝ, CuspidalL2.Chamber (K + 2) x → ∀ q ∈ Q₁,
          w (torusA (F := F) x * q) ≤
            ENNReal.ofReal (C * Real.exp (-spread x) * Real.exp (-|∑ i, x i|))) →
        ∀ (ν : Measure (AdelicGL F n)) [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν],
          ∫⁻ x in t, w x ∂ν < ⊤ := by
  have := adelicGL_t2Space F n
  obtain ⟨Q₂, hQ₂def⟩ : ∃ Q₂ : Set (AdelicGL F n), (fun p : (Fin n → ℝ) × AdelicGL F n =>
      torusA (F := F) p.1 * p.2) '' ((Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) ×ˢ Q₁) = Q₂ :=
    ⟨_, rfl⟩
  have hQ₂ : IsCompact Q₂ := hQ₂def ▸ ((isCompact_univ_pi fun _ => isCompact_Icc).prod hQ₁).image
    (((map_continuous (AdelicGL.ofInfinite F n)).comp
      ((continuous_torInf F n).comp continuous_fst)).mul continuous_snd)
  let J := {m : Fin n → ℤ // CuspidalL2.Chamber (K + 1) (fun i => (m i : ℝ))}
  let a : J → AdelicGL F n := fun m => torusA (F := F) fun i => (m.1 i : ℝ)
  refine ⟨CuspidalL2.leftTranslateCover a Q₂,
    CuspidalL2.measurableSet_leftTranslateCover a hQ₂, ?_, ?_⟩
  · intro g
    obtain ⟨c, x, q, hq, hc, hx⟩ := hdec g
    have hfl := (CuspidalL2.floor_chamber x hx le_rfl).1
    have hxy : (fun i => ((⌊x i⌋ : ℤ) : ℝ)) + (fun i => Int.fract (x i)) = x :=
      funext fun i => Int.floor_add_fract (x i)
    refine ⟨c, Set.mem_iUnion.mpr ⟨⟨fun i => ⌊x i⌋, hfl⟩,
      torusA (F := F) (fun i => Int.fract (x i)) * q,
      hQ₂def ▸ ⟨(fun i => Int.fract (x i), q),
        ⟨fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, hq⟩, rfl⟩, ?_⟩⟩
    show torusA (F := F) (fun i => ((⌊x i⌋ : ℤ) : ℝ)) *
      (torusA (F := F) (fun i => Int.fract (x i)) * q) = AdelicGL.rational F n c * g
    rw [hc, ← mul_assoc, ← map_mul, ← torInf_add, hxy]
  · intro w C hw ν _ _
    let b : J → ℝ≥0∞ := fun m => ENNReal.ofReal
      (|C| * Real.exp n * Real.exp (-(∑ i, |((m.1 i : ℤ) : ℝ)|)))
    refine CuspidalL2.lintegral_leftTranslateCover_lt_top ν a Q₂ hQ₂.measure_lt_top _ b ?_ ?_
    · intro m z hz
      rw [← hQ₂def] at hz
      obtain ⟨p, hp, hpz⟩ := hz
      have hpz' : torusA (F := F) p.1 * p.2 = z := hpz
      obtain ⟨hX, -, hXm⟩ := CuspidalL2.shift_chamber (R := |∑ i, ((m.1 i : ℤ) : ℝ)|)
        (fun i => ((m.1 i : ℤ) : ℝ)) p.1 (fun i => hp.1 i (Set.mem_univ i)) m.2
        (le_add_of_nonneg_right (Nat.cast_nonneg n))
      obtain ⟨X, hXdef⟩ : ∃ X : Fin n → ℝ, (fun i => ((m.1 i : ℤ) : ℝ)) + p.1 = X := ⟨_, rfl⟩
      rw [hXdef] at hX hXm
      have heq : a m * z = torusA (F := F) X * p.2 := by
        rw [← hpz']
        show torusA (F := F) (fun i => ((m.1 i : ℤ) : ℝ)) * (torusA (F := F) p.1 * p.2) = _
        rw [← mul_assoc, ← map_mul, ← torInf_add, hXdef]
      have hb := hw X hX p.2 hp.2
      have hl1 := UnequalAnalytic.sum_abs_le_sum_abs_sub_mean X
      rw [heq]
      refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : -spread X + -|∑ i, X i| ≤ n + -(∑ i, |((m.1 i : ℤ) : ℝ)|) := by
        simp only [spread]
        linarith
      calc C * Real.exp (-spread X) * Real.exp (-|∑ i, X i|)
          ≤ |C| * Real.exp (-spread X + -|∑ i, X i|) := by
            rw [Real.exp_add, ← mul_assoc]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
              (Real.exp_pos _).le) (Real.exp_pos _).le
        _ ≤ |C| * Real.exp (n + -(∑ i, |((m.1 i : ℤ) : ℝ)|)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) (abs_nonneg _)
        _ = |C| * Real.exp n * Real.exp (-(∑ i, |((m.1 i : ℤ) : ℝ)|)) := by
            rw [Real.exp_add]; ring
    · have hsum := UnequalAnalytic.summable_lattice_bound (fun m : Fin n → ℤ =>
        CuspidalL2.Chamber (K + 1) (fun i => (m i : ℝ))) (|C| * Real.exp n)
      have hb : (∑' m, b m) = ENNReal.ofReal (∑' m : J,
          |C| * Real.exp n * Real.exp (-(∑ i, |((m.1 i : ℤ) : ℝ)|))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum).symm
      rw [hb]
      exact ENNReal.ofReal_lt_top

local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F

/-- **Finiteness on the quotient from a bound in Siegel coordinates.** -/
theorem lintegral_quotient_lt_top_of_siegel {Q₁ : Set (AdelicGL F n)} {K : ℝ}
    (hQ₁ : IsCompact Q₁)
    (hdec : ∀ g : AdelicGL F n, ∃ (c : RationalGL F n) (x : Fin n → ℝ) (q : AdelicGL F n),
        q ∈ Q₁ ∧ AdelicGL.rational F n c * g = torusA (F := F) x * q ∧
          CuspidalL2.Chamber K x)
    (w : Points F n → ℝ≥0∞) (hw : Measurable w)
    (hwr : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      w (AdelicGroupPoints.rational F (Scheme F n) c * g) = w g) (C : ℝ)
    (hb : ∀ x : Fin n → ℝ, CuspidalL2.Chamber (K + 2) x → ∀ q ∈ Q₁,
      w ((e n).symm (torusA (F := F) x * q)) ≤
        ENNReal.ofReal (C * Real.exp (-spread x) * Real.exp (-|∑ i, x i|))) :
    ∫⁻ y, w (Quotient.out y)
      ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) < ⊤ := by
  let : MeasurableSpace (AdelicGL F n) := borel _
  have : BorelSpace (AdelicGL F n) := ⟨rfl⟩
  obtain ⟨t, ht, hcov, hint⟩ := finite_cover_of_siegel (F := F) hQ₁ hdec
  have : (Measure.map (e n) (Measure.haar : Measure (Points F n))).IsHaarMeasure :=
    (e n).isHaarMeasure_map Measure.haar
  have hfin := hint (fun M => w ((e n).symm M)) C hb (Measure.map (e n) Measure.haar)
  let Γ := AdelicGroupPoints.rationalSubgroup F (Scheme F n)
  have hΓ := AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F n)
  have hw' : ∀ (c : Γ) (x : Points F n), w ((c : Points F n) * x) = w x := by
    rintro ⟨_, c, rfl⟩ x
    exact hwr c x
  have hfun : (fun y : AdelicGroupPoints.RationalQuotient F (Scheme F n) => w (Quotient.out y)) =
      LeftCosetSpace.lift Γ w hw' := funext fun y => (UnequalAnalytic.lift_eq_out Γ w hw' y).symm
  have hliftm : Measurable (LeftCosetSpace.lift Γ w hw') := measurable_from_quotient.2 hw
  have hcov' : ∀ x : Points F n, LeftCosetSpace.mk Γ x ∈ Set.univ →
      ∃ c : Γ, (c : Points F n) * x ∈ (e n) ⁻¹' t := by
    intro x _
    obtain ⟨c, hc⟩ := hcov (e n x)
    let c' := (GeneralLinearGroupPoints.rationalEquiv F n).symm c
    refine ⟨⟨AdelicGroupPoints.rational F (Scheme F n) c', ⟨c', rfl⟩⟩, ?_⟩
    change e n (AdelicGroupPoints.rational F (Scheme F n) c' * x) ∈ t
    simpa only [c', map_mul, GeneralLinearGroupPoints.adelicHomeomorph_rational,
      MulEquiv.apply_symm_apply] using hc
  have hle := LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le Γ hΓ
    Measure.haar Set.univ MeasurableSet.univ ((e n) ⁻¹' t)
    (ht.preimage (e n).continuous.measurable) hcov' (LeftCosetSpace.lift Γ w hw') hliftm
  rw [Measure.restrict_univ] at hle
  rw [hfun]
  refine hle.trans_lt (lt_of_eq_of_lt ?_ hfin)
  have hGm : Measurable fun M : AdelicGL F n => w ((e n).symm M) :=
    hw.comp (e n).symm.continuous.measurable
  have hem : Measurable fun x : Points F n => e n x := (e n).continuous.measurable
  rw [← lintegral_indicator ht _, lintegral_map (hGm.indicator ht) hem,
    ← lintegral_indicator (ht.preimage hem) _]
  refine lintegral_congr fun x => ?_
  simp only [Set.indicator, Set.mem_preimage, LeftCosetSpace.lift_mk,
    ContinuousMulEquiv.symm_apply_apply]
  rfl

/-! ### Exponent bookkeeping -/

omit [NumberField F] in
/-- On `Σ x ≥ -b`, a sufficiently negative linear term dominates. -/
theorem exponent_le_of_ge {S A₀ α b : ℝ} (hb : 0 ≤ b) (hA₀ : 0 ≤ A₀) (hS : -b ≤ S)
    (hα : α + A₀ ≤ -1) : A₀ * |S| + α * S ≤ -|S| + (|α| + A₀ + 1) * b := by
  rcases le_or_gt 0 S with h | h
  · rw [abs_of_nonneg h]
    have : (α + A₀ + 1) * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h
    nlinarith [abs_nonneg α]
  · rw [abs_of_neg h]
    have h1 : α * S ≤ |α| * b := by
      calc α * S ≤ |α * S| := le_abs_self _
        _ = |α| * (-S) := by rw [abs_mul, abs_of_neg h]
        _ ≤ |α| * b := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    nlinarith

omit [NumberField F] in
/-- On `Σ x ≤ b`, a sufficiently positive linear term dominates. -/
theorem exponent_le_of_le {S A₀ α b : ℝ} (hb : 0 ≤ b) (hA₀ : 0 ≤ A₀) (hS : S ≤ b)
    (hα : 1 ≤ α - A₀) : A₀ * |S| + α * S ≤ -|S| + (|α| + A₀ + 1) * b := by
  have h := exponent_le_of_ge (S := -S) (α := -α) hb hA₀ (by linarith) (by linarith)
  rw [abs_neg, abs_neg] at h
  linarith

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
