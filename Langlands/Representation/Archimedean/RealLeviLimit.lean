import Langlands.Representation.Archimedean.JacquetLimit
import Langlands.Representation.Archimedean.RealLeviTorus
import Langlands.Representation.Archimedean.RealLeviChartIntegralStatement
import Langlands.Representation.Archimedean.RealLeviParabolicIntegrationStatement

/-!
# The limit argument along a standard parabolic subgroup `Q` of `GL_N(ℝ)`, torus averaged

Let `ds` be a list of real blocks of rank `N = ∑ sz_i` whose block exponents `t_p` decrease weakly
along the positions and strictly from one block of `Q` to the next. Let `u` lie in the principal
series of the inverse characters and `h` in the standard module of `ds`, both `O(N)`-finite. If
`∫_{O(N)} u(κ g) h(κ) dκ = 0` for every `g`, then
`∫_{K_M} ∫_{N̄_Q} c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ))) dX dκ = 0`, where `c_Z` is the iterated
mode-`0` torus coefficient over the induction blocks of `ds` (`RealLeviLimitStatement`), assuming
the integrability statement `RealLeviChartIntegrableStatement` and the integration formula
`RealLeviParabolicIntegrationStatement`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviLimit

open RealInducedBlockBound RealInducedTorusCore RealLeviChart GramFormula RealLeviTorus

/-! ## Continuity -/

section Cont

variable {c : ℕ} {sz : Fin c → ℕ}

theorem continuous_lower : Continuous (RealLeviChart.lower sz) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [RealLeviChart.lower, Matrix.of_apply]
  split_ifs
  all_goals first | exact continuous_apply _ | exact continuous_const

theorem lower_zero : RealLeviChart.lower sz 0 = 1 := by
  ext p q
  simp only [RealLeviChart.lower, Matrix.of_apply, Pi.zero_apply, Matrix.one_apply]
  split_ifs with h1 h2
  · subst h2
    exact absurd h1 (lt_irrefl _)
  · rfl
  · rfl
  · rfl

theorem lowerGL_zero : lowerGL sz 0 = 1 := by
  ext : 1
  rw [lowerGL_val, lower_zero, Units.val_one]

theorem lowerGL_inv_val (X : Coord sz → ℝ) :
    (((lowerGL sz X)⁻¹ : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
      Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) = (RealLeviChart.lower sz X).adjugate := by
  rw [Matrix.coe_units_inv, lowerGL_val, Matrix.inv_def, det_lower, Ring.inverse_one, one_smul]

theorem continuous_lowerGL : Continuous (lowerGL sz) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_lower.congr fun X => (lowerGL_val sz X).symm, ?_⟩
  exact (continuous_lower.matrix_adjugate).congr fun X => (lowerGL_inv_val X).symm

theorem continuous_adCoord_prod :
    Continuous fun p : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ × (Coord sz → ℝ) =>
      adCoord p.1 p.2 := by
  refine continuous_pi fun pq => ?_
  simp only [adCoord]
  exact ((continuous_fst.matrix_mul (continuous_lower.comp continuous_snd)).matrix_mul
    continuous_fst.matrix_transpose).matrix_elem _ _

theorem continuous_scaleCoord (s : ℝ) : Continuous (scaleCoord sz s) :=
  continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem continuous_gram {α : Type*} [TopologicalSpace α] {n : ℕ}
    {M : α → Matrix (Fin n) (Fin n) ℝ} (hM : Continuous M) (l : ℕ) :
    Continuous fun a => GramFormula.gram l (M a) := by
  unfold GramFormula.gram
  refine Continuous.matrix_det ?_
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [paddedGram, Matrix.of_apply]
  split_ifs
  · exact (hM.matrix_mul hM.matrix_transpose).matrix_elem p q
  · exact continuous_const

/-- The Gram bound `X ↦ ∏_l G_l(n̄(X))^{γ_l}`. -/
def gramBound (γ : Fin (∑ i, sz i) → ℝ) (X : Coord sz → ℝ) : ℝ :=
  ∏ l : Fin (∑ i, sz i), GramFormula.gram (l : ℕ) (RealLeviChart.lower sz X) ^ γ l

theorem continuous_gramBound (γ : Fin (∑ i, sz i) → ℝ) : Continuous (gramBound (sz := sz) γ) :=
  continuous_finsetProd _ fun l _ =>
    (continuous_gram continuous_lower (l : ℕ)).rpow_const fun X =>
      Or.inl (zero_lt_one.trans_le (one_le_gram_lower sz X l)).ne'

theorem gramBound_nonneg (γ : Fin (∑ i, sz i) → ℝ) (X : Coord sz → ℝ) :
    0 ≤ gramBound γ X :=
  Finset.prod_nonneg fun l _ =>
    Real.rpow_nonneg (zero_le_one.trans (one_le_gram_lower sz X l)) _

theorem gramBound_le_one {γ : Fin (∑ i, sz i) → ℝ} (hγ : ∀ l, γ l ≤ 0) (X : Coord sz → ℝ) :
    gramBound γ X ≤ 1 :=
  Finset.prod_le_one₀ (fun l _ => Real.rpow_nonneg (zero_le_one.trans
    (one_le_gram_lower sz X l)) _) fun l _ =>
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_gram_lower sz X l) (hγ l)

theorem continuous_of_mem_unitaryCompact {α : Type*} [TopologicalSpace α] {n : ℕ}
    {f : α → Langlands.GeneralLinear n ℝ}
    (hf : Continuous fun a => ((f a : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ))
    (h : ∀ a, f a ∈ unitaryCompact ℝ n) : Continuous f := by
  rw [Units.continuous_iff]
  refine ⟨hf, ?_⟩
  have hinv : ∀ a, (((f a)⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      ((f a : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ := fun a =>
    Units.inv_eq_of_mul_eq_one_right
      (mul_eq_one_comm.mp (transpose_mul_self_of_mem_unitaryCompact (h a)))
  exact hf.matrix_transpose.congr fun a => (hinv a).symm

/-- `diag(κ_0, …, κ_{c-1})` for `κ ∈ K_M = ∏_i O(sz_i)`. -/
def bdK (sz : Fin c → ℕ) (κ : ∀ i, unitaryCompact ℝ (sz i)) :
    Langlands.GeneralLinear (∑ i, sz i) ℝ :=
  blockDiagGL sz fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ)

theorem bdK_mem_blockOrth (κ : ∀ i, unitaryCompact ℝ (sz i)) : bdK sz κ ∈ blockOrth sz :=
  blockDiagGL_mem_blockOrth κ

theorem continuous_bdK : Continuous (bdK sz) := by
  refine continuous_of_mem_unitaryCompact ?_ fun κ => blockDiagGL_mem_unitaryCompact κ
  have : ∀ κ : ∀ i, unitaryCompact ℝ (sz i),
      ((bdK sz κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
        Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun i =>
          ((κ i : Langlands.GeneralLinear (sz i) ℝ) : Matrix (Fin (sz i)) (Fin (sz i)) ℝ)) :=
    fun κ => rfl
  refine Continuous.congr ?_ fun κ => (this κ).symm
  exact (Continuous.matrix_blockDiagonal' (continuous_pi fun i =>
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply i)))).matrix_reindex
      _ _

theorem continuous_integrand {α : Type*} [TopologicalSpace α]
    {F : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ} (hF : Continuous F)
    {g : α → Langlands.GeneralLinear (∑ i, sz i) ℝ} {X : α → Coord sz → ℝ}
    {κ : α → ∀ i, unitaryCompact ℝ (sz i)} (hg : Continuous g) (hX : Continuous X)
    (hκ : Continuous κ) :
    Continuous fun a => F (g a * (lowerGL sz (X a) * bdK sz (κ a))) :=
  hF.comp (hg.mul ((continuous_lowerGL.comp hX).mul (continuous_bdK.comp hκ)))

end Cont

/-! ## Limits and bounds -/

section Bounds

variable {c : ℕ} {sz : Fin c → ℕ}

theorem tendsto_scaleCoord (X : Coord sz → ℝ) :
    Tendsto (fun n : ℕ => scaleCoord sz ((n : ℝ) + 1) X) atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro pq
  have hlt : (cls sz pq.1.2 : ℕ) < (cls sz pq.1.1 : ℕ) := pq.2
  have key : ∀ n : ℕ, scaleCoord sz ((n : ℝ) + 1) X pq =
      (((n : ℝ) + 1) ^ ((cls sz pq.1.1 : ℕ) - (cls sz pq.1.2 : ℕ)))⁻¹ * X pq := by
    intro n
    have hpos : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [scaleCoord, scaleVec]
    rw [pow_sub₀ _ hpos hlt.le, mul_inv, inv_inv, div_eq_mul_inv,
      mul_comm (((n : ℝ) + 1) ^ (cls sz pq.1.2 : ℕ))]
  simp_rw [key]
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h2 := (tendsto_inv_atTop_zero.comp
    ((tendsto_pow_atTop (Nat.sub_ne_zero_of_lt hlt)).comp h1)).mul_const (X pq)
  simpa only [zero_mul, Function.comp_def, Pi.zero_apply] using h2

theorem tendsto_lowerGL_scale (X : Coord sz → ℝ) (k : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
    Tendsto (fun n : ℕ => lowerGL sz (scaleCoord sz ((n : ℝ) + 1) X) * k) atTop (𝓝 k) := by
  have h := ((continuous_lowerGL (sz := sz)).tendsto 0).comp (tendsto_scaleCoord X)
  rw [lowerGL_zero] at h
  simpa only [one_mul, Function.comp_def] using h.mul_const k

/-- A continuous function is bounded on `O(N) g_n` for a convergent sequence `g_n`. -/
theorem exists_bound_mul_tendsto {N : ℕ} {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : Continuous F) {g : ℕ → Langlands.GeneralLinear N ℝ} {g0 : Langlands.GeneralLinear N ℝ}
    (hg : Tendsto g atTop (𝓝 g0)) :
    ∃ M : ℝ, ∀ k ∈ unitaryCompact ℝ N, ∀ n, ‖F (k * g n)‖ ≤ M := by
  have hK : IsCompact (unitaryCompact ℝ N : Set (Langlands.GeneralLinear N ℝ)) := by
    have := isCompact_range (continuous_subtype_val :
      Continuous fun k : unitaryCompact ℝ N => (k : Langlands.GeneralLinear N ℝ))
    simpa using this
  obtain ⟨M, hM⟩ := (hK.prod hg.isCompact_insert_range).exists_bound_of_continuousOn
    ((hF.comp (continuous_fst.mul continuous_snd)).continuousOn)
  exact ⟨M, fun k hk n => hM (k, g n) ⟨hk, Set.mem_insert_of_mem _ ⟨n, rfl⟩⟩⟩

/-- Growth bound along `n̄(Y) κ` in terms of Gram determinants. -/
theorem norm_le_gram_lower {F : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    {c' : (Fin (∑ i, sz i) → ℝˣ) → ℂ} {σ : ℕ → ℝ}
    (hF : ∀ (a : Fin (∑ i, sz i) → ℝˣ) (u : upperUnipotent (∑ i, sz i) ℝ)
      (g : Langlands.GeneralLinear (∑ i, sz i) ℝ),
      F ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear (∑ i, sz i) ℝ) *
        (u : Langlands.GeneralLinear (∑ i, sz i) ℝ) * g) = c' a * F g)
    (hc : ∀ a, ‖c' a‖ = ∏ l : Fin (∑ i, sz i), |(a l : ℝ)| ^ σ l)
    {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℝ (∑ i, sz i), ‖F k‖ ≤ C)
    (Y : Coord sz → ℝ) {κ : Langlands.GeneralLinear (∑ i, sz i) ℝ}
    (hκ : κ ∈ unitaryCompact ℝ (∑ i, sz i)) (ε : Fin (∑ i, sz i) → ℝ)
    (hε : ∀ l : Fin (∑ i, sz i), 0 < (l : ℕ) → ε l = (σ l - σ ((l : ℕ) - 1)) / 2) :
    ‖F (lowerGL sz Y * κ)‖ ≤ C * gramBound ε Y :=
  norm_le_gram_fin hF hc hC (lowerGL sz Y)
    (by rw [lowerGL_val, gram_zero_eq, det_lower, one_pow]) hκ ε hε

open PartialJacquet RealInducedStandardBound in
theorem isSignedPower_absChar (e : ℕ → ℝ) :
    IsSignedPower (absChar e) fun l => ((e l : ℝ) : ℂ) where
  eq := absChar_eq e
  one l := by simp [absChar]
  norm_neg_one l := by simp [absChar]

open PartialJacquet RealInducedStandardBound in
/-- `‖E^e(n̄(Y) κ)‖ ≤ ∏_l G_l(n̄(Y))^{(e_l − e_{l−1} − 1)/2}`. -/
theorem norm_expFun_le (e : ℕ → ℝ) (Y : Coord sz → ℝ) {κ : Langlands.GeneralLinear (∑ i, sz i) ℝ}
    (hκ : κ ∈ unitaryCompact ℝ (∑ i, sz i)) (ε : Fin (∑ i, sz i) → ℝ)
    (hε : ∀ l : Fin (∑ i, sz i), 0 < (l : ℕ) → ε l = (e l - e ((l : ℕ) - 1) - 1) / 2) :
    ‖expFun (∑ i, sz i) e (lowerGL sz Y * κ)‖ ≤ gramBound ε Y := by
  have h := norm_le_gram_lower
    (σ := fun l : ℕ => e l + (((∑ i, sz i : ℕ) : ℝ) - 1) / 2 - (l : ℝ))
    (expFun_mem (∑ i, sz i) e).2
    (fun a => by
      rw [norm_principalSeriesCharacter (isSignedPower_absChar e)]
      refine Finset.prod_congr rfl fun l _ => ?_
      simp only [Complex.ofReal_re])
    (C := 1) (fun k hk => by
      have := expFun_mul (∑ i, sz i) e 1 hk
      rw [one_mul] at this
      rw [this, expFun_one, norm_one])
    Y hκ ε (fun l hl => by
      rw [hε l hl]
      simp only [Nat.cast_sub (show 1 ≤ (l : ℕ) by omega), Nat.cast_one]
      ring)
  simpa only [one_mul] using h

/-- Growth bound for modulus covariant functions: exponent `−1` at every Gram determinant. -/
theorem norm_modulusCovariant_le {F : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hF : MaximalParabolicIntegration.IsModulusCovariant F)
    {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℝ (∑ i, sz i), ‖F k‖ ≤ C)
    (Y : Coord sz → ℝ) {κ : Langlands.GeneralLinear (∑ i, sz i) ℝ}
    (hκ : κ ∈ unitaryCompact ℝ (∑ i, sz i)) :
    ‖F (lowerGL sz Y * κ)‖ ≤ C * gramBound (fun _ => -1) Y :=
  norm_le_gram_lower (σ := fun l : ℕ => (((∑ i, sz i : ℕ) : ℝ) - 1) - 2 * (l : ℝ)) hF
    (JacquetLimit.norm_modulusCharacter _) hC Y hκ (fun _ => -1) fun l hl => by
      simp only [Nat.cast_sub (show 1 ≤ (l : ℕ) by omega), Nat.cast_one]
      ring

/-- The exponents `γ_l = max((t_{l−1} − t_l − 1)/2, 0) + (t_l − t_{l−1} − 1)/2` (`γ_0 = −1`). -/
def gammaExp (t : ℕ → ℝ) (l : ℕ) : ℝ :=
  if l = 0 then -1 else max ((t (l - 1) - t l - 1) / 2) 0 + (t l - t (l - 1) - 1) / 2

theorem gammaExp_le (t : ℕ → ℝ) {l : ℕ} (hl : 0 < l) (ht : t l ≤ t (l - 1)) :
    gammaExp t l ≤ -(1 / 2) := by
  simp only [gammaExp, hl.ne', ↓reduceIte]
  rcases le_or_gt 0 ((t (l - 1) - t l - 1) / 2) with h | h
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right h.le]
    linarith

theorem gammaExp_lt (t : ℕ → ℝ) {l : ℕ} (hl : 0 < l) (ht : t l < t (l - 1)) :
    gammaExp t l < -(1 / 2) := by
  simp only [gammaExp, hl.ne', ↓reduceIte]
  rcases le_or_gt 0 ((t (l - 1) - t l - 1) / 2) with h | h
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right h.le]
    linarith

theorem gammaExp_nonpos (t : ℕ → ℝ) (ht : ∀ l : ℕ, 0 < l → t l ≤ t (l - 1)) (l : ℕ) :
    gammaExp t l ≤ 0 := by
  rcases Nat.eq_zero_or_pos l with h | h
  · simp only [gammaExp, h, ↓reduceIte]
    norm_num
  · linarith [gammaExp_le t h (ht l h)]

/-- **Domination.** For `s ≥ 1`,
`∏ G_l(n̄(Y_s))^{ε^u_l} ∏ G_l(n̄(Y))^{ε^h_l} ≤ ∏ G_l(n̄(Y))^{γ_l}` with
`ε^u_l = (t_{l−1} − t_l − 1)/2` and `ε^h_l = (t_l − t_{l−1} − 1)/2`. -/
theorem gramBound_mul_le (t : ℕ → ℝ) {s : ℝ} (hs : 1 ≤ s) (Y : Coord sz → ℝ) :
    gramBound (fun l : Fin (∑ i, sz i) => (t ((l : ℕ) - 1) - t l - 1) / 2)
        (scaleCoord sz s Y) *
      gramBound (fun l : Fin (∑ i, sz i) => (t l - t ((l : ℕ) - 1) - 1) / 2) Y ≤
      gramBound (fun l : Fin (∑ i, sz i) => gammaExp t l) Y := by
  unfold gramBound
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun l _ => mul_nonneg
    (Real.rpow_nonneg (zero_le_one.trans (one_le_gram_lower sz _ _)) _)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_gram_lower sz _ _)) _)) fun l _ => ?_
  have ha : 1 ≤ GramFormula.gram (l : ℕ) (RealLeviChart.lower sz (scaleCoord sz s Y)) := one_le_gram_lower sz _ _
  have hb : 1 ≤ GramFormula.gram (l : ℕ) (RealLeviChart.lower sz Y) := one_le_gram_lower sz _ _
  have hab := gram_lower_scaleCoord_le sz hs Y (l : ℕ)
  have hb0 : 0 < GramFormula.gram (l : ℕ) (RealLeviChart.lower sz Y) := zero_lt_one.trans_le hb
  by_cases hl : (l : ℕ) = 0
  · have h1 : GramFormula.gram (l : ℕ) (RealLeviChart.lower sz (scaleCoord sz s Y)) = 1 := by
      rw [hl, gram_zero_eq, det_lower, one_pow]
    have h2 : GramFormula.gram (l : ℕ) (RealLeviChart.lower sz Y) = 1 := by
      rw [hl, gram_zero_eq, det_lower, one_pow]
    rw [h1, h2, Real.one_rpow, Real.one_rpow, Real.one_rpow, one_mul]
  · simp only [gammaExp, hl, ↓reduceIte]
    rw [Real.rpow_add hb0]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hb0.le _)
    rcases le_or_gt 0 ((t ((l : ℕ) - 1) - t l - 1) / 2) with h | h
    · rw [max_eq_left h]
      exact Real.rpow_le_rpow (zero_le_one.trans ha) hab h
    · rw [max_eq_right h.le, Real.rpow_zero]
      exact Real.rpow_le_one_of_one_le_of_nonpos ha h.le

end Bounds

/-! ## Integrability after the substitution `X ↦ Ad(τ_θ) X` and the exchange of integrals -/

section Fubini

open RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance borelSpaceK_ll (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

attribute [local instance] RealBlockLimit.secondCountableTopology_unitaryCompact

variable {c : ℕ} {sz : Fin c → ℕ} {r : ℕ}

theorem integrable_comp_adCoord {B : (Coord sz → ℝ) → ℝ} (hBc : Continuous B) (hB : Integrable B)
    {μ : Measure (Fin r → ℝ)} [IsFiniteMeasure μ]
    {T : (Fin r → ℝ) → Langlands.GeneralLinear (∑ i, sz i) ℝ} (hT : Continuous T)
    (hTo : ∀ θ, T θ ∈ blockOrth sz) :
    Integrable (fun p : (Coord sz → ℝ) × (Fin r → ℝ) =>
      B (adCoord (T p.2 : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) p.1)) (volume.prod μ) := by
  have hc : Continuous (fun p : (Coord sz → ℝ) × (Fin r → ℝ) =>
      B (adCoord (T p.2 : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) p.1)) :=
    hBc.comp (continuous_adCoord_prod.comp
      ((Units.continuous_val.comp (hT.comp continuous_snd)).prodMk continuous_fst))
  rw [integrable_prod_iff' hc.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun θ => ?_, ?_⟩
  · exact (measurePreserving_adCoord (hTo θ)).integrable_comp_of_integrable hB
  · have : (fun θ => ∫ X, ‖B (adCoord (T θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X)‖) =
        fun _ => ∫ X, ‖B X‖ := by
      funext θ
      exact integral_adCoord (hTo θ) (fun X => ‖B X‖)
    rw [this]
    exact integrable_const _

/-- **Exchange of integrals.** `∫_{K_M} ∫_X ∫_θ f = ∫_θ ∫_{K_M} ∫_X f` under a bound `b(X, θ)`
integrable on the product. -/
theorem integral_swap_torus {μK : Measure (∀ i, unitaryCompact ℝ (sz i))} [IsFiniteMeasure μK]
    {μ : Measure (Fin r → ℝ)} [IsFiniteMeasure μ]
    {f : (∀ i, unitaryCompact ℝ (sz i)) → (Coord sz → ℝ) → (Fin r → ℝ) → ℂ}
    (hf : Continuous fun p : ((∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ)) × (Fin r → ℝ) =>
      f p.1.1 p.1.2 p.2)
    {b : (Coord sz → ℝ) → (Fin r → ℝ) → ℝ}
    (hb : Integrable (fun p : (Coord sz → ℝ) × (Fin r → ℝ) => b p.1 p.2) (volume.prod μ))
    (hbθ : ∀ θ, Integrable fun X => b X θ)
    (hfb : ∀ κ X θ, ‖f κ X θ‖ ≤ b X θ) :
    ∫ κ, (∫ X, (∫ θ, f κ X θ ∂μ)) ∂μK = ∫ θ, (∫ κ, (∫ X, f κ X θ) ∂μK) ∂μ := by
  have h1 : ∀ κ, ∫ X, (∫ θ, f κ X θ ∂μ) = ∫ θ, (∫ X, f κ X θ) ∂μ := by
    intro κ
    refine integral_integral_swap ?_
    refine Integrable.mono' hb ?_ (ae_of_all _ fun p => hfb κ p.1 p.2)
    exact (hf.comp ((continuous_const.prodMk continuous_fst).prodMk
      continuous_snd)).aestronglyMeasurable
  simp_rw [h1]
  refine integral_integral_swap ?_
  refine Integrable.mono' (hb.integral_prod_right.comp_snd μK) ?_
    (ae_of_all _ fun p => norm_integral_le_of_norm_le (hbθ p.2)
      (ae_of_all _ fun X => hfb p.1 X p.2))
  exact AEStronglyMeasurable.integral_prod_right'
    (f := fun q : ((∀ i, unitaryCompact ℝ (sz i)) × (Fin r → ℝ)) × (Coord sz → ℝ) =>
      f q.1.1 q.2 q.1.2)
    (hf.comp (((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
      (continuous_snd.comp continuous_fst))).aestronglyMeasurable

end Fubini

/-! ## The pairing identity at a fixed scale -/

section FixedScale

open RealPrincipalSeriesDuality MaximalParabolicIntegration PartialJacquet JacquetLimit

attribute [local instance] measurableSpaceK

local instance borelSpaceK_lf (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

attribute [local instance] RealBlockLimit.secondCountableTopology_unitaryCompact

variable {c : ℕ} {sz : Fin c → ℕ}

/-- **The pairing identity at the scale `s`.** For all `s > 0`,
`∫_{K_M} ∫_X ∫_θ u(τ_θ n̄(X_s) diag(κ)) h(τ_θ n̄(X) diag(κ)) dθ dX dκ = 0`. -/
theorem integral_torus_scale_eq_zero (hT1 : RealLeviChartIntegrableStatement)
    (hT3 : RealLeviParabolicIntegrationStatement) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}
    (hχ : IsSignedPower χ e) {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hu : u ∈ principalSeries ℝ (∑ i, sz i) (dualChar χ))
    (hh : h ∈ principalSeries ℝ (∑ i, sz i) χ)
    (h0 : ∀ g : Langlands.GeneralLinear (∑ i, sz i) ℝ,
      ∫ κ, u ((κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) * g) * h κ ∂haarK (∑ i, sz i) = 0)
    (L : List (Slot (∑ i, sz i)))
    (hL : ∀ s ∈ L, cls sz ⟨s.p, by have := s.hp; omega⟩ = cls sz ⟨s.p + 1, s.hp⟩)
    {s : ℝ} (hs : 0 < s) :
    ∫ κ, (∫ X : Coord sz → ℝ, (∫ θ,
        u (torusElem L θ * (lowerGL sz (scaleCoord sz s X) * bdK sz κ)) *
          h (torusElem L θ * (lowerGL sz X * bdK sz κ)) ∂torusMeasure L.length))
      ∂Measure.pi (fun i => haarK (sz i)) = 0 := by
  obtain ⟨C, hC, hT3'⟩ := hT3 c sz
  have hτ : ∀ θ, torusElem L θ ∈ blockOrth sz := torusElem_mem_blockOrth L hL
  set d : Langlands.GeneralLinear (∑ i, sz i) ℝ := scaleGL sz hs with hd
  have hud := rightTranslation_mem_principalSeries (χ := dualChar χ) hu d
  set G : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ := fun y => u (y * d) * h y with hGdef
  have hGs : ContMDiff (matrixModel ℝ (∑ i, sz i)) 𝓘(ℝ, ℂ) ∞ G := contMDiff_mul_fun hud.1 hh.1
  have hGc : Continuous G := hGs.continuous
  have hG : IsModulusCovariant G := by
    intro z v y
    simp only [hGdef]
    rw [mul_assoc _ y, hu.2 z v, hh.2 z v y, ← principalSeriesCharacter_dual_mul hχ]
    ring
  -- the integral formula
  have hJ : ∫ κ, (∫ X : Coord sz → ℝ, G (lowerGL sz X * bdK sz κ))
      ∂Measure.pi (fun i => haarK (sz i)) = 0 := by
    have h1 := (hT3' G hGs hG).2
    rw [show (∫ κ, G (κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) ∂haarK (∑ i, sz i)) = 0
      from h0 d] at h1
    have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
    exact (mul_eq_zero.mp h1.symm).resolve_left hC0
  -- invariance under the torus element
  have hθ : ∀ θ, ∫ κ, (∫ X : Coord sz → ℝ, G (torusElem L θ * (lowerGL sz X * bdK sz κ)))
      ∂Measure.pi (fun i => haarK (sz i)) = 0 := by
    intro θ
    have e1 : ∀ κ : ∀ i, unitaryCompact ℝ (sz i),
        (∫ X : Coord sz → ℝ, G (torusElem L θ * (lowerGL sz X * bdK sz κ))) =
          ∫ X : Coord sz → ℝ, G (lowerGL sz X * (torusElem L θ * bdK sz κ)) := by
      intro κ
      have : ∀ X, G (torusElem L θ * (lowerGL sz X * bdK sz κ)) =
          G (lowerGL sz (adCoord (torusElem L θ : Matrix _ _ ℝ) X) *
            (torusElem L θ * bdK sz κ)) := by
        intro X
        rw [← mul_assoc, mul_lowerGL (hτ θ), mul_assoc]
      simp_rw [this]
      exact integral_adCoord (hτ θ)
        (fun Y => G (lowerGL sz Y * (torusElem L θ * bdK sz κ)))
    simp_rw [e1]
    have h2 := integral_blockOrth_mul
      (fun g => ∫ X : Coord sz → ℝ, G (lowerGL sz X * g)) (hτ θ)
    exact h2.trans hJ
  -- the scaling identity
  set c' := principalSeriesCharacter ℝ (∑ i, sz i) (dualChar χ)
    (fun p => Units.mk0 (scaleVec sz s p) (scaleVec_pos sz hs p).ne') with hc'def
  have hdu : ∀ y, u (d * y) = c' * u y := fun y => by
    have := hu.2 (fun p => Units.mk0 (scaleVec sz s p) (scaleVec_pos sz hs p).ne') 1 y
    simpa [hd, scaleGL] using this
  have hc'0 : c' ≠ 0 := by
    rw [← norm_ne_zero_iff, hc'def, norm_principalSeriesCharacter hχ.dual]
    exact (Finset.prod_pos fun l _ =>
      Real.rpow_pos_of_pos (abs_pos.mpr (Units.ne_zero _)) _).ne'
  have hpt : ∀ (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ) (θ : Fin L.length → ℝ),
      u (torusElem L θ * (lowerGL sz (scaleCoord sz s X) * bdK sz κ)) *
        h (torusElem L θ * (lowerGL sz X * bdK sz κ)) =
      c'⁻¹ * G (torusElem L θ * (lowerGL sz X * bdK sz κ)) := by
    intro κ X θ
    have hk := bdK_mem_blockOrth (sz := sz) κ
    have e2 : torusElem L θ * (lowerGL sz X * bdK sz κ) * d =
        d * (torusElem L θ * (lowerGL sz (scaleCoord sz s X) * bdK sz κ)) := by
      rw [mul_assoc, mul_assoc, mul_scaleGL hk hs, ← mul_assoc (lowerGL sz X),
        lowerGL_mul_scaleGL sz hs, mul_assoc, ← mul_assoc (torusElem L θ),
        mul_scaleGL (hτ θ) hs, mul_assoc]
    simp only [hGdef]
    rw [e2, hdu, mul_assoc c', inv_mul_cancel_left₀ hc'0]
  simp_rw [hpt, integral_const_mul]
  refine mul_eq_zero_of_right _ ?_
  -- exchange the torus integral with the others
  obtain ⟨CG, hCG⟩ := exists_bound_unitaryCompact hGc
  have hT1' := hT1 c sz (fun _ => -1) (fun _ _ => by norm_num) (fun _ _ _ _ => by norm_num)
  have hB : Integrable fun X : Coord sz → ℝ => CG * gramBound (fun _ => -1) X :=
    hT1'.const_mul CG
  have hBc : Continuous fun X : Coord sz → ℝ => CG * gramBound (fun _ => -1) X :=
    continuous_const.mul (continuous_gramBound _)
  rw [integral_swap_torus (μ := torusMeasure L.length)
    (b := fun X θ => CG * gramBound (fun _ => -1)
      (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X))
    (continuous_integrand hGc ((continuous_torusElem L).comp continuous_snd)
      (continuous_snd.comp continuous_fst) (continuous_fst.comp continuous_fst))
    (integrable_comp_adCoord hBc hB (continuous_torusElem L) hτ)
    (fun θ => (measurePreserving_adCoord (hτ θ)).integrable_comp_of_integrable hB)
    (fun κ X θ => ?_)]
  · simp_rw [hθ]
    exact integral_zero _ _
  · rw [← mul_assoc, mul_lowerGL (hτ θ), mul_assoc]
    exact norm_modulusCovariant_le hG hCG _
      (mem_unitaryCompact_of_mem_blockOrth (mul_mem (hτ θ) (bdK_mem_blockOrth κ)))

end FixedScale

/-! ## The limit -/

section Limit

open RealPrincipalSeriesDuality PartialJacquet RealInducedStandardBound
  RealStrictCharacterLanglandsQuotient

attribute [local instance] measurableSpaceK

local instance borelSpaceK_lm (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

attribute [local instance] RealBlockLimit.secondCountableTopology_unitaryCompact

variable {c : ℕ} {sz : Fin c → ℕ}

/-- The induction blocks of `ds` lie inside the blocks of `Q`. -/
theorem slots_cls_eq {ds : List RealBlock}
    (hstrict : ∀ p q : Fin (∑ i, sz i), cls sz p < cls sz q →
      realPositionBlockExponent ds q < realPositionBlockExponent ds p) :
    ∀ s ∈ slots ds (∑ i, sz i), cls sz ⟨s.p, by have := s.hp; omega⟩ = cls sz ⟨s.p + 1, s.hp⟩ := by
  intro s hs
  obtain ⟨p, hp, d, hd, rfl⟩ := mem_slots hs
  obtain ⟨-, -, -, -, hb1, hb2, -⟩ := induced_at hd
  refine le_antisymm (cls_mono sz (Fin.mk_le_mk.mpr (Nat.le_succ p))) (not_lt.mp fun hlt => ?_)
  have h2 : realPositionBlockExponent ds (p + 1) < realPositionBlockExponent ds p :=
    hstrict _ _ hlt
  rw [hb1, hb2] at h2
  exact lt_irrefl _ h2

/-- **The limit argument along `Q`, torus averaged.** -/
theorem integral_coeffs_eq_zero (hT1 : RealLeviChartIntegrableStatement)
    (hT3 : RealLeviParabolicIntegrationStatement) {ds : List RealBlock}
    (hN : realRank ds = ∑ i, sz i)
    (hanti : ∀ p q : Fin (∑ i, sz i), p ≤ q →
      realPositionBlockExponent ds q ≤ realPositionBlockExponent ds p)
    (hstrict : ∀ p q : Fin (∑ i, sz i), cls sz p < cls sz q →
      realPositionBlockExponent ds q < realPositionBlockExponent ds p)
    {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hh : h ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds) (unitaryCompact ℝ (∑ i, sz i)))
    (h0 : ∀ g : Langlands.GeneralLinear (∑ i, sz i) ℝ,
      ∫ κ, u ((κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) * g) * h κ ∂haarK (∑ i, sz i) = 0) :
    ∫ κ, (∫ X : Coord sz → ℝ, coeffs (zeroModes (slots ds (∑ i, sz i)))
        (fun x => u (x * bdK sz κ) * h (x * (lowerGL sz X * bdK sz κ))) 1)
      ∂Measure.pi (fun i => haarK (sz i)) = 0 := by
  set L := slots ds (∑ i, sz i) with hLdef
  set t := realPositionBlockExponent ds with htdef
  have hpsu : u ∈ principalSeries ℝ (∑ i, sz i) (dualChar (realPositionCharacter ds)) := hu.1
  have hps : h ∈ principalSeries ℝ (∑ i, sz i) (realPositionCharacter ds) := hh.1.1
  have huc : Continuous u := hpsu.1.continuous
  have hhc : Continuous h := hps.1.continuous
  have hL := slots_cls_eq (sz := sz) hstrict
  have hτ : ∀ θ, torusElem L θ ∈ blockOrth sz := torusElem_mem_blockOrth L hL
  have hT : Continuous (torusElem L) := continuous_torusElem L
  have hτK : ∀ θ, torusElem L θ ∈ unitaryCompact ℝ (∑ i, sz i) :=
    torusElem_mem_unitaryCompact L
  -- the torus-pairing bound
  obtain ⟨C0, hC0⟩ := exists_bound hN hu hh
  set C := max C0 0 with hCdef
  -- the exponents
  have hdrop : ∀ l : ℕ, 0 < l → l < ∑ i, sz i → t l ≤ t (l - 1) := fun l hl hlN =>
    hanti ⟨l - 1, by omega⟩ ⟨l, hlN⟩ (Fin.mk_le_mk.mpr (Nat.sub_le l 1))
  set γ : Fin (∑ i, sz i) → ℝ := fun l => gammaExp t l with hγ
  have hγ0 : ∀ l, γ l ≤ 0 := fun l => by
    rcases Nat.eq_zero_or_pos (l : ℕ) with h' | h'
    · simp only [hγ, gammaExp, h', ↓reduceIte]
      norm_num
    · linarith [gammaExp_le t h' (hdrop l h' l.2)]
  have hBi : Integrable (gramBound (sz := sz) γ) :=
    hT1 c sz γ (fun l hl => gammaExp_le t hl (hdrop l hl l.2)) fun k l hkl hcls => by
      have h1 := hstrict k l hcls
      have h2 : (k : ℕ) = (l : ℕ) - 1 := by omega
      refine gammaExp_lt t (by omega) ?_
      rw [← h2]
      exact h1
  have hBc : Continuous (gramBound (sz := sz) γ) := continuous_gramBound γ
  have hprod := integrable_comp_adCoord hBc hBi (μ := torusMeasure L.length) hT hτ
  set D : (Coord sz → ℝ) → ℝ := fun X => C * ∫ θ, gramBound γ
    (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X)
      ∂torusMeasure L.length with hDdef
  have hDi : Integrable D := hprod.integral_prod_left.const_mul C
  have hBθ : ∀ X : Coord sz → ℝ, Integrable (fun θ => gramBound γ
      (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X))
      (torusMeasure L.length) := fun X => by
    refine Integrable.of_bound ?_ 1 (ae_of_all _ fun θ => ?_)
    · exact (hBc.comp (continuous_adCoord_prod.comp
        ((Units.continuous_val.comp hT).prodMk continuous_const))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (gramBound_nonneg _ _)]
      exact gramBound_le_one hγ0 _
  -- the integrands
  set Ψ : ℕ → (∀ i, unitaryCompact ℝ (sz i)) → (Coord sz → ℝ) → ℂ := fun n κ X =>
    ∫ θ, u (torusElem L θ * (lowerGL sz (scaleCoord sz ((n : ℝ) + 1) X) * bdK sz κ)) *
      h (torusElem L θ * (lowerGL sz X * bdK sz κ)) ∂torusMeasure L.length with hΨ
  set Ψ' : (∀ i, unitaryCompact ℝ (sz i)) → (Coord sz → ℝ) → ℂ := fun κ X =>
    ∫ θ, u (torusElem L θ * bdK sz κ) * h (torusElem L θ * (lowerGL sz X * bdK sz κ))
      ∂torusMeasure L.length with hΨ'
  have hcont : ∀ n : ℕ, Continuous fun q : ((∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ)) ×
      (Fin L.length → ℝ) =>
      u (torusElem L q.2 * (lowerGL sz (scaleCoord sz ((n : ℝ) + 1) q.1.2) * bdK sz q.1.1)) *
        h (torusElem L q.2 * (lowerGL sz q.1.2 * bdK sz q.1.1)) := fun n =>
    (continuous_integrand huc (hT.comp continuous_snd)
      ((continuous_scaleCoord _).comp (continuous_snd.comp continuous_fst))
      (continuous_fst.comp continuous_fst)).mul
    (continuous_integrand hhc (hT.comp continuous_snd) (continuous_snd.comp continuous_fst)
      (continuous_fst.comp continuous_fst))
  have hzero : ∀ n : ℕ, ∫ κ, (∫ X, Ψ n κ X) ∂Measure.pi (fun i => haarK (sz i)) = 0 :=
    fun n => integral_torus_scale_eq_zero hT1 hT3 (isSignedPower ds) hpsu hps h0 L hL
      (by positivity)
  -- domination
  have hbound : ∀ (n : ℕ) (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ),
      ‖Ψ n κ X‖ ≤ D X := by
    intro n κ X
    have hs1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith
    have hs0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set y1 := lowerGL sz (scaleCoord sz ((n : ℝ) + 1) X) * bdK sz κ with hy1
    set y2 := lowerGL sz X * bdK sz κ with hy2
    have e1 : Ψ n κ X = coeffs (zeroModes L) (fun x => u (x * y1) * h (x * y2)) 1 := by
      rw [coeffs_eq_integral (F := fun x => u (x * y1) * h (x * y2)) ((huc.comp (continuous_id.mul continuous_const)).mul
        (hhc.comp (continuous_id.mul continuous_const))) L 1]
      simp only [mul_one, hΨ]
      rfl
    have hE1 := (contMDiff_expFun (∑ i, sz i) fun l => -t l).continuous
    have hE2 := (contMDiff_expFun (∑ i, sz i) t).continuous
    have e2 : coeffs (zeroModes L) (fun x => expFun (∑ i, sz i) (fun l => -t l) (x * y1) *
        expFun (∑ i, sz i) t (x * y2)) 1 = ∫ θ, expFun (∑ i, sz i) (fun l => -t l)
          (torusElem L θ * y1) * expFun (∑ i, sz i) t (torusElem L θ * y2)
          ∂torusMeasure L.length := by
      rw [coeffs_eq_integral (F := fun x => expFun (∑ i, sz i) (fun l => -t l) (x * y1) *
        expFun (∑ i, sz i) t (x * y2)) ((hE1.comp (continuous_id.mul continuous_const)).mul
        (hE2.comp (continuous_id.mul continuous_const))) L 1]
      simp only [mul_one]
    have hpt : ∀ θ, ‖expFun (∑ i, sz i) (fun l => -t l) (torusElem L θ * y1) *
        expFun (∑ i, sz i) t (torusElem L θ * y2)‖ ≤ gramBound γ
          (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X) := by
      intro θ
      have hk : torusElem L θ * bdK sz κ ∈ unitaryCompact ℝ (∑ i, sz i) :=
        mem_unitaryCompact_of_mem_blockOrth (mul_mem (hτ θ) (bdK_mem_blockOrth κ))
      have f1 : torusElem L θ * y1 = lowerGL sz (scaleCoord sz ((n : ℝ) + 1)
          (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X)) *
            (torusElem L θ * bdK sz κ) := by
        rw [hy1, ← mul_assoc, mul_lowerGL (hτ θ), mul_assoc,
          adCoord_scaleCoord (hτ θ).1 (hτ θ).2 hs0]
      have f2 : torusElem L θ * y2 = lowerGL sz
          (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X) *
            (torusElem L θ * bdK sz κ) := by
        rw [hy2, ← mul_assoc, mul_lowerGL (hτ θ), mul_assoc]
      rw [f1, f2, norm_mul]
      refine le_trans ?_ (gramBound_mul_le t hs1 _)
      refine mul_le_mul (norm_expFun_le _ _ hk _ fun l _ => ?_)
        (norm_expFun_le _ _ hk _ fun l _ => rfl) (norm_nonneg _)
        (gramBound_nonneg _ _)
      ring
    rw [e1]
    refine (hC0 y1 y2).trans ?_
    rw [e2]
    calc C0 * ‖∫ θ, expFun (∑ i, sz i) (fun l => -t l) (torusElem L θ * y1) *
          expFun (∑ i, sz i) t (torusElem L θ * y2) ∂torusMeasure L.length‖ ≤
        C * ‖∫ θ, expFun (∑ i, sz i) (fun l => -t l) (torusElem L θ * y1) *
          expFun (∑ i, sz i) t (torusElem L θ * y2) ∂torusMeasure L.length‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ D X := mul_le_mul_of_nonneg_left
          (norm_integral_le_of_norm_le (hBθ X) (ae_of_all _ hpt)) (le_max_right _ _)
  -- the innermost limit
  have hlimθ : ∀ (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ),
      Tendsto (fun n : ℕ => Ψ n κ X) atTop (𝓝 (Ψ' κ X)) := by
    intro κ X
    obtain ⟨Mu, hMu⟩ := exists_bound_mul_tendsto huc (tendsto_lowerGL_scale X (bdK sz κ))
    obtain ⟨Mh, hMh⟩ := exists_bound_mul hhc (lowerGL sz X * bdK sz κ)
    have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu 1 (one_mem _) 0)
    refine tendsto_integral_of_dominated_convergence (fun _ => Mu * Mh) (fun n => ?_)
      (integrable_const _) (fun n => ae_of_all _ fun θ => ?_) (ae_of_all _ fun θ => ?_)
    · exact ((hcont n).comp ((continuous_const.prodMk continuous_const).prodMk
        continuous_id)).aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_mul (hMu _ (hτK θ) n) (hMh _ (hτK θ)) (norm_nonneg _) hMu0
    · exact ((huc.tendsto _).comp (tendsto_const_nhds.mul
        (tendsto_lowerGL_scale X (bdK sz κ)))).mul_const _
  -- the middle limit
  have hlimX : ∀ κ : ∀ i, unitaryCompact ℝ (sz i),
      Tendsto (fun n : ℕ => ∫ X, Ψ n κ X) atTop (𝓝 (∫ X, Ψ' κ X)) := by
    intro κ
    refine tendsto_integral_of_dominated_convergence D (fun n => ?_) hDi
      (fun n => ae_of_all _ (hbound n κ)) (ae_of_all _ (hlimθ κ))
    exact AEStronglyMeasurable.integral_prod_right'
      (f := fun p : (Coord sz → ℝ) × (Fin L.length → ℝ) =>
        u (torusElem L p.2 * (lowerGL sz (scaleCoord sz ((n : ℝ) + 1) p.1) * bdK sz κ)) *
          h (torusElem L p.2 * (lowerGL sz p.1 * bdK sz κ)))
      ((hcont n).comp ((continuous_const.prodMk continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable
  -- the outer limit
  have hlim : Tendsto (fun n : ℕ => ∫ κ, (∫ X, Ψ n κ X) ∂Measure.pi (fun i => haarK (sz i)))
      atTop (𝓝 (∫ κ, (∫ X, Ψ' κ X) ∂Measure.pi (fun i => haarK (sz i)))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ X, D X) (fun n => ?_)
      (integrable_const _) (fun n => ae_of_all _ fun κ => ?_) (ae_of_all _ hlimX)
    · exact AEStronglyMeasurable.integral_prod_right'
        (f := fun q : (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ) => Ψ n q.1 q.2)
        (AEStronglyMeasurable.integral_prod_right'
          (f := fun q : ((∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ)) ×
            (Fin L.length → ℝ) =>
            u (torusElem L q.2 * (lowerGL sz (scaleCoord sz ((n : ℝ) + 1) q.1.2) *
              bdK sz q.1.1)) * h (torusElem L q.2 * (lowerGL sz q.1.2 * bdK sz q.1.1)))
          (hcont n).aestronglyMeasurable)
    · exact norm_integral_le_of_norm_le hDi (ae_of_all _ (hbound n κ))
  simp only [hzero] at hlim
  have h3 := tendsto_nhds_unique hlim tendsto_const_nhds
  have e3 : ∀ (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ),
      coeffs (zeroModes L) (fun x => u (x * bdK sz κ) * h (x * (lowerGL sz X * bdK sz κ))) 1 =
        Ψ' κ X := by
    intro κ X
    rw [coeffs_eq_integral (F := fun x => u (x * bdK sz κ) * h (x * (lowerGL sz X * bdK sz κ)))
      ((huc.comp (continuous_id.mul continuous_const)).mul
        (hhc.comp (continuous_id.mul continuous_const))) L 1]
    simp only [mul_one, hΨ']
  simp_rw [e3]
  exact h3

end Limit

end RealLeviLimit

open RealPrincipalSeriesDuality RealLeviChart RealInducedBlockBound RealInducedTorusCore
  RealInducedStandardBound PartialJacquet in
attribute [local instance] measurableSpaceK in
/-- **The limit argument along a standard parabolic subgroup, torus averaged** (assuming
`RealLeviChartIntegrableStatement` and `RealLeviParabolicIntegrationStatement`). Let `Q` be the
standard parabolic subgroup of `GL_N(ℝ)` with diagonal blocks of sizes `sz_0, …, sz_{c-1}`
(`N = ∑ sz_i`), and let `ds` be a list of real blocks of rank `N` whose block exponents
`t_p = realPositionBlockExponent ds p` decrease weakly along the positions and strictly from a
block of `Q` to a later one. Let `u` be an `O(N)`-finite function in the principal series of the
inverse characters of `ds` and `h` an `O(N)`-finite function in the standard module of `ds`. If
`∫_{O(N)} u(κ g) h(κ) dκ = 0` for every `g`, then
`∫_{K_M} ∫_{N̄_Q} c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ))) dX dκ = 0`, where `K_M = ∏_i O(sz_i)`
carries the product of the Haar probability measures, `N̄_Q` the Lebesgue measure in the
coordinates `Coord sz`, and `c_Z = coeffs (zeroModes (slots ds N)) · 1` is the iterated mode-`0`
Fourier coefficient over the rotations of the induction blocks of `ds`, evaluated at `1`. -/
def RealLeviLimitStatement : Prop :=
  RealLeviChartIntegrableStatement → RealLeviParabolicIntegrationStatement →
  ∀ (c : ℕ) (sz : Fin c → ℕ) (ds : List RealBlock), realRank ds = ∑ i, sz i →
    (∀ p q : Fin (∑ i, sz i), p ≤ q →
      realPositionBlockExponent ds q ≤ realPositionBlockExponent ds p) →
    (∀ p q : Fin (∑ i, sz i), cls sz p < cls sz q →
      realPositionBlockExponent ds q < realPositionBlockExponent ds p) →
    ∀ u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i) (dualChar (realPositionCharacter ds)))
        (unitaryCompact ℝ (∑ i, sz i)),
    ∀ h ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds) (unitaryCompact ℝ (∑ i, sz i)),
      (∀ g : Langlands.GeneralLinear (∑ i, sz i) ℝ,
        ∫ κ, u ((κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) * g) * h κ
          ∂haarK (∑ i, sz i) = 0) →
      ∫ κ : (∀ i, unitaryCompact ℝ (sz i)),
        (∫ X : Coord sz → ℝ, coeffs (zeroModes (slots ds (∑ i, sz i)))
          (fun x => u (x * blockDiagGL sz (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ))) *
            h (x * (lowerGL sz X *
              blockDiagGL sz (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ))))) 1)
        ∂Measure.pi (fun i => haarK (sz i)) = 0

theorem realLeviLimit : RealLeviLimitStatement :=
  fun hT1 hT3 _ _ _ hN hanti hstrict _ hu _ hh h0 =>
    RealLeviLimit.integral_coeffs_eq_zero hT1 hT3 hN hanti hstrict hu hh h0

end Langlands.Archimedean
