import Langlands.Representation.Archimedean.RealLeviLimit
import Langlands.Representation.Archimedean.RealLeviModes
import Langlands.Representation.Archimedean.RealLeviDensity

/-!
# The torus averaged pairing along a standard parabolic subgroup

For `u` in the `O(N)`-finite principal series of the inverse characters of a list `ds` and `h` in
the `O(N)`-finite standard module of `ds`, the pairing
`Θ(u, h) = ∫_{K_M} ∫_{N̄_Q} c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ))) dX dκ` of
`RealLeviLimitStatement` converges absolutely when the exponents of `ds` decrease weakly and
strictly between the blocks of `Q` (assuming `RealLeviChartIntegrableStatement`). This module
proves the domination of its integrand by an integrable bounded function of `X`, the continuity
of the integrand, the linearity of `Θ` in `h`, and that `Θ(u, h)` depends on `u` only through
its jointly allowed iterated coefficients at the points `diag(κ)`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviPairing

open RealInducedBlockBound RealInducedTorusCore RealLeviChart GramFormula RealLeviTorus
  RealLeviLimit RealPrincipalSeriesDuality PartialJacquet RealInducedStandardBound
  RealStrictCharacterLanglandsQuotient RealLeviModes

attribute [local instance] measurableSpaceK

local instance borelSpaceK_lp (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

attribute [local instance] RealBlockLimit.secondCountableTopology_unitaryCompact

/-! ## Iterated coefficients -/

section Coeffs

variable {N : ℕ}

theorem coeffs_zero_fun : ∀ (L : List (Slot N)) (g : Langlands.GeneralLinear N ℝ),
    coeffs L (fun _ => 0) g = 0
  | [], _ => rfl
  | s :: L, _ => blockFourierCoefficient_eq_zero_of s.j fun _ => coeffs_zero_fun L _

/-- Iterated coefficients vanish everywhere if one block coefficient vanishes everywhere. -/
theorem coeffs_eq_zero_of_forall {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) :
    ∀ (L : List (Slot N)), L.Pairwise Slot.Disjoint → ∀ t ∈ L,
      (∀ g, blockFourierCoefficient N t.p t.j F g = 0) → ∀ g, coeffs L F g = 0
  | [], _, t, ht, _, _ => absurd ht List.not_mem_nil
  | s :: rest, hpw, t, ht, h0, g => by
    obtain ⟨hsd, hrest⟩ := List.pairwise_cons.mp hpw
    have hsd' : ∀ t' ∈ rest, s.p + 1 < t'.p ∨ t'.p + 1 < s.p := hsd
    rcases List.mem_cons.mp ht with rfl | ht'
    · show blockFourierCoefficient N t.p t.j (coeffs rest F) g = 0
      rw [blockFourierCoefficient_coeffs t.j hF rest hsd']
      have : blockFourierCoefficient N t.p t.j F = fun _ => 0 := funext h0
      rw [this]
      exact coeffs_zero_fun rest g
    · show blockFourierCoefficient N s.p s.j (coeffs rest F) g = 0
      exact blockFourierCoefficient_eq_zero_of s.j fun θ =>
        coeffs_eq_zero_of_forall hF rest hrest t ht' h0 _

theorem coeffs_const_mul (a : ℂ) (F : Langlands.GeneralLinear N ℝ → ℂ) :
    ∀ (L : List (Slot N)) (g : Langlands.GeneralLinear N ℝ),
      coeffs L (fun x => a * F x) g = a * coeffs L F g
  | [], _ => rfl
  | s :: L, g => by
    simp only [coeffs]
    rw [show coeffs L (fun x => a * F x) = fun x => a * coeffs L F x from
      funext fun x => coeffs_const_mul a F L x]
    unfold blockFourierCoefficient
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only
    ring

theorem hasDegree_mono {S : List (Slot N)} {D D' : ℕ} {u : Langlands.GeneralLinear N ℝ → ℂ}
    (h : HasDegree S D u) (hD : D ≤ D') : HasDegree S D' u :=
  fun s hs j hj k hk => h s hs j (lt_of_le_of_lt (by exact_mod_cast hD) hj) k hk

/-- A continuous function is bounded on `O(N) · S` for a compact set `S`. -/
theorem exists_bound_compact {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F)
    {S : Set (Langlands.GeneralLinear N ℝ)} (hS : IsCompact S) :
    ∃ M : ℝ, ∀ k ∈ unitaryCompact ℝ N, ∀ y ∈ S, ‖F (k * y)‖ ≤ M := by
  have hK : IsCompact (unitaryCompact ℝ N : Set (Langlands.GeneralLinear N ℝ)) := by
    have := isCompact_range (continuous_subtype_val :
      Continuous fun k : unitaryCompact ℝ N => (k : Langlands.GeneralLinear N ℝ))
    simpa using this
  obtain ⟨M, hM⟩ := (hK.prod hS).exists_bound_of_continuousOn
    ((hF.comp (continuous_fst.mul continuous_snd)).continuousOn)
  exact ⟨M, fun k hk y hy => hM (k, y) ⟨hk, hy⟩⟩

end Coeffs

/-! ## The pairing -/

section Pairing

variable {c : ℕ} {sz : Fin c → ℕ}

/-- The integrand `c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ)))` of the pairing. -/
def psi (L : List (Slot (∑ i, sz i))) (u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ)
    (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ) : ℂ :=
  coeffs (zeroModes L) (fun x => u (x * bdK sz κ) * h (x * (lowerGL sz X * bdK sz κ))) 1

/-- The pairing `Θ(u, h) = ∫_{K_M} ∫_X psi`. -/
def theta (L : List (Slot (∑ i, sz i))) (u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ) : ℂ :=
  ∫ κ, (∫ X, psi L u h κ X) ∂Measure.pi (fun i => haarK (sz i))

/-- The exponent conditions of the limit argument along `Q`. -/
structure Admissible (sz : Fin c → ℕ) (ds : List RealBlock) : Prop where
  rank : realRank ds = ∑ i, sz i
  anti : ∀ p q : Fin (∑ i, sz i), p ≤ q →
    realPositionBlockExponent ds q ≤ realPositionBlockExponent ds p
  strict : ∀ p q : Fin (∑ i, sz i), cls sz p < cls sz q →
    realPositionBlockExponent ds q < realPositionBlockExponent ds p

theorem gramBound_mono {a b : Fin (∑ i, sz i) → ℝ}
    (hab : ∀ l : Fin (∑ i, sz i), 0 < (l : ℕ) → a l ≤ b l) (Y : Coord sz → ℝ) :
    gramBound a Y ≤ gramBound b Y := by
  unfold gramBound
  refine Finset.prod_le_prod₀ (fun l _ => Real.rpow_nonneg
    (zero_le_one.trans (one_le_gram_lower sz Y l)) _) fun l _ => ?_
  by_cases hl : (l : ℕ) = 0
  · have h1 : gram (l : ℕ) (lower sz Y) = 1 := by rw [hl, gram_zero_eq, det_lower, one_pow]
    rw [h1, Real.one_rpow, Real.one_rpow]
  · exact Real.rpow_le_rpow_of_exponent_le (one_le_gram_lower sz Y l)
      (hab l (Nat.pos_of_ne_zero hl))

theorem psi_eq_integral {L : List (Slot (∑ i, sz i))}
    {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ} (hu : Continuous u) (hh : Continuous h)
    (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ) :
    psi L u h κ X = ∫ θ, u (torusElem L θ * bdK sz κ) *
      h (torusElem L θ * (lowerGL sz X * bdK sz κ)) ∂torusMeasure L.length := by
  unfold psi
  rw [coeffs_eq_integral (F := fun x => u (x * bdK sz κ) * h (x * (lowerGL sz X * bdK sz κ)))
    ((hu.comp (continuous_id.mul continuous_const)).mul
      (hh.comp (continuous_id.mul continuous_const))) L 1]
  simp only [mul_one]

/-- **Continuity of the integrand** in `(κ, X)`. -/
theorem continuous_psi (L : List (Slot (∑ i, sz i)))
    {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ} (hu : Continuous u) (hh : Continuous h) :
    Continuous fun p : (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ) => psi L u h p.1 p.2 := by
  have e : (fun p : (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ) => psi L u h p.1 p.2) =
      fun p => ∫ θ, u (torusElem L θ * bdK sz p.1) *
        h (torusElem L θ * (lowerGL sz p.2 * bdK sz p.1)) ∂torusMeasure L.length :=
    funext fun p => psi_eq_integral hu hh p.1 p.2
  rw [e]
  have hT := continuous_torusElem L
  have hG : Continuous fun q : ((∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ)) ×
      (Fin L.length → ℝ) => u (torusElem L q.2 * bdK sz q.1.1) *
        h (torusElem L q.2 * (lowerGL sz q.1.2 * bdK sz q.1.1)) :=
    (hu.comp ((hT.comp continuous_snd).mul (continuous_bdK.comp
      (continuous_fst.comp continuous_fst)))).mul
    (hh.comp ((hT.comp continuous_snd).mul ((continuous_lowerGL.comp
      (continuous_snd.comp continuous_fst)).mul (continuous_bdK.comp
        (continuous_fst.comp continuous_fst)))))
  refine continuous_iff_continuousAt.mpr fun p0 => ?_
  set S : Set (Langlands.GeneralLinear (∑ i, sz i) ℝ) :=
    (fun q : (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ) => lowerGL sz q.2 * bdK sz q.1) ''
      (Set.univ ×ˢ Metric.closedBall p0.2 1) with hSdef
  have hS : IsCompact S := (isCompact_univ.prod (isCompact_closedBall _ _)).image
    ((continuous_lowerGL.comp continuous_snd).mul (continuous_bdK.comp continuous_fst))
  obtain ⟨Mu, hMu⟩ := exists_bound_compact hu (isCompact_range (continuous_bdK (sz := sz)))
  obtain ⟨Mh, hMh⟩ := exists_bound_compact hh hS
  have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu 1 (one_mem _) _ ⟨p0.1, rfl⟩)
  refine continuousAt_of_dominated (bound := fun _ => Mu * Mh)
    (Eventually.of_forall fun p =>
      (hG.comp ((continuous_const.prodMk continuous_id))).aestronglyMeasurable)
    ?_ (integrable_const _) (ae_of_all _ fun θ =>
      (hG.comp (continuous_id.prodMk continuous_const)).continuousAt)
  filter_upwards [prod_mem_nhds Filter.univ_mem (Metric.closedBall_mem_nhds p0.2 one_pos)] with p hp
  refine ae_of_all _ fun θ => ?_
  rw [norm_mul]
  exact mul_le_mul (hMu _ (torusElem_mem_unitaryCompact L θ) _ ⟨p.1, rfl⟩)
    (hMh _ (torusElem_mem_unitaryCompact L θ) _ ⟨p, ⟨trivial, hp.2⟩, rfl⟩) (norm_nonneg _) hMu0

variable {ds : List RealBlock}

/-- **Domination.** The integrand is bounded by an integrable bounded function of `X`. -/
theorem exists_dom (hT1 : RealLeviChartIntegrableStatement) (hA : Admissible sz ds)
    {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hh : h ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
      (unitaryCompact ℝ (∑ i, sz i))) :
    ∃ D : (Coord sz → ℝ) → ℝ, Integrable D ∧ (∃ B : ℝ, ∀ X, D X ≤ B) ∧
      ∀ κ X, ‖psi (slots ds (∑ i, sz i)) u h κ X‖ ≤ D X := by
  set L := slots ds (∑ i, sz i) with hLdef
  set t := realPositionBlockExponent ds with htdef
  have hL := slots_cls_eq (sz := sz) hA.strict
  have hτ : ∀ θ, torusElem L θ ∈ blockOrth sz := torusElem_mem_blockOrth L hL
  have hT : Continuous (torusElem L) := continuous_torusElem L
  obtain ⟨C0, hC0⟩ := exists_bound hA.rank hu hh
  set C := max C0 0 with hCdef
  have hdrop : ∀ l : ℕ, 0 < l → l < ∑ i, sz i → t l ≤ t (l - 1) := fun l hl hlN =>
    hA.anti ⟨l - 1, by omega⟩ ⟨l, hlN⟩ (Fin.mk_le_mk.mpr (Nat.sub_le l 1))
  set γ : Fin (∑ i, sz i) → ℝ := fun l => gammaExp t l with hγ
  have hγ0 : ∀ l, γ l ≤ 0 := fun l => by
    rcases Nat.eq_zero_or_pos (l : ℕ) with h' | h'
    · simp only [hγ, gammaExp, h', ↓reduceIte]
      norm_num
    · linarith [gammaExp_le t h' (hdrop l h' l.2)]
  have hBi : Integrable (gramBound (sz := sz) γ) :=
    hT1 c sz γ (fun l hl => gammaExp_le t hl (hdrop l hl l.2)) fun k l hkl hcls => by
      have h1 := hA.strict k l hcls
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
  refine ⟨D, hDi, ⟨C * (torusMeasure L.length).real Set.univ, fun X => ?_⟩, fun κ X => ?_⟩
  · refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
    calc ∫ θ, gramBound γ (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i))
          (Fin (∑ i, sz i)) ℝ) X) ∂torusMeasure L.length ≤
        ∫ _θ, (1 : ℝ) ∂torusMeasure L.length :=
          integral_mono (hBθ X) (integrable_const _) fun θ => gramBound_le_one hγ0 _
      _ = (torusMeasure L.length).real Set.univ := by simp
  · set y1 := bdK sz κ with hy1
    set y2 := lowerGL sz X * bdK sz κ with hy2
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
      have f1 : expFun (∑ i, sz i) (fun l => -t l) (torusElem L θ * y1) = 1 := by
        have := expFun_mul (∑ i, sz i) (fun l => -t l) 1 hk
        rw [one_mul, expFun_one] at this
        exact this
      have f2 : torusElem L θ * y2 = lowerGL sz
          (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X) *
            (torusElem L θ * bdK sz κ) := by
        rw [hy2, ← mul_assoc, mul_lowerGL (hτ θ), mul_assoc]
      rw [f1, one_mul, f2]
      refine (norm_expFun_le t _ hk
        (fun l : Fin (∑ i, sz i) => (t l - t ((l : ℕ) - 1) - 1) / 2) fun l _ => rfl).trans
        (gramBound_mono (fun l hl => ?_) _)
      simp only [hγ, gammaExp, hl.ne', ↓reduceIte]
      linarith [le_max_right ((t ((l : ℕ) - 1) - t l - 1) / 2) 0]
    show ‖coeffs (zeroModes L) (fun x => u (x * y1) * h (x * y2)) 1‖ ≤ D X
    refine (hC0 y1 y2).trans ?_
    rw [e2]
    calc C0 * ‖∫ θ, expFun (∑ i, sz i) (fun l => -t l) (torusElem L θ * y1) *
          expFun (∑ i, sz i) t (torusElem L θ * y2) ∂torusMeasure L.length‖ ≤
        C * ‖∫ θ, expFun (∑ i, sz i) (fun l => -t l) (torusElem L θ * y1) *
          expFun (∑ i, sz i) t (torusElem L θ * y2) ∂torusMeasure L.length‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ D X := mul_le_mul_of_nonneg_left
          (norm_integral_le_of_norm_le (hBθ X) (ae_of_all _ hpt)) (le_max_right _ _)

section Integrable

variable (hT1 : RealLeviChartIntegrableStatement) (hA : Admissible sz ds)
  {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
  (hu : u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
    (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
  (hh : h ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
    (unitaryCompact ℝ (∑ i, sz i)))
include hT1 hA hu hh

theorem integrable_psi_prod :
    Integrable (fun p : (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ) =>
      psi (slots ds (∑ i, sz i)) u h p.1 p.2)
      ((Measure.pi fun i => haarK (sz i)).prod volume) := by
  obtain ⟨D, hDi, -, hD⟩ := exists_dom hT1 hA hu hh
  exact Integrable.mono' (hDi.comp_snd _)
    (continuous_psi _ hu.1.1.continuous hh.1.1.1.continuous).aestronglyMeasurable
    (ae_of_all _ fun p => hD p.1 p.2)

theorem integrable_psi (κ : ∀ i, unitaryCompact ℝ (sz i)) :
    Integrable (psi (slots ds (∑ i, sz i)) u h κ) := by
  obtain ⟨D, hDi, -, hD⟩ := exists_dom hT1 hA hu hh
  exact Integrable.mono' hDi ((continuous_psi _ hu.1.1.continuous
    hh.1.1.1.continuous).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun X => hD κ X)

theorem integrable_integral_psi :
    Integrable (fun κ => ∫ X, psi (slots ds (∑ i, sz i)) u h κ X)
      (Measure.pi fun i => haarK (sz i)) :=
  (integrable_psi_prod hT1 hA hu hh).integral_prod_left

end Integrable

/-! ## Linearity in `h` -/

theorem psi_add {L : List (Slot (∑ i, sz i))}
    {u h₁ h₂ : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ} (hu : Continuous u)
    (hh₁ : Continuous h₁) (hh₂ : Continuous h₂) (κ : ∀ i, unitaryCompact ℝ (sz i))
    (X : Coord sz → ℝ) :
    psi L u (h₁ + h₂) κ X = psi L u h₁ κ X + psi L u h₂ κ X := by
  unfold psi
  have e : (fun x => u (x * bdK sz κ) * (h₁ + h₂) (x * (lowerGL sz X * bdK sz κ))) =
      (fun x => u (x * bdK sz κ) * h₁ (x * (lowerGL sz X * bdK sz κ))) +
        fun x => u (x * bdK sz κ) * h₂ (x * (lowerGL sz X * bdK sz κ)) := by
    funext x
    simp only [Pi.add_apply, mul_add]
  rw [e]
  exact RealLeviDensity.coeffs_add ((hu.comp (continuous_id.mul continuous_const)).mul
    (hh₁.comp (continuous_id.mul continuous_const)))
    ((hu.comp (continuous_id.mul continuous_const)).mul
      (hh₂.comp (continuous_id.mul continuous_const))) _ 1

theorem psi_smul {L : List (Slot (∑ i, sz i))}
    {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ} (a : ℂ) (κ : ∀ i, unitaryCompact ℝ (sz i))
    (X : Coord sz → ℝ) :
    psi L u (a • h) κ X = a * psi L u h κ X := by
  unfold psi
  rw [← coeffs_const_mul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_add (hT1 : RealLeviChartIntegrableStatement) (hA : Admissible sz ds)
    {u h₁ h₂ : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hh₁ : h₁ ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
      (unitaryCompact ℝ (∑ i, sz i)))
    (hh₂ : h₂ ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
      (unitaryCompact ℝ (∑ i, sz i))) :
    theta (slots ds (∑ i, sz i)) u (h₁ + h₂) =
      theta (slots ds (∑ i, sz i)) u h₁ + theta (slots ds (∑ i, sz i)) u h₂ := by
  unfold theta
  have e : ∀ κ, ∫ X, psi (slots ds (∑ i, sz i)) u (h₁ + h₂) κ X =
      (∫ X, psi (slots ds (∑ i, sz i)) u h₁ κ X) +
        ∫ X, psi (slots ds (∑ i, sz i)) u h₂ κ X := by
    intro κ
    simp_rw [psi_add hu.1.1.continuous hh₁.1.1.1.continuous hh₂.1.1.1.continuous κ]
    exact integral_add (integrable_psi hT1 hA hu hh₁ κ) (integrable_psi hT1 hA hu hh₂ κ)
  simp_rw [e]
  exact integral_add (integrable_integral_psi hT1 hA hu hh₁)
    (integrable_integral_psi hT1 hA hu hh₂)

theorem theta_smul {L : List (Slot (∑ i, sz i))}
    {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ} (a : ℂ) :
    theta L u (a • h) = a * theta L u h := by
  unfold theta
  simp_rw [psi_smul a, integral_const_mul]

/-! ## Dependence on the jointly allowed coefficients of `u` -/

/-- `psi u h` depends on `u` only through the jointly allowed iterated coefficients of `u` at the
points `diag(κ)`. -/
theorem psi_congr
    {u u' h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hu' : u' ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hh : h ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
      (unitaryCompact ℝ (∑ i, sz i)))
    (hJ : ∀ J : List ℤ, J.length = (slots ds (∑ i, sz i)).length →
      (∀ t ∈ withModes (slots ds (∑ i, sz i)) J, (t.M : ℤ) ≤ |t.j|) →
        ∀ κ : ∀ i, unitaryCompact ℝ (sz i),
          coeffs (withModes (slots ds (∑ i, sz i)) J) u (bdK sz κ) =
            coeffs (withModes (slots ds (∑ i, sz i)) J) u' (bdK sz κ))
    (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ) :
    psi (slots ds (∑ i, sz i)) u h κ X = psi (slots ds (∑ i, sz i)) u' h κ X := by
  set S := slots ds (∑ i, sz i) with hSdef
  have hS := pairwise_slots ds (∑ i, sz i)
  have huc : Continuous u := hu.1.1.continuous
  have hu'c : Continuous u' := hu'.1.1.continuous
  have hhc : Continuous h := hh.1.1.1.continuous
  obtain ⟨D1, hD1⟩ := exists_hasDegree huc hu.2 S
  obtain ⟨D2, hD2⟩ := exists_hasDegree hu'c hu'.2 S
  have hk : bdK sz κ ∈ unitaryCompact ℝ (∑ i, sz i) :=
    mem_unitaryCompact_of_mem_blockOrth (bdK_mem_blockOrth κ)
  unfold psi
  rw [coeffs_zeroModes_mul_eq_sum (max D1 D2) S hS huc hu.2
      (hasDegree_mono hD1 (le_max_left _ _)) hhc _ hk,
    coeffs_zeroModes_mul_eq_sum (max D1 D2) S hS hu'c hu'.2
      (hasDegree_mono hD2 (le_max_right _ _)) hhc _ hk]
  congr 1
  refine Finset.sum_congr rfl fun J hJmem => ?_
  have hlen : J.length = S.length := (mem_modeLists hJmem).1
  by_cases hall : ∀ t ∈ withModes S J, (t.M : ℤ) ≤ |t.j|
  · rw [hJ J hlen hall κ]
  · push Not at hall
    obtain ⟨t, ht, hlt⟩ := hall
    have ht' := setMode_neg_mem_withModes ht
    obtain ⟨s, hs, j, rfl⟩ := mem_withModes ht
    have h0 : coeffs (withModes S (J.map Neg.neg)) h (lowerGL sz X * bdK sz κ) = 0 :=
      coeffs_eq_zero_of_forall hhc _ (pairwise_withModes _ hS) _ ht'
        (fun g => window_of_mem_standard hh.1 s hs (-j) (by rw [abs_neg]; exact hlt) g) _
    rw [h0, mul_zero, mul_zero]

theorem theta_congr
    {u u' h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hu' : u' ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hh : h ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
      (unitaryCompact ℝ (∑ i, sz i)))
    (hJ : ∀ J : List ℤ, J.length = (slots ds (∑ i, sz i)).length →
      (∀ t ∈ withModes (slots ds (∑ i, sz i)) J, (t.M : ℤ) ≤ |t.j|) →
        ∀ κ : ∀ i, unitaryCompact ℝ (sz i),
          coeffs (withModes (slots ds (∑ i, sz i)) J) u (bdK sz κ) =
            coeffs (withModes (slots ds (∑ i, sz i)) J) u' (bdK sz κ)) :
    theta (slots ds (∑ i, sz i)) u h = theta (slots ds (∑ i, sz i)) u' h := by
  unfold theta
  simp_rw [psi_congr hu hu' hh hJ]

end Pairing

end RealLeviPairing

end Langlands.Archimedean
