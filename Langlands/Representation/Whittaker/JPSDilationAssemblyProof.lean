import Langlands.Representation.Whittaker.JPSDilationAssemblyStatement
import Langlands.LocalField.Normalization.Continuity
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# JPS decomposition assembly from uniform coordinate dilations: proof

Coordinates are processed one at a time. A coordinate is either large, where it
stays in the coefficient, or small, where the dilation hypothesis replaces it by a
fixed unit and produces a translate of a finite function. After all coordinates
are processed, the coefficient is supported on a compact open box of the additive
space.
-/

noncomputable section

namespace Langlands.Whittaker.JPSDilationAssembly

open scoped BigOperators Topology
open JPSFunctionSpace

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ### Normalized absolute values -/

theorem normalizedAbs_pow (x : F.Carrier) (k : ℕ) :
    T.normalizedAbs (x ^ k) = T.normalizedAbs x ^ k := by
  induction k with
  | zero => simp [T.normalizedAbs_one]
  | succ k ih => rw [pow_succ, T.normalizedAbs_mul, ih, pow_succ]

theorem normalizedAbs_units_inv (c : F.Carrierˣ) :
    T.normalizedAbs ((c⁻¹ : F.Carrierˣ) : F.Carrier) = (T.normalizedAbs (c : F.Carrier))⁻¹ := by
  have h := T.normalizedAbs_mul (c : F.Carrier) ((c⁻¹ : F.Carrierˣ) : F.Carrier)
  rw [Units.mul_inv, T.normalizedAbs_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- Every positive bound is exceeded by the normalized absolute value of no power of a
uniformizer beyond some exponent; in particular some unit lies below the bound. -/
theorem exists_unit_normalizedAbs_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ c : F.Carrierˣ, T.normalizedAbs (c : F.Carrier) < ε := by
  have hπ : T.uniformizer ≠ 0 := by
    intro h
    have ho := T.ord_uniformizer
    rw [h, T.ord_zero] at ho
    exact zero_ne_one ho
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  refine ⟨Units.mk0 (T.uniformizer ^ k) (pow_ne_zero k hπ), ?_⟩
  rw [Units.val_mk0, normalizedAbs_pow, T.normalizedAbs_uniformizer, zpow_neg_one]
  exact hk

/-! ### The algebraic induction over coordinates -/

variable {n : ℕ}

/-- Replace the coordinates in `J` by those of `c`. -/
def freeze (J : Finset (Fin n)) (c a : Torus F n) : Torus F n :=
  fun i => if i ∈ J then c i else a i

/-- The factor of coordinate `i`: a small-ball cutoff times `γ i` on the frozen set `J`,
the constant one on the unprocessed set `S`, and a large-coordinate cutoff otherwise. -/
def factor (S J : Finset (Fin n)) (r : Fin n → ℝ) (γ : Fin n → F.Carrierˣ → ℂ)
    (i : Fin n) (y : F.Carrierˣ) : ℂ :=
  if i ∈ J then (if T.normalizedAbs (y : F.Carrier) ≤ r i then γ i y else 0)
  else if i ∈ S then 1 else (if r i < T.normalizedAbs (y : F.Carrier) then 1 else 0)

/-- The function handled at one stage of the induction. -/
def term (S J : Finset (Fin n)) (r : Fin n → ℝ) (γ : Fin n → F.Carrierˣ → ℂ)
    (c : Torus F n) (g : Torus F n → ℂ) (a : Torus F n) : ℂ :=
  (∏ i, factor T S J r γ i (a i)) * g (freeze J c a)

/-- Processing one coordinate `i`: the large part keeps `g`, and the small part is
expanded by the dilation formula at the frozen value `ci`. -/
theorem term_insert (W : FunctionSpace F n) (Y : Fin n → Finset (F.Carrierˣ → ℂ))
    (A : Fin n → (F.Carrierˣ → ℂ) → Module.End ℂ W.toSubmodule)
    {S J : Finset (Fin n)} {i : Fin n} (hiJ : i ∉ J) (hiS : i ∉ S) (r : Fin n → ℝ)
    (γ : Fin n → F.Carrierˣ → ℂ) (c : Torus F n) (g : W.toSubmodule)
    {ε : ℝ} (ci : F.Carrierˣ) (hci : T.normalizedAbs (ci : F.Carrier) < ε)
    (hdil : ∀ a : Torus F n, T.normalizedAbs (a i : F.Carrier) < ε →
      ∀ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 →
        (coordinateRepresentation W i b g).val a = ∑ η ∈ Y i, η b * (A i η g).val a)
    (a : Torus F n) :
    term T (insert i S) J r γ c g.val a =
      term T S J (Function.update r i (T.normalizedAbs (ci : F.Carrier))) γ c g.val a +
        ∑ η ∈ Y i, term T S (insert i J)
          (Function.update r i (T.normalizedAbs (ci : F.Carrier)))
          (Function.update γ i (fun y => η (ci⁻¹ * y))) (Function.update c i ci)
          (A i η g).val a := by
  set r' := Function.update r i (T.normalizedAbs (ci : F.Carrier)) with hr'
  set P := ∏ k ∈ Finset.univ.erase i, factor T (insert i S) J r γ k (a k) with hP
  -- The factors away from `i` agree.
  have hrest : ∀ k ∈ Finset.univ.erase i,
      factor T S J r' γ k (a k) = factor T (insert i S) J r γ k (a k) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    simp [factor, hr', hki, Finset.mem_insert]
  have hrest' : ∀ η : F.Carrierˣ → ℂ, ∀ k ∈ Finset.univ.erase i,
      factor T S (insert i J) r' (Function.update γ i (fun y => η (ci⁻¹ * y))) k (a k) =
        factor T (insert i S) J r γ k (a k) := by
    intro η k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    simp [factor, hr', hki, Finset.mem_insert]
  have e0 : ∏ k, factor T (insert i S) J r γ k (a k) = P := by
    have h0 : factor T (insert i S) J r γ i (a i) = 1 := by simp [factor, hiJ]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), h0, one_mul]
  have e1 : ∏ k, factor T S J r' γ k (a k) =
      (if T.normalizedAbs (ci : F.Carrier) < T.normalizedAbs (a i : F.Carrier) then 1 else 0) *
        P := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Finset.prod_congr rfl hrest]
    congr 1
    simp [factor, hiJ, hiS, hr']
  have e2 : ∀ η : F.Carrierˣ → ℂ,
      ∏ k, factor T S (insert i J) r' (Function.update γ i (fun y => η (ci⁻¹ * y))) k (a k) =
        (if T.normalizedAbs (a i : F.Carrier) ≤ T.normalizedAbs (ci : F.Carrier)
          then η (ci⁻¹ * a i) else 0) * P := by
    intro η
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Finset.prod_congr rfl (hrest' η)]
    congr 1
    simp [factor, hr']
  -- The frozen point after processing `i`, and its dilation back to the old point.
  have hpt : freeze (insert i J) (Function.update c i ci) a *
      coordinateEmbedding i (ci⁻¹ * a i) = freeze J c a := by
    rw [mul_coordinateEmbedding]
    funext k
    by_cases hki : k = i
    · subst hki
      simp [freeze, hiJ]
    · simp [freeze, hki]
  have hfi : (freeze (insert i J) (Function.update c i ci) a) i = ci := by
    simp [freeze]
  unfold term
  rw [e0, e1, Finset.sum_congr rfl (fun η _ => by rw [e2 η])]
  by_cases hsmall : T.normalizedAbs (a i : F.Carrier) ≤ T.normalizedAbs (ci : F.Carrier)
  · have hnot : ¬ T.normalizedAbs (ci : F.Carrier) < T.normalizedAbs (a i : F.Carrier) :=
      not_lt.mpr hsmall
    simp only [hsmall, hnot, ite_true, ite_false, zero_mul, zero_add]
    have hb : T.normalizedAbs (((ci⁻¹ * a i : F.Carrierˣ)) : F.Carrier) ≤ 1 := by
      rw [Units.val_mul, T.normalizedAbs_mul, normalizedAbs_units_inv]
      have hc := T.normalizedAbs_pos ci.ne_zero
      rw [inv_mul_le_iff₀ hc, mul_one]
      exact hsmall
    have hd := hdil (freeze (insert i J) (Function.update c i ci) a) (by rw [hfi]; exact hci)
      (ci⁻¹ * a i) hb
    rw [coordinateRepresentation_apply, hpt] at hd
    rw [hd, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun η _ => ?_)
    ring
  · simp only [hsmall, ite_false, zero_mul, Finset.sum_const_zero, add_zero]
    have hlt : T.normalizedAbs (ci : F.Carrier) < T.normalizedAbs (a i : F.Carrier) :=
      lt_of_not_ge hsmall
    simp only [hlt, ite_true, one_mul]

/-- The induction over the unprocessed coordinates `S`, for an arbitrary predicate `E`
closed under sums. At every step the threshold of the dilation hypothesis is taken for
the current function `g`, so no common choice over several functions is needed. -/
theorem term_induction (W : FunctionSpace F n) (Y : Fin n → Finset (F.Carrierˣ → ℂ))
    (A : Fin n → (F.Carrierˣ → ℂ) → Module.End ℂ W.toSubmodule)
    (hD : ∀ i : Fin n, ∀ f : W.toSubmodule,
      ∃ ε : ℝ, 0 < ε ∧
        ∀ a : Torus F n, T.normalizedAbs (a i : F.Carrier) < ε →
          ∀ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 →
            (coordinateRepresentation W i b f).val a =
              ∑ η ∈ Y i, η b * (A i η f).val a)
    (M : Fin n → Set (F.Carrierˣ → ℂ))
    (hM : ∀ i, ∀ η ∈ Y i, ∀ b : F.Carrierˣ, (fun y => η (b * y)) ∈ M i)
    (E : (Torus F n → ℂ) → Prop) (hE0 : E 0) (hEadd : ∀ u v, E u → E v → E (u + v))
    (hterm : ∀ (J : Finset (Fin n)) (r : Fin n → ℝ) (γ : Fin n → F.Carrierˣ → ℂ)
      (c : Torus F n) (g : W.toSubmodule), (∀ i, 0 < r i) → (∀ i ∈ J, γ i ∈ M i) →
        E (term T ∅ J r γ c g.val))
    (S : Finset (Fin n)) :
    ∀ (J : Finset (Fin n)) (r : Fin n → ℝ) (γ : Fin n → F.Carrierˣ → ℂ) (c : Torus F n)
      (g : W.toSubmodule), Disjoint J S → (∀ i, 0 < r i) → (∀ i ∈ J, γ i ∈ M i) →
        E (term T S J r γ c g.val) := by
  induction S using Finset.induction_on with
  | empty =>
    intro J r γ c g _ hr hγ
    exact hterm J r γ c g hr hγ
  | insert i S hiS ih =>
    intro J r γ c g hJS hr hγ
    have hiJ : i ∉ J := fun h => Finset.disjoint_left.mp hJS h (Finset.mem_insert_self i S)
    have hJS' : Disjoint J S := Finset.disjoint_of_subset_right (Finset.subset_insert i S) hJS
    obtain ⟨ε, hε, hdil⟩ := hD i g
    obtain ⟨ci, hci⟩ := exists_unit_normalizedAbs_lt T hε
    have hr' : ∀ k, 0 < Function.update r i (T.normalizedAbs (ci : F.Carrier)) k := by
      intro k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self]
        exact T.normalizedAbs_pos ci.ne_zero
      · rw [Function.update_of_ne hk]
        exact hr k
    have heq : term T (insert i S) J r γ c g.val =
        term T S J (Function.update r i (T.normalizedAbs (ci : F.Carrier))) γ c g.val +
          ∑ η ∈ Y i, term T S (insert i J)
            (Function.update r i (T.normalizedAbs (ci : F.Carrier)))
            (Function.update γ i (fun y => η (ci⁻¹ * y))) (Function.update c i ci)
            (A i η g).val := by
      funext a
      rw [Pi.add_apply, Finset.sum_apply]
      exact term_insert T W Y A hiJ hiS r γ c g ci hci hdil a
    rw [heq]
    refine hEadd _ _ (ih J _ γ c g hJS' hr' hγ) ?_
    refine Finset.sum_induction _ E hEadd hE0 (fun η hη => ?_)
    refine ih (insert i J) _ _ _ _ ?_ hr' ?_
    · exact Finset.disjoint_insert_left.mpr ⟨hiS, hJS'⟩
    · intro k hk
      by_cases hki : k = i
      · subst hki
        rw [Function.update_self]
        exact hM k η hη ci⁻¹
      · rw [Function.update_of_ne hki]
        exact hγ k ((Finset.mem_insert.mp hk).resolve_left hki)

/-- Every function is the term with all coordinates unprocessed. -/
theorem term_univ (g : Torus F n → ℂ) :
    term T Finset.univ ∅ 1 1 1 g = g := by
  funext a
  have hfr : freeze (∅ : Finset (Fin n)) (1 : Torus F n) a = a := by
    funext i
    simp [freeze]
  simp [term, factor, hfr]

/-! ### Schwartz–Bruhat coefficients on compact open boxes -/

theorem isOpen_le {ρ : ℝ} (hρ : 0 < ρ) :
    letI := T.topology
    IsOpen {y : F.Carrier | T.normalizedAbs y ≤ ρ} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hU : IsOpen {z : F.Carrier | T.normalizedAbs (z - y) < ρ} :=
    isOpen_lt (T.continuous_normalizedAbs.comp (continuous_id.sub continuous_const))
      continuous_const
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · change T.normalizedAbs (y - y) < ρ
    rw [sub_self, T.normalizedAbs_zero]
    exact hρ
  · intro z hz
    have h := T.normalizedAbs_add_le_max y (z - y)
    rw [add_sub_cancel] at h
    exact h.trans (max_le hy (le_of_lt hz))

theorem isClopen_le {ρ : ℝ} (hρ : 0 < ρ) :
    letI := T.topology
    IsClopen {y : F.Carrier | T.normalizedAbs y ≤ ρ} := by
  let := T.topology
  exact ⟨isClosed_le T.continuous_normalizedAbs continuous_const, isOpen_le T hρ⟩

/-- Closed balls for the normalized absolute value are compact. -/
theorem isCompact_le (ρ : ℝ) :
    letI := T.topology
    IsCompact {y : F.Carrier | T.normalizedAbs y ≤ ρ} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hρ' : 0 < max ρ 1 := lt_max_of_lt_right one_pos
  obtain ⟨d, hd⟩ := exists_unit_normalizedAbs_lt T (inv_pos.mpr hρ')
  have hK : IsCompact ((fun z : F.Carrier => ((d⁻¹ : F.Carrierˣ) : F.Carrier) * z) ''
      (T.Integers : Set F.Carrier)) :=
    T.isCompact_integers.image (continuous_const.mul continuous_id)
  refine hK.of_isClosed_subset (isClosed_le T.continuous_normalizedAbs continuous_const) ?_
  intro y hy
  refine ⟨(d : F.Carrier) * y, ?_, ?_⟩
  · change (d : F.Carrier) * y ∈ T.Integers
    rw [← T.normalizedAbs_le_one_iff_mem_integers, T.normalizedAbs_mul]
    have hdn := T.normalizedAbs_nonneg (d : F.Carrier)
    have hy' : T.normalizedAbs y ≤ max ρ 1 := hy.trans (le_max_left _ _)
    calc T.normalizedAbs (d : F.Carrier) * T.normalizedAbs y
        ≤ T.normalizedAbs (d : F.Carrier) * max ρ 1 := mul_le_mul_of_nonneg_left hy' hdn
      _ ≤ (max ρ 1)⁻¹ * max ρ 1 := mul_le_mul_of_nonneg_right hd.le hρ'.le
      _ = 1 := inv_mul_cancel₀ hρ'.ne'
  · change ((d⁻¹ : F.Carrierˣ) : F.Carrier) * ((d : F.Carrier) * y) = y
    rw [← mul_assoc, Units.inv_mul, one_mul]

open Classical in
/-- A unit with the given value, when the value is nonzero. -/
def unitOf (y : F.Carrier) : F.Carrierˣ :=
  if h : y = 0 then 1 else Units.mk0 y h

theorem unitOf_val (u : F.Carrierˣ) : unitOf (u : F.Carrier) = u := by
  simp [unitOf, u.ne_zero]

theorem val_unitOf {y : F.Carrier} (hy : y ≠ 0) : ((unitOf y : F.Carrierˣ) : F.Carrier) = y := by
  simp [unitOf, hy]

theorem continuousAt_unitOf {y : F.Carrier} (hy : y ≠ 0) :
    letI := T.topology
    ContinuousAt unitOf y := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  rw [Units.isEmbedding_val₀.isInducing.continuousAt_iff]
  refine continuousAt_id.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hy] with z hz
  exact (val_unitOf hz).symm

/-- The torus point with the coordinates of `J` taken from `c` and the others from `x`. -/
def fill (J : Finset (Fin n)) (c : Torus F n) (x : Fin n → F.Carrier) : Torus F n :=
  fun i => if i ∈ J then c i else unitOf (x i)

/-- The admissible values of coordinate `i`: small on `J`, large off `J`. -/
def boxSet (J : Finset (Fin n)) (r : Fin n → ℝ) (i : Fin n) : Set F.Carrier :=
  if i ∈ J then {y | T.normalizedAbs y ≤ r i} else {y | r i < T.normalizedAbs y}

/-- The box of all coordinates with admissible values. -/
def box (J : Finset (Fin n)) (r : Fin n → ℝ) : Set (Fin n → F.Carrier) :=
  {x | ∀ i, x i ∈ boxSet T J r i}

theorem isClopen_box (J : Finset (Fin n)) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    letI := T.topology
    IsClopen (box T J r) := by
  let := T.topology
  have hset : box T J r = ⋂ i, (fun x : Fin n → F.Carrier => x i) ⁻¹' boxSet T J r i := by
    ext x
    simp [box]
  rw [hset]
  refine isClopen_iInter_of_finite (fun i => IsClopen.preimage ?_ (continuous_apply i))
  unfold boxSet
  split_ifs
  · exact isClopen_le T (hr i)
  · have h := (isClopen_le T (hr i)).compl
    convert h using 1
    ext y
    simp

open Classical in
/-- The coefficient of the terminal stage: `g` at the filled point on the box, zero off it. -/
def boxCoeff (J : Finset (Fin n)) (r : Fin n → ℝ) (c : Torus F n) (g : Torus F n → ℂ)
    (x : Fin n → F.Carrier) : ℂ :=
  if x ∈ box T J r then g (fill J c x) else 0

theorem boxCoeff_mem (W : FunctionSpace F n) (hLC : IsLocallyConstantSpace W T)
    (hUS : HasCoordinateUpperSupport W T) (J : Finset (Fin n)) {r : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (c : Torus F n) (g : W.toSubmodule) :
    letI := T.topology
    boxCoeff T J r c g.val ∈ HarmonicAnalysis.schwartzBruhatSubmodule (Fin n → F.Carrier) := by
  let := T.topology
  classical
  have hbox := isClopen_box T J hr
  -- Off `J`, box coordinates are nonzero.
  have hne : ∀ x ∈ box T J r, ∀ i ∉ J, x i ≠ 0 := by
    intro x hx i hi h0
    have h := hx i
    simp only [boxSet, hi, ite_false, Set.mem_ofPred_eq, h0, T.normalizedAbs_zero] at h
    exact absurd h (not_lt.mpr (hr i).le)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ box T J r
    · have hfill : ContinuousAt (fill J c) x := by
        refine continuousAt_pi.mpr (fun i => ?_)
        by_cases hi : i ∈ J
        · simp only [fill, hi, ite_true]
          exact continuousAt_const
        · simp only [fill, hi, ite_false]
          exact ContinuousAt.comp (f := fun y : Fin n → F.Carrier => y i)
            (continuousAt_unitOf T (hne x hx i hi)) (continuous_apply i).continuousAt
      have hg := (IsLocallyConstant.iff_eventually_eq _).mp (hLC g) (fill J c x)
      filter_upwards [hbox.isOpen.mem_nhds hx, hfill.eventually hg] with y hy hgy
      simp only [boxCoeff, hy, hx, ite_true]
      exact hgy
    · filter_upwards [hbox.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.mem_compl_iff] at hy
      simp only [boxCoeff, hx, hy, ite_false]
  · choose R hRpos hR using fun i => hUS g i
    let ρ : Fin n → ℝ := fun i => if i ∈ J then r i else R i
    refine HasCompactSupport.intro' (K := Set.univ.pi fun i => {y | T.normalizedAbs y ≤ ρ i})
      (isCompact_univ_pi fun i => isCompact_le T (ρ i))
      (isClosed_set_pi fun i _ => isClosed_le T.continuous_normalizedAbs continuous_const) ?_
    intro x hxK
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, true_implies, not_forall,
      not_le] at hxK
    obtain ⟨i, hi⟩ := hxK
    by_cases hx : x ∈ box T J r
    · simp only [boxCoeff, hx, ite_true]
      have hxi := hx i
      by_cases hiJ : i ∈ J
      · simp only [boxSet, hiJ, ite_true, Set.mem_ofPred_eq] at hxi
        simp only [ρ, hiJ, ite_true] at hi
        exact absurd hxi (not_le.mpr hi)
      · apply hR i
        simp only [ρ, hiJ, ite_false] at hi
        simp only [fill, hiJ, ite_false, val_unitOf (hne x hx i hiJ)]
        exact hi
    · simp only [boxCoeff, hx, ite_false]

/-- The terminal term is the box coefficient times a product of one-coordinate functions. -/
theorem term_empty_eq (J : Finset (Fin n)) (r : Fin n → ℝ) (γ : Fin n → F.Carrierˣ → ℂ)
    (c : Torus F n) (g : Torus F n → ℂ) (a : Torus F n) :
    term T ∅ J r γ c g a =
      boxCoeff T J r c g (fun i => (a i : F.Carrier)) *
        ∏ i, (if i ∈ J then γ i else 1) (a i) := by
  classical
  unfold term boxCoeff
  by_cases hx : (fun i => (a i : F.Carrier)) ∈ box T J r
  · simp only [hx, ite_true]
    rw [mul_comm]
    have hfr : fill J c (fun i => (a i : F.Carrier)) = freeze J c a := by
      funext i
      simp [fill, freeze, unitOf_val]
    rw [hfr]
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hxi := hx i
    by_cases hi : i ∈ J
    · simp only [boxSet, hi, ite_true, Set.mem_ofPred_eq] at hxi
      simp [factor, hi, hxi]
    · simp only [boxSet, hi, ite_false, Set.mem_ofPred_eq] at hxi
      simp [factor, hi, hxi]
  · simp only [hx, ite_false, zero_mul]
    simp only [box, Set.mem_ofPred_eq, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    have h0 : factor T ∅ J r γ i (a i) = 0 := by
      by_cases hiJ : i ∈ J
      · simp only [boxSet, hiJ, ite_true, Set.mem_ofPred_eq] at hi
        simp [factor, hiJ, hi]
      · simp only [boxSet, hiJ, ite_false, Set.mem_ofPred_eq] at hi
        simp [factor, hiJ, hi]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul]


/-! ### Finite families of one-coordinate functions -/

/-- The product of one-coordinate functions over all coordinates. -/
def prodFun (σ : Fin n → F.Carrierˣ → ℂ) (a : Torus F n) : ℂ :=
  ∏ i, σ i (a i)

/-- The span of the constant one and of all left translates of members of `Y`. -/
def transSpan (Y : Finset (F.Carrierˣ → ℂ)) : Submodule ℂ (F.Carrierˣ → ℂ) :=
  Submodule.span ℂ (insert 1 {h | ∃ η ∈ Y, ∃ b : F.Carrierˣ, h = fun y => η (b * y)})

theorem one_mem_transSpan (Y : Finset (F.Carrierˣ → ℂ)) :
    (1 : F.Carrierˣ → ℂ) ∈ transSpan Y :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem translate_mem_transSpan {Y : Finset (F.Carrierˣ → ℂ)} {η : F.Carrierˣ → ℂ}
    (hη : η ∈ Y) (b : F.Carrierˣ) : (fun y => η (b * y)) ∈ transSpan Y :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨η, hη, b, rfl⟩)

/-- The span is stable under left translation. -/
theorem translate_mem_of_mem {Y : Finset (F.Carrierˣ → ℂ)} {h : F.Carrierˣ → ℂ}
    (hh : h ∈ transSpan Y) (b : F.Carrierˣ) : (fun y => h (b * y)) ∈ transSpan Y := by
  have hle : transSpan Y ≤
      (transSpan Y).comap (LinearMap.funLeft ℂ ℂ (fun y : F.Carrierˣ => b * y)) := by
    refine Submodule.span_le.mpr ?_
    rintro k (rfl | ⟨η, hη, b', rfl⟩)
    · exact one_mem_transSpan Y
    · change (fun y => η (b' * (b * y))) ∈ transSpan Y
      have heq : (fun y => η (b' * (b * y))) = fun y => η ((b' * b) * y) := by
        funext y
        rw [mul_assoc]
      rw [heq]
      exact translate_mem_transSpan hη (b' * b)
  exact hle hh

theorem continuous_of_mem_transSpan {Y : Finset (F.Carrierˣ → ℂ)}
    (hY : letI := T.topology; ∀ η ∈ Y, Continuous η) {h : F.Carrierˣ → ℂ}
    (hh : h ∈ transSpan Y) :
    letI := T.topology
    Continuous h := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  induction hh using Submodule.span_induction with
  | mem k hk =>
    rcases hk with rfl | ⟨η, hη, b, rfl⟩
    · exact continuous_const
    · exact (hY η hη).comp (continuous_const.mul continuous_id)
  | zero => exact continuous_const
  | add u v _ _ hu hv => exact hu.add hv
  | smul z u _ hu => exact hu.const_smul z

theorem fg_transSpan {Y : Finset (F.Carrierˣ → ℂ)}
    (hY : ∀ η ∈ Y, FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a)))) :
    (transSpan Y).FG := by
  let N : (F.Carrierˣ → ℂ) → Submodule ℂ (F.Carrierˣ → ℂ) := fun η =>
    Submodule.span ℂ (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a))
  have hfg : (Submodule.span ℂ {(1 : F.Carrierˣ → ℂ)} ⊔ Y.sup N).FG :=
    (Submodule.fg_span_singleton _).sup
      (Submodule.fg_finset_sup Y N fun η hη =>
        (Submodule.fg_iff_finiteDimensional _).mpr (hY η hη))
  refine hfg.of_le (Submodule.span_le.mpr ?_)
  rintro k (rfl | ⟨η, hη, b, rfl⟩)
  · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  · exact Submodule.mem_sup_right (Finset.le_sup (f := N) hη (Submodule.subset_span ⟨b, rfl⟩))

/-- A product of one-coordinate functions from the spans of `B i` is a combination of
products of members of the `B i`. -/
theorem prod_expand (B : Fin n → Finset (F.Carrierˣ → ℂ)) {τ : Fin n → F.Carrierˣ → ℂ}
    (hτ : ∀ i, τ i ∈ Submodule.span ℂ (B i : Set (F.Carrierˣ → ℂ))) :
    ∃ κ : (Fin n → F.Carrierˣ → ℂ) → ℂ, ∀ a : Torus F n,
      ∏ i, τ i (a i) = ∑ σ ∈ Fintype.piFinset B, κ σ * prodFun σ a := by
  choose w _ hw using fun i => Submodule.mem_span_finset.mp (hτ i)
  refine ⟨fun σ => ∏ i, w i (σ i), fun a => ?_⟩
  have h1 : ∀ i, τ i (a i) = ∑ β ∈ B i, w i β * β (a i) := by
    intro i
    conv_lhs => rw [← hw i]
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.prod_mul_distrib]
  rfl

/-! ### Expansions with Schwartz–Bruhat coefficients -/

/-- Expansion with Schwartz–Bruhat coefficients over products from the families `B`. -/
def HasExpansion (B : Fin n → Finset (F.Carrierˣ → ℂ)) (h : Torus F n → ℂ) : Prop :=
  letI := T.topology
  ∃ Ψ : (Fin n → F.Carrierˣ → ℂ) → (Fin n → F.Carrier) → ℂ,
    (∀ σ, Ψ σ ∈ HarmonicAnalysis.schwartzBruhatSubmodule (Fin n → F.Carrier)) ∧
      ∀ a : Torus F n,
        h a = ∑ σ ∈ Fintype.piFinset B, Ψ σ (fun i => (a i : F.Carrier)) * prodFun σ a

theorem hasExpansion_zero (B : Fin n → Finset (F.Carrierˣ → ℂ)) : HasExpansion T B 0 := by
  let := T.topology
  refine ⟨0, fun σ => Submodule.zero_mem _, fun a => ?_⟩
  simp

theorem hasExpansion_add (B : Fin n → Finset (F.Carrierˣ → ℂ)) {u v : Torus F n → ℂ}
    (hu : HasExpansion T B u) (hv : HasExpansion T B v) : HasExpansion T B (u + v) := by
  let := T.topology
  obtain ⟨Ψ₁, hΨ₁, he₁⟩ := hu
  obtain ⟨Ψ₂, hΨ₂, he₂⟩ := hv
  refine ⟨Ψ₁ + Ψ₂, fun σ => Submodule.add_mem _ (hΨ₁ σ) (hΨ₂ σ), fun a => ?_⟩
  rw [Pi.add_apply, he₁ a, he₂ a, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [Pi.add_apply]
  ring

/-- The terminal terms have expansions. -/
theorem hasExpansion_term (W : FunctionSpace F n) (hLC : IsLocallyConstantSpace W T)
    (hUS : HasCoordinateUpperSupport W T) (Y B : Fin n → Finset (F.Carrierˣ → ℂ))
    (hB : ∀ i, Submodule.span ℂ (B i : Set (F.Carrierˣ → ℂ)) = transSpan (Y i))
    (J : Finset (Fin n)) (r : Fin n → ℝ) (γ : Fin n → F.Carrierˣ → ℂ) (c : Torus F n)
    (g : W.toSubmodule) (hr : ∀ i, 0 < r i) (hγ : ∀ i ∈ J, γ i ∈ transSpan (Y i)) :
    HasExpansion T B (term T ∅ J r γ c g.val) := by
  let := T.topology
  have hτ : ∀ i, (if i ∈ J then γ i else 1) ∈
      Submodule.span ℂ (B i : Set (F.Carrierˣ → ℂ)) := by
    intro i
    rw [hB i]
    by_cases hi : i ∈ J
    · simp only [hi, ite_true]
      exact hγ i hi
    · simp only [hi, ite_false]
      exact one_mem_transSpan _
  obtain ⟨κ, hκ⟩ := prod_expand B hτ
  refine ⟨fun σ => κ σ • boxCoeff T J r c g.val,
    fun σ => Submodule.smul_mem _ _ (boxCoeff_mem T W hLC hUS J hr c g), fun a => ?_⟩
  rw [term_empty_eq, hκ a, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Products of members of the `B i` are finite functions on the torus. -/
theorem isFiniteFunction_prodFun (Y : Fin n → Finset (F.Carrierˣ → ℂ))
    (hY : letI := T.topology; ∀ i, ∀ η ∈ Y i, Continuous η)
    (B : Fin n → Finset (F.Carrierˣ → ℂ))
    (hB : ∀ i, Submodule.span ℂ (B i : Set (F.Carrierˣ → ℂ)) = transSpan (Y i))
    (X : Finset (Torus F n → ℂ)) (hX : ∀ σ ∈ Fintype.piFinset B, prodFun σ ∈ X)
    {σ : Fin n → F.Carrierˣ → ℂ} (hσ : σ ∈ Fintype.piFinset B) :
    IsFiniteFunction T (prodFun σ) := by
  let := T.topology
  have hσM : ∀ i, σ i ∈ transSpan (Y i) := fun i => by
    rw [← hB i]
    exact Submodule.subset_span (Fintype.mem_piFinset.mp hσ i)
  refine ⟨?_, ?_⟩
  · show Continuous fun a : Torus F n => ∏ i, σ i (a i)
    exact continuous_finsetProd _ (fun i _ =>
      (continuous_of_mem_transSpan T (hY i) (hσM i)).comp (continuous_apply i))
  · have hle : Submodule.span ℂ (Set.range fun b : Torus F n => fun a => prodFun σ (b * a)) ≤
        Submodule.span ℂ (X : Set (Torus F n → ℂ)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨b, rfl⟩
      have hτ : ∀ i, (fun y => σ i (b i * y)) ∈
          Submodule.span ℂ (B i : Set (F.Carrierˣ → ℂ)) := fun i => by
        rw [hB i]
        exact translate_mem_of_mem (hσM i) (b i)
      obtain ⟨κ, hκ⟩ := prod_expand B hτ
      have heq : (fun a => prodFun σ (b * a)) =
          ∑ σ' ∈ Fintype.piFinset B, κ σ' • prodFun σ' := by
        funext a
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact hκ a
      show (fun a => prodFun σ (b * a)) ∈
        (Submodule.span ℂ (X : Set (Torus F n → ℂ)) : Set (Torus F n → ℂ))
      rw [heq, SetLike.mem_coe]
      exact Submodule.sum_mem _ (fun σ' hσ' =>
        Submodule.smul_mem _ _ (Submodule.subset_span (hX σ' hσ')))
    exact Submodule.finiteDimensional_of_le hle

end Langlands.Whittaker.JPSDilationAssembly

namespace Langlands.Whittaker

open JPSFunctionSpace JPSDilationAssembly

universe uF

/-- JPS (1979), Lemma (2.2.1), internal assembly step: one finite set of finite
functions, chosen before the function, expands every function of the space with
Schwartz–Bruhat coefficients on the whole additive space. -/
theorem jpsDilationAssembly : JPSDilationAssemblyStatement.{uF} := by
  intro p _ F T n W Y A hLC hUS hFF hD
  let := T.topology
  classical
  choose B hB using fun i => fg_transSpan (fun η hη => (hFF i η hη).2)
  let X : Finset (Torus F n → ℂ) := (Fintype.piFinset B).image prodFun
  have hX : ∀ σ ∈ Fintype.piFinset B, prodFun σ ∈ X :=
    fun σ hσ => Finset.mem_image_of_mem _ hσ
  refine ⟨X, ?_, fun f => ?_⟩
  · intro χ hχ
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hχ
    exact isFiniteFunction_prodFun T Y (fun i η hη => (hFF i η hη).1) B hB X hX hσ
  · have hE := term_induction T W Y A hD
      (fun i => (transSpan (Y i) : Set (F.Carrierˣ → ℂ)))
      (fun i η hη b => translate_mem_transSpan hη b) (HasExpansion T B)
      (hasExpansion_zero T B) (fun u v hu hv => hasExpansion_add T B hu hv)
      (fun J r γ c g hr hγ => hasExpansion_term T W hLC hUS Y B hB J r γ c g hr hγ)
      Finset.univ ∅ 1 1 1 f (Finset.disjoint_empty_left _) (fun _ => one_pos) (by simp)
    rw [term_univ] at hE
    obtain ⟨Ψ, hΨ, he⟩ := hE
    refine ⟨fun χ => ⟨∑ σ ∈ (Fintype.piFinset B).filter (fun σ => prodFun σ = χ), Ψ σ,
      Submodule.sum_mem _ (fun σ _ => hΨ σ)⟩, fun a => ?_⟩
    rw [he a, ← Finset.sum_fiberwise_of_maps_to hX]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    show _ = (∑ σ ∈ (Fintype.piFinset B).filter (fun σ => prodFun σ = χ), Ψ σ)
      (fun i => (a i : F.Carrier)) * χ a
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun σ hσ => ?_)
    rw [(Finset.mem_filter.mp hσ).2]

end Langlands.Whittaker
