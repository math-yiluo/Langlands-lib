import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.GroupCompletion

/-! # Completed Laurent polynomials under a Gauss norm at a positive radius -/

noncomputable section

universe u

namespace Langlands.Analytic

/-- Laurent polynomials over `K`, to be normed by the Gauss norm at radius `t`. -/
def GaussLaurent (K : Type u) [NormedField K] (_t : ℝ) : Type u := AddMonoidAlgebra K ℤ

namespace GaussLaurent

variable (K : Type u) [NormedField K] (t : ℝ)

instance : CommRing (GaussLaurent K t) := inferInstanceAs (CommRing (AddMonoidAlgebra K ℤ))

variable {K t}

/-- The finitely supported coefficient function. -/
def coeff (p : GaussLaurent K t) : ℤ →₀ K := AddMonoidAlgebra.coeff (R := K) (M := ℤ) p

/-- The Laurent monomial with exponent `k` and coefficient `a`. -/
def single (k : ℤ) (a : K) : GaussLaurent K t := AddMonoidAlgebra.single k a

@[ext] theorem ext {p q : GaussLaurent K t} (h : ∀ n, coeff p n = coeff q n) : p = q :=
  AddMonoidAlgebra.ext (R := K) (M := ℤ) (Finsupp.ext h)

@[simp] theorem coeff_zero (n : ℤ) : coeff (0 : GaussLaurent K t) n = 0 := rfl

@[simp] theorem coeff_add (p q : GaussLaurent K t) (n : ℤ) :
    coeff (p + q) n = coeff p n + coeff q n := rfl

@[simp] theorem coeff_neg (p : GaussLaurent K t) (n : ℤ) : coeff (-p) n = -coeff p n := rfl

@[simp] theorem coeff_sub (p q : GaussLaurent K t) (n : ℤ) :
    coeff (p - q) n = coeff p n - coeff q n := rfl

theorem coeff_single (k n : ℤ) (a : K) :
    coeff (single (t := t) k a) n = Finsupp.single k a n := rfl

theorem single_mul_single (k l : ℤ) (a b : K) :
    single (t := t) k a * single l b = single (k + l) (a * b) :=
  AddMonoidAlgebra.single_mul_single (R := K) (M := ℤ) k l a b

theorem one_eq_single : (1 : GaussLaurent K t) = single 0 1 := rfl

theorem coeff_mul (p q : GaussLaurent K t) (n : ℤ) :
    coeff (p * q) n = (coeff p).sum fun i a => (coeff q).sum fun j b =>
      if i + j = n then a * b else 0 := by
  classical
  exact AddMonoidAlgebra.coeff_mul (R := K) (M := ℤ) p q n

theorem coeff_single_zero_mul (a : K) (p : GaussLaurent K t) (n : ℤ) :
    coeff (single 0 a * p) n = a * coeff p n :=
  AddMonoidAlgebra.coeff_single_zero_mul (R := K) (M := ℤ) p a n

/-- The constant coefficients form a ring map from `K`. -/
def C : K →+* GaussLaurent K t := (AddMonoidAlgebra.singleZeroRingHom : K →+* AddMonoidAlgebra K ℤ)

theorem C_apply (a : K) : C (t := t) a = single 0 a := rfl

section Norm

variable [Fact (0 < t)]

theorem radius_pos : 0 < t := Fact.out

/-- The nonnegative weight `t ^ n` of the exponent `n`. -/
def weight (t : ℝ) [Fact (0 < t)] (n : ℤ) : NNReal := ⟨t ^ n, (zpow_pos radius_pos n).le⟩

@[simp] theorem coe_weight (n : ℤ) : ((weight t n : NNReal) : ℝ) = t ^ n := rfl

theorem weight_pos (n : ℤ) : 0 < weight t n := by
  rw [← NNReal.coe_pos, coe_weight]
  exact zpow_pos radius_pos n

/-- The Gauss norm: the largest weighted coefficient norm. -/
def gaussNNNorm (p : GaussLaurent K t) : NNReal :=
  (coeff p).support.sup fun n => ‖coeff p n‖₊ * weight t n

theorem gaussNNNorm_le_iff (p : GaussLaurent K t) (c : NNReal) :
    gaussNNNorm p ≤ c ↔ ∀ n, ‖coeff p n‖₊ * weight t n ≤ c := by
  rw [gaussNNNorm, Finset.sup_le_iff]
  constructor
  · intro h n
    by_cases hn : n ∈ (coeff p).support
    · exact h n hn
    · rw [Finsupp.notMem_support_iff.mp hn, nnnorm_zero, zero_mul]
      exact zero_le
  · exact fun h n _ => h n

theorem le_gaussNNNorm (p : GaussLaurent K t) (n : ℤ) :
    ‖coeff p n‖₊ * weight t n ≤ gaussNNNorm p :=
  (gaussNNNorm_le_iff p _).mp le_rfl n

theorem gaussNNNorm_lt_iff (p : GaussLaurent K t) {c : NNReal} (hc : 0 < c) :
    gaussNNNorm p < c ↔ ∀ n, ‖coeff p n‖₊ * weight t n < c := by
  rw [gaussNNNorm, Finset.sup_lt_iff hc]
  constructor
  · intro h n
    by_cases hn : n ∈ (coeff p).support
    · exact h n hn
    · rw [Finsupp.notMem_support_iff.mp hn, nnnorm_zero, zero_mul]
      exact hc
  · exact fun h n _ => h n

theorem exists_gaussNNNorm_eq (p : GaussLaurent K t) :
    ∃ n, gaussNNNorm p = ‖coeff p n‖₊ * weight t n := by
  rcases (coeff p).support.eq_empty_or_nonempty with h | h
  · refine ⟨0, ?_⟩
    have h0 : coeff p 0 = 0 := Finsupp.notMem_support_iff.mp (by simp [h])
    rw [gaussNNNorm, h, Finset.sup_empty, h0, nnnorm_zero, zero_mul]
    rfl
  · obtain ⟨n, -, hn⟩ := Finset.exists_mem_eq_sup _ h fun n => ‖coeff p n‖₊ * weight t n
    exact ⟨n, hn⟩

variable [IsUltrametricDist K]

/-- The Gauss norm as an additive group norm. -/
def gaussAddGroupNorm : AddGroupNorm (GaussLaurent K t) where
  toFun p := gaussNNNorm p
  map_zero' := by
    rw [NNReal.coe_eq_zero, ← nonpos_iff_eq_zero, gaussNNNorm_le_iff]
    intro n
    simp
  add_le' p q := by
    have h : gaussNNNorm (p + q) ≤ max (gaussNNNorm p) (gaussNNNorm q) := by
      rw [gaussNNNorm_le_iff]
      intro n
      rw [coeff_add]
      calc
        ‖coeff p n + coeff q n‖₊ * weight t n
            ≤ max ‖coeff p n‖₊ ‖coeff q n‖₊ * weight t n :=
          mul_le_mul_left (IsUltrametricDist.nnnorm_add_le_max _ _) _
        _ = max (‖coeff p n‖₊ * weight t n) (‖coeff q n‖₊ * weight t n) :=
          max_mul_of_nonneg _ _ zero_le
        _ ≤ max (gaussNNNorm p) (gaussNNNorm q) :=
          max_le_max (le_gaussNNNorm p n) (le_gaussNNNorm q n)
    exact_mod_cast h.trans (max_le_add_of_nonneg zero_le zero_le)
  neg' p := by
    congr 1
    apply le_antisymm
    · rw [gaussNNNorm_le_iff]
      intro n
      simpa using le_gaussNNNorm p n
    · rw [gaussNNNorm_le_iff]
      intro n
      simpa using le_gaussNNNorm (-p) n
  eq_zero_of_map_eq_zero' p hp := by
    rw [NNReal.coe_eq_zero] at hp
    ext n
    have h := le_gaussNNNorm p n
    rw [hp, nonpos_iff_eq_zero, mul_eq_zero] at h
    rcases h with h | h
    · simpa using h
    · exact absurd h (weight_pos n).ne'

instance : NormedAddCommGroup (GaussLaurent K t) :=
  (gaussAddGroupNorm (K := K) (t := t)).toNormedAddCommGroup

theorem norm_def (p : GaussLaurent K t) : ‖p‖ = (gaussNNNorm p : ℝ) := rfl

theorem norm_coeff_mul_le (p : GaussLaurent K t) (n : ℤ) :
    ‖coeff p n‖ * t ^ n ≤ ‖p‖ := by
  rw [norm_def, ← coe_weight, ← coe_nnnorm, ← NNReal.coe_mul, NNReal.coe_le_coe]
  exact le_gaussNNNorm p n

theorem norm_le_iff (p : GaussLaurent K t) {c : ℝ} (hc : 0 ≤ c) :
    ‖p‖ ≤ c ↔ ∀ n, ‖coeff p n‖ * t ^ n ≤ c := by
  lift c to NNReal using hc
  rw [norm_def, NNReal.coe_le_coe, gaussNNNorm_le_iff]
  refine forall_congr' fun n => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_weight]

theorem norm_lt_iff (p : GaussLaurent K t) {c : ℝ} (hc : 0 < c) :
    ‖p‖ < c ↔ ∀ n, ‖coeff p n‖ * t ^ n < c := by
  lift c to NNReal using hc.le
  rw [norm_def, NNReal.coe_lt_coe, gaussNNNorm_lt_iff p (by exact_mod_cast hc)]
  refine forall_congr' fun n => ?_
  rw [← NNReal.coe_lt_coe, NNReal.coe_mul, coe_nnnorm, coe_weight]

theorem exists_norm_eq (p : GaussLaurent K t) : ∃ n, ‖p‖ = ‖coeff p n‖ * t ^ n := by
  obtain ⟨n, hn⟩ := exists_gaussNNNorm_eq p
  refine ⟨n, ?_⟩
  rw [norm_def, hn, NNReal.coe_mul, coe_nnnorm, coe_weight]

theorem norm_single (k : ℤ) (a : K) : ‖single (t := t) k a‖ = ‖a‖ * t ^ k := by
  classical
  apply le_antisymm
  · rw [norm_le_iff _ (mul_nonneg (norm_nonneg a) (zpow_pos radius_pos k).le)]
    intro n
    rw [coeff_single, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · rw [norm_zero, zero_mul]
      exact mul_nonneg (norm_nonneg a) (zpow_pos radius_pos k).le
  · simpa [coeff_single] using norm_coeff_mul_le (single (t := t) k a) k

theorem norm_C (a : K) : ‖C (t := t) a‖ = ‖a‖ := by
  rw [C_apply, norm_single, zpow_zero, mul_one]

theorem norm_mul_le' (p q : GaussLaurent K t) : ‖p * q‖ ≤ ‖p‖ * ‖q‖ := by
  classical
  have hpq : 0 ≤ ‖p‖ * ‖q‖ := mul_nonneg (norm_nonneg p) (norm_nonneg q)
  rw [norm_le_iff _ hpq]
  intro n
  have hw : 0 < t ^ n := zpow_pos radius_pos n
  rw [← le_div_iff₀ hw, coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hpq hw.le)
  intro i _
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hpq hw.le)
  intro j _
  dsimp only
  split_ifs with hij
  · rw [le_div_iff₀ hw, norm_mul, ← hij, zpow_add₀ radius_pos.ne']
    calc
      ‖coeff p i‖ * ‖coeff q j‖ * (t ^ i * t ^ j)
          = (‖coeff p i‖ * t ^ i) * (‖coeff q j‖ * t ^ j) := by ring
      _ ≤ ‖p‖ * ‖q‖ := mul_le_mul (norm_coeff_mul_le p i) (norm_coeff_mul_le q j)
          (mul_nonneg (norm_nonneg _) (zpow_pos radius_pos j).le) (norm_nonneg p)
  · rw [norm_zero]
    exact div_nonneg hpq hw.le

instance : NormedCommRing (GaussLaurent K t) :=
  { (inferInstance : NormedAddCommGroup (GaussLaurent K t)),
    (inferInstance : CommRing (GaussLaurent K t)) with
    norm_mul_le := norm_mul_le' }

instance : IsUltrametricDist (GaussLaurent K t) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun p q => by
    rw [norm_le_iff _ (le_max_of_le_left (norm_nonneg p))]
    intro n
    rw [coeff_add]
    calc
      ‖coeff p n + coeff q n‖ * t ^ n ≤ max ‖coeff p n‖ ‖coeff q n‖ * t ^ n :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _)
          (zpow_pos radius_pos n).le
      _ = max (‖coeff p n‖ * t ^ n) (‖coeff q n‖ * t ^ n) :=
        max_mul_of_nonneg _ _ (zpow_pos radius_pos n).le
      _ ≤ max ‖p‖ ‖q‖ := max_le_max (norm_coeff_mul_le p n) (norm_coeff_mul_le q n)

/-- When no nonzero power of `t` is a norm from `K`, every nonzero Laurent
polynomial has a unique dominant monomial, strictly dominating the rest. -/
theorem exists_dominant (H : ∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n)
    (p : GaussLaurent K t) (hp : p ≠ 0) :
    ∃ k, ‖p‖ = ‖coeff p k‖ * t ^ k ∧ ‖p - single k (coeff p k)‖ < ‖p‖ := by
  classical
  obtain ⟨k, hk⟩ := exists_norm_eq p
  have hpos : 0 < ‖p‖ := norm_pos_iff.mpr hp
  refine ⟨k, hk, ?_⟩
  rw [norm_lt_iff _ hpos]
  intro n
  rw [coeff_sub, coeff_single, Finsupp.single_apply]
  split_ifs with hkn
  · rw [hkn, sub_self, norm_zero, zero_mul]
    exact hpos
  · rw [sub_zero]
    apply lt_of_le_of_ne (norm_coeff_mul_le p n)
    intro heq
    have hak : coeff p k ≠ 0 := by
      intro h0
      rw [h0, norm_zero, zero_mul] at hk
      exact hpos.ne' hk
    have hnk : k - n ≠ 0 := sub_ne_zero.mpr hkn
    apply H (coeff p n / coeff p k) (k - n) hnk
    have hak' : 0 < ‖coeff p k‖ := norm_pos_iff.mpr hak
    have htn : 0 < t ^ n := zpow_pos radius_pos n
    rw [norm_div, zpow_sub₀ radius_pos.ne', div_eq_div_iff hak'.ne' htn.ne']
    linarith
end Norm

end GaussLaurent

/-- The metric completion of an ultrametric seminormed group is ultrametric. -/
instance completion_isUltrametricDist {E : Type*} [SeminormedAddCommGroup E]
    [IsUltrametricDist E] : IsUltrametricDist (UniformSpace.Completion E) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
    UniformSpace.Completion.induction_on₂ x y
      (isClosed_le (continuous_norm.comp continuous_add)
        ((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)))
      fun a b => by
        rw [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe,
          UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
        exact IsUltrametricDist.norm_add_le_max a b

/-- Ultrametric bound for a difference. -/
theorem ultrametric_norm_sub_le_max {E : Type*} [SeminormedAddCommGroup E]
    [IsUltrametricDist E] (x y : E) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

/-- The completion of the Laurent polynomials under the Gauss norm at `t`. -/
abbrev CompletedGaussLaurent (K : Type u) [NormedField K] [IsUltrametricDist K]
    (t : ℝ) [Fact (0 < t)] : Type u :=
  UniformSpace.Completion (GaussLaurent K t)

namespace CompletedGaussLaurent

open GaussLaurent

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {t : ℝ} [Fact (0 < t)]

/-- The isometric scalar inclusion as constant Laurent polynomials. -/
def ι : K →+* CompletedGaussLaurent K t :=
  (UniformSpace.Completion.coeRingHom : GaussLaurent K t →+* _).comp GaussLaurent.C

theorem ι_apply (a : K) :
    ι (t := t) a = ((GaussLaurent.single 0 a : GaussLaurent K t) :
      CompletedGaussLaurent K t) := rfl

theorem norm_ι (a : K) : ‖ι (t := t) a‖ = ‖a‖ := by
  rw [ι_apply, UniformSpace.Completion.norm_coe, norm_single, zpow_zero, mul_one]

/-- The completed Laurent variable. -/
def X : CompletedGaussLaurent K t := ((GaussLaurent.single 1 1 : GaussLaurent K t) :
  CompletedGaussLaurent K t)

theorem norm_X : ‖(X : CompletedGaussLaurent K t)‖ = t := by
  rw [X, UniformSpace.Completion.norm_coe, norm_single, norm_one, one_mul, zpow_one]

theorem norm_one' : ‖(1 : CompletedGaussLaurent K t)‖ = 1 := by
  rw [← UniformSpace.Completion.coe_one, UniformSpace.Completion.norm_coe, one_eq_single,
    norm_single, norm_one, zpow_zero, mul_one]

instance : Nontrivial (CompletedGaussLaurent K t) :=
  nontrivial_of_ne 1 0 fun h => by
    have h1 := (norm_one' (K := K) (t := t))
    rw [h, norm_zero] at h1
    exact zero_ne_one h1

/-- Under the value-group condition, every nonzero element is a unit whose
inverse has norm at most the reciprocal norm. -/
theorem exists_mul_eq_one_norm_le (H : ∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n)
    (x : CompletedGaussLaurent K t) (hx : x ≠ 0) :
    ∃ v, x * v = 1 ∧ ‖v‖ ≤ ‖x‖⁻¹ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨p, hp⟩ :=
    Metric.denseRange_iff.mp UniformSpace.Completion.denseRange_coe x ‖x‖ hxpos
  rw [dist_eq_norm] at hp
  have hpx : ‖p‖ = ‖x‖ := by
    rw [← UniformSpace.Completion.norm_coe]
    apply le_antisymm
    · calc
        ‖(p : CompletedGaussLaurent K t)‖ = ‖x - (x - p)‖ := by rw [sub_sub_cancel]
        _ ≤ max ‖x‖ ‖x - p‖ := ultrametric_norm_sub_le_max _ _
        _ = ‖x‖ := max_eq_left hp.le
    · by_contra hlt
      push Not at hlt
      have hle : ‖x‖ ≤ max ‖x - p‖ ‖(p : CompletedGaussLaurent K t)‖ := by
        calc
          ‖x‖ = ‖(x - p) + p‖ := by rw [sub_add_cancel]
          _ ≤ _ := IsUltrametricDist.norm_add_le_max _ _
      exact (max_lt hp hlt).not_ge hle
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpx
    exact hxpos.ne' hpx.symm
  obtain ⟨k, hk, hdom⟩ := exists_dominant H p hp0
  have ha : coeff p k ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul, hpx] at hk
    exact hxpos.ne' hk
  let u : (GaussLaurent K t)ˣ :=
    ⟨single k (coeff p k), single (-k) (coeff p k)⁻¹,
      by rw [single_mul_single, add_neg_cancel, mul_inv_cancel₀ ha, one_eq_single],
      by rw [single_mul_single, neg_add_cancel, inv_mul_cancel₀ ha, one_eq_single]⟩
  let U : (CompletedGaussLaurent K t)ˣ :=
    Units.map (UniformSpace.Completion.coeRingHom : GaussLaurent K t →+* _).toMonoidHom u
  have hU : (U : CompletedGaussLaurent K t) =
      ((single k (coeff p k) : GaussLaurent K t) : CompletedGaussLaurent K t) := rfl
  have hUinv : ((U⁻¹ : (CompletedGaussLaurent K t)ˣ) : CompletedGaussLaurent K t) =
      ((single (-k) (coeff p k)⁻¹ : GaussLaurent K t) : CompletedGaussLaurent K t) := rfl
  have hnormUinv : ‖((U⁻¹ : (CompletedGaussLaurent K t)ˣ) : CompletedGaussLaurent K t)‖ =
      ‖x‖⁻¹ := by
    rw [hUinv, UniformSpace.Completion.norm_coe, norm_single, norm_inv, zpow_neg, ← hpx, hk,
      mul_inv]
  have hxU : ‖x - U‖ < ‖x‖ := by
    calc
      ‖x - U‖ = ‖(x - p) + ((p : CompletedGaussLaurent K t) - U)‖ := by
        rw [sub_add_sub_cancel]
      _ ≤ max ‖x - p‖ ‖(p : CompletedGaussLaurent K t) - U‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      _ < ‖x‖ := by
        apply max_lt hp
        rw [hU, ← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe, ← hpx]
        exact hdom
  let V := Units.ofNearby U x (by rw [hnormUinv, inv_inv]; exact hxU)
  have hV : (V : CompletedGaussLaurent K t) = x := rfl
  set v : CompletedGaussLaurent K t := ((V⁻¹ : (CompletedGaussLaurent K t)ˣ) :
    CompletedGaussLaurent K t) with hvdef
  set u' : CompletedGaussLaurent K t := ((U⁻¹ : (CompletedGaussLaurent K t)ˣ) :
    CompletedGaussLaurent K t) with hu'def
  have hxv : x * v = 1 := by
    rw [← hV]
    exact V.mul_inv
  have huU : u' * U = 1 := U.inv_mul
  refine ⟨v, hxv, ?_⟩
  have hv : v = u' - u' * (x - U) * v := by linear_combination u' * hxv - v * huU
  have h1 : ‖v‖ ≤ max ‖u'‖ ‖u' * (x - U) * v‖ := by
    calc
      ‖v‖ = ‖u' - u' * (x - U) * v‖ := congrArg norm hv
      _ ≤ _ := ultrametric_norm_sub_le_max _ _
  have h2 : ‖u' * (x - U) * v‖ ≤ ‖u'‖ * ‖x - U‖ * ‖v‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have h3 : ‖u'‖ * ‖x - U‖ < 1 := by
    rw [hnormUinv, inv_mul_lt_iff₀ hxpos, mul_one]
    exact hxU
  rw [← hnormUinv]
  by_contra hlt
  push Not at hlt
  have hvpos : 0 < ‖v‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  rcases le_max_iff.mp h1 with h | h
  · exact hlt.not_ge h
  · have : ‖v‖ < ‖v‖ :=
      calc
        ‖v‖ ≤ ‖u'‖ * ‖x - U‖ * ‖v‖ := h.trans h2
        _ < 1 * ‖v‖ := mul_lt_mul_of_pos_right h3 hvpos
        _ = ‖v‖ := one_mul _
    exact this.false

theorem isUnit_or_eq_zero (H : ∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n)
    (x : CompletedGaussLaurent K t) : IsUnit x ∨ x = 0 := by
  by_cases hx : x = 0
  · exact Or.inr hx
  · obtain ⟨v, hxv, -⟩ := exists_mul_eq_one_norm_le H x hx
    exact Or.inl (IsUnit.of_mul_eq_one v hxv)

theorem norm_mul_eq (H : ∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n)
    (x y : CompletedGaussLaurent K t) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  apply le_antisymm (norm_mul_le x y)
  by_cases hx : x = 0
  · rw [hx, zero_mul, norm_zero, zero_mul]
  obtain ⟨v, hxv, hv⟩ := exists_mul_eq_one_norm_le H x hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy : ‖y‖ ≤ ‖x‖⁻¹ * ‖x * y‖ :=
    calc
      ‖y‖ = ‖v * (x * y)‖ := by rw [← mul_assoc, mul_comm v x, hxv, one_mul]
      _ ≤ ‖v‖ * ‖x * y‖ := norm_mul_le _ _
      _ ≤ ‖x‖⁻¹ * ‖x * y‖ := mul_le_mul_of_nonneg_right hv (norm_nonneg _)
  rw [inv_mul_eq_div, le_div_iff₀ hxpos] at hy
  linarith

/-- The field structure on the completed Laurent ring under the value-group condition. -/
abbrev field (H : ∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n) :
    Field (CompletedGaussLaurent K t) :=
  Field.ofIsUnitOrEqZero (isUnit_or_eq_zero H)

/-- The completed Laurent field with its multiplicative Gauss norm. -/
abbrev normedField (H : ∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n) :
    NormedField (CompletedGaussLaurent K t) :=
  { (inferInstance : NormedCommRing (CompletedGaussLaurent K t)), field H with
    norm_mul := norm_mul_eq H }

section Retraction

/-- The constant coefficient of a Laurent polynomial. -/
def constCoeff : GaussLaurent K t →+ K where
  toFun p := coeff p 0
  map_zero' := rfl
  map_add' _ _ := rfl

theorem norm_constCoeff_le (p : GaussLaurent K t) : ‖constCoeff p‖ ≤ ‖p‖ := by
  change ‖coeff p 0‖ ≤ ‖p‖
  simpa using norm_coeff_mul_le p 0

theorem continuous_constCoeff : Continuous (constCoeff (K := K) (t := t)) :=
  AddMonoidHomClass.continuous_of_bound constCoeff 1 fun p => by
    rw [one_mul]
    exact norm_constCoeff_le p

variable [CompleteSpace K]

/-- The continuous extension of the constant coefficient. -/
def retraction : CompletedGaussLaurent K t →+ K :=
  constCoeff.extension continuous_constCoeff

theorem retraction_coe (p : GaussLaurent K t) : retraction (p : CompletedGaussLaurent K t) =
    coeff p 0 :=
  AddMonoidHom.extension_coe _ _ p

theorem continuous_retraction : Continuous (retraction (K := K) (t := t)) :=
  AddMonoidHom.continuous_extension _ _

theorem norm_retraction_le (x : CompletedGaussLaurent K t) : ‖retraction x‖ ≤ ‖x‖ :=
  UniformSpace.Completion.induction_on x
    (isClosed_le (continuous_norm.comp continuous_retraction) continuous_norm)
    fun p => by
      rw [retraction_coe, UniformSpace.Completion.norm_coe]
      exact norm_constCoeff_le p

theorem retraction_ι_mul (a : K) (x : CompletedGaussLaurent K t) :
    retraction (ι a * x) = a * retraction x :=
  UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_retraction.comp (continuous_const.mul continuous_id))
      (continuous_const.mul continuous_retraction))
    fun p => by
      rw [ι_apply, ← UniformSpace.Completion.coe_mul, retraction_coe, retraction_coe,
        coeff_single_zero_mul]

theorem retraction_one : retraction (1 : CompletedGaussLaurent K t) = 1 := by
  rw [← UniformSpace.Completion.coe_one, retraction_coe, one_eq_single, coeff_single,
    Finsupp.single_eq_same]

end Retraction

end CompletedGaussLaurent

end Langlands.Analytic
