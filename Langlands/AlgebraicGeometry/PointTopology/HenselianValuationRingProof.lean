import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsCompactProof
import Langlands.AlgebraicGeometry.PointTopology.HenselianIffSeparablyClosedProof
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormAmbient
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormReduction
import Langlands.Galois.Local.SeparableHenselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# A non-archimedean field is henselian exactly when its valuation ring is

Let `K` be a non-archimedean nontrivially normed field with closed unit ball `O`.

* If `O` is a henselian local ring, simple-root Hensel lifting holds for the norm valuation, and
  therefore Newton's form of Hensel's lemma. A separable element `x` of the completion has a
  minimal polynomial `g` with `g'(x) ≠ 0`. Approximating `x` by `a ∈ K` makes `g(a)` small
  compared with `g'(a)`, so `g` has a root in `K`, and `x ∈ K`. Thus `K` is separably closed in
  its completion, hence henselian.
* If `K` is henselian, the unique extension `w` of the norm to a separable closure `Ω` is
  invariant under `Gal(Ω/K)`. The valuation ring of `w` is henselian since `Ω` is separably
  closed, and simple-root Hensel lifting descends to `K` because Hensel roots are unique and
  Galois-fixed elements lie in `K`.
-/

noncomputable section

universe u

open Polynomial IsLocalRing Finset
open scoped NNReal

open Langlands.ClassFieldTheory.Local.SeparableInertiaNorm

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianValuationRing

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- The norm valuation of `K`. -/
local notation "ν" => (NormedField.valuation : Valuation K ℝ≥0)

theorem val_lt_one_iff (x : K) : ν x < 1 ↔ ‖x‖ < 1 := by
  rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]

theorem val_le_one_iff (x : K) : ν x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

theorem val_eq_one_iff (x : K) : ν x = 1 ↔ ‖x‖ = 1 := by
  rw [NormedField.valuation_apply, ← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one]

section Ring

variable {O : Subring K}

omit [IsUltrametricDist K] in
theorem eval_coe (f : O[X]) (b : O) :
    (f.map (algebraMap O K)).eval (b : K) = ((f.eval b : O) : K) := by
  rw [eval_map]
  exact eval₂_at_apply (algebraMap O K) b

variable (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
include hO

omit [IsUltrametricDist K] in
theorem nonunit_iff (x : O) : x ∈ nonunits O ↔ ‖(x : K)‖ < 1 := by
  rw [mem_nonunits_iff, HenselianUnitBall.isUnit_iff_norm_eq_one O hO]
  exact ⟨fun h => lt_of_le_of_ne ((hO _).1 x.2) h, ne_of_lt⟩

/-- The closed unit ball is a local ring. -/
theorem isLocalRing : IsLocalRing O := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [nonunit_iff hO] at ha hb ⊢
  exact (IsUltrametricDist.norm_add_le_max (a : K) b).trans_lt (max_lt ha hb)

/-- A henselian unit ball gives simple-root Hensel lifting for the norm valuation. -/
theorem valHensel_of_henselianLocalRing (hhen : HenselianLocalRing O) : ValHensel ν := by
  intro F hmon hint a₀ ha₀ hev hder
  obtain ⟨f, hf⟩ : ∃ f : O[X], f.map (algebraMap O K) = F :=
    (mem_lifts F).mp ((lifts_iff_coeff_lifts F).mpr fun n =>
      ⟨⟨F.coeff n, (hO _).2 ((val_le_one_iff _).1 (hint n))⟩, rfl⟩)
  have hinj : Function.Injective (algebraMap O K) := Subtype.val_injective
  have hfm : f.Monic := monic_of_injective hinj (by rw [hf]; exact hmon)
  let b₀ : O := ⟨a₀, (hO _).2 ((val_le_one_iff _).1 ha₀)⟩
  have hev' : f.eval b₀ ∈ maximalIdeal O := by
    rw [mem_maximalIdeal, nonunit_iff hO, ← eval_coe, hf]
    exact (val_lt_one_iff _).1 hev
  have hder' : IsUnit (f.derivative.eval b₀) := by
    rw [HenselianUnitBall.isUnit_iff_norm_eq_one O hO, ← eval_coe, ← derivative_map, hf]
    exact (val_eq_one_iff _).1 hder
  obtain ⟨b, hb, hsub⟩ := HenselianLocalRing.is_henselian f hfm b₀ hev' hder'
  refine ⟨b, ?_, ?_⟩
  · rw [← hf, eval_coe, hb.eq_zero]
    rfl
  · rw [mem_maximalIdeal, nonunit_iff hO] at hsub
    exact (val_lt_one_iff _).2 hsub

/-- Simple-root Hensel lifting for the norm valuation makes the unit ball henselian. -/
theorem henselianLocalRing_of_valHensel (h : ValHensel ν) : HenselianLocalRing O := by
  have hloc := isLocalRing hO
  refine { hloc with is_henselian := fun f hf b₀ h₁ h₂ => ?_ }
  rw [mem_maximalIdeal, nonunit_iff hO] at h₁
  rw [HenselianUnitBall.isUnit_iff_norm_eq_one O hO] at h₂
  obtain ⟨a, ha, hsub⟩ := h (f.map (algebraMap O K)) (hf.map _)
    (fun i => by rw [coeff_map, val_le_one_iff]; exact (hO _).1 (f.coeff i).2) (b₀ : K)
    ((val_le_one_iff _).2 ((hO _).1 b₀.2))
    (by rw [eval_coe, val_lt_one_iff]; exact h₁)
    (by rw [derivative_map, eval_coe, val_eq_one_iff]; exact h₂)
  rw [val_lt_one_iff] at hsub
  have haO : a ∈ O := by
    refine (hO _).2 ?_
    rw [show a = (a - b₀) + b₀ by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le hsub.le ((hO _).1 b₀.2))
  refine ⟨⟨a, haO⟩, ?_, ?_⟩
  · apply Subtype.val_injective
    rw [← eval_coe]
    exact ha
  · rw [mem_maximalIdeal, nonunit_iff hO]
    exact hsub

end Ring

/-- **Newton's form of Hensel's lemma**, deduced from simple-root lifting. -/
theorem exists_root_of_newton (hH : ValHensel ν) (g : K[X]) (a s : K)
    (hD : ‖g.eval a‖ < ‖g.derivative.eval a * s‖)
    (hk : ∀ k, 2 ≤ k → ‖(taylor a g).coeff k * s ^ k‖ ≤ ‖g.derivative.eval a * s‖) :
    ∃ r : K, g.eval r = 0 := by
  set D := g.derivative.eval a * s with hD_def
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, norm_zero] at hD
    exact (norm_nonneg _).not_gt hD
  set t := taylor a g with ht
  set N := t.natDegree + 2 with hN
  let c : ℕ → K := fun k => if 2 ≤ k then t.coeff k * s ^ k / D else 0
  have hc : ∀ k, ν (c k) ≤ 1 := by
    intro k
    rw [val_le_one_iff]
    by_cases h2 : 2 ≤ k
    · simp only [c, h2, ↓reduceIte, norm_div]
      exact div_le_one_of_le₀ (hk k h2) (norm_nonneg _)
    · simp [c, h2]
  have ha0 : ν (g.eval a / D) < 1 := by
    rw [val_lt_one_iff, norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hD0)).mpr hD
  obtain ⟨y, -, hy⟩ := exists_root_one_add_of_hensel hH N ha0 hc
  refine ⟨s * y + a, ?_⟩
  have hev : t.eval (s * y) = g.eval (s * y + a) := by rw [ht, taylor_eval]
  have hsplit : t.eval (s * y) = D * (g.eval a / D + y + ∑ k ∈ Ico 2 N, c k * y ^ k) := by
    rw [eval_eq_sum_range' (n := N) (by omega), range_eq_Ico,
      sum_eq_sum_Ico_succ_bot (by omega : 0 < N),
      sum_eq_sum_Ico_succ_bot (by omega : 0 + 1 < N), ht, taylor_coeff_zero, taylor_coeff_one,
      ← ht, mul_add, mul_add, mul_div_cancel₀ _ hD0, mul_sum, pow_zero, mul_one, zero_add,
      pow_one, ← add_assoc]
    congr 1
    · rw [hD_def]
      ring
    · refine sum_congr rfl fun k hk => ?_
      have h2 : 2 ≤ k := (mem_Ico.mp hk).1
      simp only [c, h2, ↓reduceIte]
      field_simp
      ring
  rw [← hev, hsplit, hy, mul_zero]

local notation "K̂" => UniformSpace.Completion K

/-- **Simple-root Hensel lifting makes `K` separably closed in its completion.** -/
theorem separableClosure_eq_bot (hH : ValHensel ν) : separableClosure K K̂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_separableClosure_iff] at hx
  have hint : IsIntegral K x := hx.isIntegral
  have hgx : aeval x (minpoly K x) = 0 := minpoly.aeval K x
  have hd : aeval x (derivative (minpoly K x)) ≠ 0 := hx.aeval_derivative_ne_zero hgx
  set g := minpoly K x with hg
  set n := g.natDegree with hn
  set δ := ‖aeval x (derivative g)‖ / 2 with hδ
  have hδ0 : 0 < δ := by
    have := norm_pos_iff.mpr hd
    rw [hδ]
    positivity
  have hterm : ∀ j ∈ range (n + 1), 0 ≤ ‖aeval x (hasseDeriv j g)‖ + 1 := fun j _ => by
    positivity
  set C := 1 + ∑ k ∈ range (n + 1), (‖aeval x (hasseDeriv k g)‖ + 1) with hC
  have hC1 : 1 ≤ C := by
    have := sum_nonneg hterm
    linarith
  have hCk : ∀ k ∈ range (n + 1), ‖aeval x (hasseDeriv k g)‖ + 1 ≤ C := fun k hk => by
    have := single_le_sum hterm hk
    linarith
  have hC0 : 0 < C := by linarith
  obtain ⟨s, hs0, hs⟩ := NormedField.exists_norm_lt K (show 0 < min 1 (δ / C) by positivity)
  have hs1 : ‖s‖ < 1 := hs.trans_le (min_le_left _ _)
  have hsδ : ‖s‖ < δ / C := hs.trans_le (min_le_right _ _)
  let V : Set K̂ := ({y | δ < ‖aeval y (derivative g)‖} ∩ {y | ‖aeval y g‖ < δ * ‖s‖}) ∩
    ⋂ k ∈ range (n + 1), {y | ‖aeval y (hasseDeriv k g)‖ < ‖aeval x (hasseDeriv k g)‖ + 1}
  have hV : IsOpen V := by
    refine ((isOpen_lt continuous_const ?_).inter (isOpen_lt ?_ continuous_const)).inter
      (isOpen_biInter_finset fun k _ => isOpen_lt ?_ continuous_const)
    · exact continuous_norm.comp (Polynomial.continuous_aeval _)
    · exact continuous_norm.comp (Polynomial.continuous_aeval _)
    · exact continuous_norm.comp (Polynomial.continuous_aeval _)
  have hxV : x ∈ V := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change δ < ‖aeval x (derivative g)‖
      have := norm_pos_iff.mpr hd
      linarith
    · change ‖aeval x g‖ < δ * ‖s‖
      rw [hgx, norm_zero]
      positivity
    · simp only [Set.mem_iInter]
      intro k _
      exact lt_add_one ‖aeval x (hasseDeriv k g)‖
  obtain ⟨a, haV⟩ := UniformSpace.Completion.denseRange_coe.exists_mem_open hV ⟨x, hxV⟩
  have hcoe : ∀ p : K[X], ‖aeval (a : K̂) p‖ = ‖p.eval a‖ := fun p => by
    rw [show (a : K̂) = algebraMap K K̂ a from rfl, aeval_algebraMap_apply,
      show algebraMap K K̂ (aeval a p) = ((aeval a p : K) : K̂) from rfl,
      UniformSpace.Completion.norm_coe, coe_aeval_eq_eval]
  obtain ⟨⟨h1, h2⟩, h3⟩ := haV
  change δ < ‖aeval (a : K̂) (derivative g)‖ at h1
  change ‖aeval (a : K̂) g‖ < δ * ‖s‖ at h2
  simp only [Set.mem_iInter] at h3
  rw [hcoe] at h1 h2
  have hD : ‖g.eval a‖ < ‖g.derivative.eval a * s‖ := by
    rw [norm_mul]
    calc ‖g.eval a‖ < δ * ‖s‖ := h2
      _ ≤ ‖g.derivative.eval a‖ * ‖s‖ := by gcongr
  have hk : ∀ k, 2 ≤ k → ‖(taylor a g).coeff k * s ^ k‖ ≤ ‖g.derivative.eval a * s‖ := by
    intro k hk2
    rw [taylor_coeff, norm_mul, norm_pow, norm_mul]
    by_cases hkn : k ≤ n
    · have hb : ‖(hasseDeriv k g).eval a‖ < ‖aeval x (hasseDeriv k g)‖ + 1 := by
        have := h3 k (mem_range.mpr (by omega))
        change ‖aeval (a : K̂) (hasseDeriv k g)‖ < _ at this
        rwa [hcoe] at this
      have hCk' := hCk k (mem_range.mpr (by omega))
      have hpow : ‖s‖ ^ k ≤ ‖s‖ * ‖s‖ := by
        rw [← sq]
        exact pow_le_pow_of_le_one (norm_nonneg _) hs1.le hk2
      calc ‖(hasseDeriv k g).eval a‖ * ‖s‖ ^ k ≤ C * (‖s‖ * ‖s‖) := by
            gcongr
            linarith
        _ ≤ C * ((δ / C) * ‖s‖) := by gcongr
        _ = δ * ‖s‖ := by field_simp
        _ ≤ ‖g.derivative.eval a‖ * ‖s‖ := by gcongr
    · rw [hasseDeriv_eq_zero_of_lt_natDegree g k (by omega), eval_zero, norm_zero, zero_mul]
      positivity
  obtain ⟨r, hr⟩ := exists_root_of_newton hH g a s hD hk
  have hdeg := degree_eq_one_of_irreducible_of_root (minpoly.irreducible hint) hr
  rw [IntermediateField.mem_bot]
  exact minpoly.natDegree_eq_one_iff.mp (natDegree_eq_of_degree_eq_some hdeg)

/-- **A henselian valued field satisfies simple-root Hensel lifting** for its norm valuation. -/
theorem valHensel_of_isHenselianValuedField (hK : IsHenselianValuedField K) : ValHensel ν := by
  let Ω := SeparableClosure K
  obtain ⟨w, hw, huniq⟩ := hK Ω
  have hinv : ∀ (σ : Ω ≃ₐ[K] Ω) (x : Ω), w (σ x) = w x := by
    intro σ x
    have h := huniq (HenselianIffSeparablyClosed.pullback w σ.toRingHom) (fun a => by
      change w (σ (algebraMap K Ω a)) = ‖a‖
      rw [AlgEquiv.commutes]
      exact hw a)
    exact congrArg (fun v : AbsoluteValue Ω ℝ => v x) h
  have hna : ∀ x y : Ω, w (x + y) ≤ max (w x) (w y) := by
    have : IsUltrametricDist (WithAbs w) :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n => by
        rw [WithAbs.norm_eq_apply_ofAbs]
        have hn : WithAbs.ofAbs (n : WithAbs w) = algebraMap K Ω n := by
          rw [map_natCast]
          exact map_natCast (WithAbs.equiv w) n
        rw [hn, hw]
        exact IsUltrametricDist.norm_natCast_le_one K n
    intro x y
    exact IsUltrametricDist.norm_add_le_max (WithAbs.toAbs w x) (WithAbs.toAbs w y)
  let ω : Valuation Ω ℝ≥0 :=
    { toFun := fun x => (⟨w x, w.nonneg x⟩ : ℝ≥0)
      map_zero' := by ext; exact map_zero w
      map_one' := by ext; exact map_one w
      map_mul' := fun x y => by ext; exact map_mul w x y
      map_add_le_max' := fun x y =>
        NNReal.coe_le_coe.mp ((hna x y).trans_eq
          (NNReal.coe_max (⟨w x, w.nonneg x⟩ : ℝ≥0) (⟨w y, w.nonneg y⟩ : ℝ≥0)).symm) }
  have hωw : ∀ x, (ω x : ℝ) = w x := fun _ => rfl
  have : HenselianLocalRing ω.valuationSubring :=
    Langlands.LocalGalois.Separable.sepClosed_henselian _
  have h := valHensel_comap (valHensel_of_henselian ω)
    (fun σ x => by
      apply NNReal.eq
      rw [hωw, hωw]
      exact hinv σ x)
    (fun x hx => by
      rw [← IntermediateField.mem_bot]
      exact (InfiniteGalois.mem_bot_iff_fixed x).2 hx)
  have hcomap : ω.comap (algebraMap K Ω) = ν := by
    ext x
    rw [Valuation.comap_apply, NormedField.valuation_apply, hωw, coe_nnnorm]
    exact hw x
  rwa [hcomap] at h

end HenselianValuationRing

/-- **A non-archimedean field is henselian exactly when its valuation ring is a henselian local
ring** (Conrad, printed p.14, citing [Ber, 2.4.3]). -/
theorem henselianIffValuationRingHenselian :
    HenselianIffValuationRingHenselianStatement.{u} := by
  intro K _ _ O hO
  constructor
  · intro hK
    exact HenselianValuationRing.henselianLocalRing_of_valHensel hO
      (HenselianValuationRing.valHensel_of_isHenselianValuedField hK)
  · intro hhen
    exact HenselianIffSeparablyClosed.isHenselianValuedField_of_separableClosure_eq_bot
      (HenselianValuationRing.separableClosure_eq_bot
        (HenselianValuationRing.valHensel_of_henselianLocalRing hO hhen))

end Langlands.AlgebraicGeometry.PointTopology
