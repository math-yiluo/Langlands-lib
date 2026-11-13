import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Langlands.LinearAlgebra.LocalQuadraticAnisotropicDimensionBoundStatement
import Langlands.LinearAlgebra.QuadraticFormCoordinatePolynomial

/-! # The anisotropic quadratic dimension bound over nonarchimedean local fields: proof -/

noncomputable section

universe u v w

namespace Langlands.LocalQuadraticAnisotropic

open ValuativeRel QuadraticMap

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local notation "val" => valuation K

/-- Hensel's lemma for `u ^ 2 + u + t` when `t` lies in the maximal ideal. -/
theorem exists_root_sq_add_self_add (t : K) (ht : val t < 1) :
    ∃ u : K, u ^ 2 + u + t = 0 := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  let t' : 𝒪[K] := ⟨t, ht.le⟩
  have ht' : t' ∈ 𝓂[K] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr ht
  let f : Polynomial 𝒪[K] := Polynomial.X ^ 2 + Polynomial.X + Polynomial.C t'
  have hf : f.Monic := by
    simp only [f]
    monicity!
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := 𝓂[K]) f hf 0
    (by simpa [f] using ht') (by simp [f])
  refine ⟨a, ?_⟩
  have := congrArg (fun z : 𝒪[K] => (z : K)) ha
  simpa [f, Polynomial.IsRoot, t'] using this

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem valuation_two_le_one : val (2 : K) ≤ 1 := by
  have := (val).map_add (1 : K) 1
  rw [one_add_one_eq_two] at this
  simpa using this

variable {V : Type v} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

/-- The polar bound `v(b)^2 ≤ v(a) v(c)` for an anisotropic form. -/
theorem polar_sq_le (hQ : Q.Anisotropic) (x y : V) :
    val (polar Q x y) ^ 2 ≤ val (Q x) * val (Q y) := by
  by_contra! h
  have hb : polar Q x y ≠ 0 := by
    intro hb
    rw [hb, map_zero] at h
    simp at h
  have ha : Q x ≠ 0 := by
    intro ha
    have hx := hQ x ha
    apply hb
    simp [hx]
  have hbv : (0 : ValueGroupWithZero K) < val (polar Q x y) ^ 2 := by
    simpa [zero_lt_iff] using hb
  have ht : val (Q x * Q y / polar Q x y ^ 2) < 1 := by
    rw [map_div₀, map_mul, map_pow, div_lt_one₀ hbv]
    exact h
  obtain ⟨u, hu⟩ := exists_root_sq_add_self_add _ ht
  set s := polar Q x y / Q x * u with hs
  have hzero : Q (s • x + y) = 0 := by
    rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, polar_smul_left, smul_eq_mul,
      smul_eq_mul]
    have : s * s * Q x + Q y + s * polar Q x y =
        polar Q x y ^ 2 / Q x * (u ^ 2 + u + Q x * Q y / polar Q x y ^ 2) := by
      rw [hs]
      field_simp
      ring
    rw [this, hu, mul_zero]
  have hy : y = -(s • x) := eq_neg_of_add_eq_zero_right (hQ _ hzero)
  have hc : Q y = s * s * Q x := by
    rw [hy, QuadraticMap.map_neg, QuadraticMap.map_smul, smul_eq_mul]
  have hb' : polar Q x y = -(s * (2 * Q x)) := by
    rw [hy, polar_neg_right, polar_smul_right, polar_self, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have h4 : polar Q x y ^ 2 = 4 * (Q x * Q y) := by
    rw [hc]
    nth_rewrite 1 [hb']
    ring
  have h4v : val (4 : K) ≤ 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, map_mul]
    exact mul_le_one' valuation_two_le_one valuation_two_le_one
  have : val (polar Q x y) ^ 2 ≤ val (Q x) * val (Q y) := by
    rw [← map_pow, h4, map_mul, map_mul]
    calc val 4 * (val (Q x) * val (Q y)) ≤ 1 * (val (Q x) * val (Q y)) := mul_le_mul_left h4v _
      _ = val (Q x) * val (Q y) := one_mul _
  exact absurd this (not_le.mpr h)

theorem val_polar_le_max (hQ : Q.Anisotropic) (x y : V) :
    val (polar Q x y) ≤ max (val (Q x)) (val (Q y)) := by
  by_contra! hlt
  have h := polar_sq_le Q hQ x y
  have h2 : val (Q x) * val (Q y) ≤ max (val (Q x)) (val (Q y)) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul' (le_max_left _ _) (le_max_right _ _)
  have h3 : max (val (Q x)) (val (Q y)) ^ 2 < val (polar Q x y) ^ 2 :=
    pow_lt_pow_left₀ hlt zero_le two_ne_zero
  exact absurd (h.trans h2) (not_le.mpr h3)

/-- The value of an anisotropic form is ultrametric. -/
theorem val_map_add_le (hQ : Q.Anisotropic) (x y : V) :
    val (Q (x + y)) ≤ max (val (Q x)) (val (Q y)) := by
  rw [QuadraticMap.map_add (⇑Q)]
  exact Valuation.map_add_le _ (Valuation.map_add_le _ (le_max_left _ _) (le_max_right _ _))
    (val_polar_le_max Q hQ x y)

theorem val_map_sub_le (hQ : Q.Anisotropic) (x y : V) :
    val (Q (x - y)) ≤ max (val (Q x)) (val (Q y)) := by
  simpa [sub_eq_add_neg, QuadraticMap.map_neg] using val_map_add_le Q hQ x (-y)

theorem val_map_sum_le (hQ : Q.Anisotropic) {ι : Type*} (s : Finset ι) (w : ι → V)
    (γ : ValueGroupWithZero K) (h : ∀ i ∈ s, val (Q (w i)) ≤ γ) :
    val (Q (∑ i ∈ s, w i)) ≤ γ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (val_map_add_le Q hQ _ _).trans
      (max_le (h i (by simp)) (ih fun j hj => h j (by simp [hj])))

/-- A family is dominant when each term of a linear combination has value at most the value of
the whole combination. -/
def Dominant {ι : Type*} [Fintype ι] (e : ι → V) : Prop :=
  ∀ (a : ι → K) (i : ι), val (Q (a i • e i)) ≤ val (Q (∑ j, a j • e j))

open WithZeroTopology in
/-- Best approximation from the span of a dominant family exists. -/
theorem exists_min (hQ : Q.Anisotropic) {k : ℕ} (e : Fin k → V) (he0 : ∀ j, e j ≠ 0)
    (he : Dominant Q e) (x : V) : ∃ a₀ : Fin k → K, ∀ a : Fin k → K,
      val (Q (x - ∑ j, a₀ j • e j)) ≤ val (Q (x - ∑ j, a j • e j)) := by
  set δ := val (Q x) with hδ
  let ρ : Fin k → ValueGroupWithZero K := fun j => max 1 (δ * (val (Q (e j)))⁻¹)
  let A : Set (Fin k → K) := Set.univ.pi fun j => {y : K | val y ≤ ρ j}
  have hA : IsCompact A :=
    isCompact_univ_pi fun j => IsNonarchimedeanLocalField.isCompact_closedBall K (ρ j)
  let F : (Fin k → K) → ValueGroupWithZero K := fun a => val (Q (x - ∑ j, a j • e j))
  have hpoly : F = fun a : Fin k → K => val (MvPolynomial.eval
      (Fin.cons 1 (-a) : Fin (k + 1) → K)
      (QuadraticPolynomial.coordinatePolynomial Q (Fin.cons x e : Fin (k + 1) → V))) := by
    funext a
    rw [QuadraticPolynomial.eval_coordinatePolynomial, Fin.sum_univ_succ]
    simp [F, sub_eq_add_neg, Finset.sum_neg_distrib, neg_smul]
  have hb : Continuous fun a : Fin k → K => (Fin.cons 1 (-a) : Fin (k + 1) → K) := by
    refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact continuous_const
    · simp only [Fin.cons_succ, Pi.neg_apply]
      exact (continuous_apply j).neg
  have hF : Continuous F := by
    rw [hpoly]
    exact IsValuativeTopology.continuous_valuation.comp ((MvPolynomial.continuous_eval _).comp hb)
  have h0A : (0 : Fin k → K) ∈ A := by
    simp only [A, Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, Pi.zero_apply, map_zero,
      true_implies]
    exact fun j => zero_le
  obtain ⟨a₀, -, hmin⟩ := hA.exists_isMinOn ⟨0, h0A⟩ hF.continuousOn
  refine ⟨a₀, fun a => ?_⟩
  by_cases ha : a ∈ A
  · exact hmin ha
  · simp only [A, Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, true_implies, not_forall,
      not_le] at ha
    obtain ⟨j, hj⟩ := ha
    have hej : val (Q (e j)) ≠ 0 := by
      intro h
      exact he0 j (hQ _ ((Valuation.zero_iff (valuation K)).mp h))
    have hlarge : δ < val (Q (∑ i, a i • e i)) := by
      refine lt_of_lt_of_le ?_ (he a j)
      rw [QuadraticMap.map_smul, smul_eq_mul, map_mul, map_mul]
      have h1 : 1 ≤ val (a j) := (le_max_left _ _).trans hj.le
      have h2 : δ * (val (Q (e j)))⁻¹ < val (a j) := (le_max_right _ _).trans_lt hj
      have hpos : (0 : ValueGroupWithZero K) < val (Q (e j)) := zero_lt_iff.mpr hej
      calc δ = δ * (val (Q (e j)))⁻¹ * val (Q (e j)) := by
            rw [inv_mul_cancel_right₀ hej]
        _ < val (a j) * val (Q (e j)) := mul_lt_mul_of_pos_right h2 hpos
        _ ≤ val (a j) * val (a j) * val (Q (e j)) := by
            refine mul_le_mul_left ?_ _
            calc val (a j) = val (a j) * 1 := (mul_one _).symm
              _ ≤ val (a j) * val (a j) := mul_le_mul_right h1 _
    have hw : val (Q (∑ i, a i • e i)) ≤ max δ (F a) := by
      have := val_map_sub_le Q hQ x (x - ∑ i, a i • e i)
      simpa [sub_sub_cancel] using this
    have hFa : val (Q (∑ i, a i • e i)) ≤ F a := by
      rcases le_max_iff.mp hw with h | h
      · exact absurd h (not_le.mpr hlarge)
      · exact h
    have h0 : F a₀ ≤ F 0 := hmin h0A
    have hF0 : F 0 = δ := by simp [F, hδ]
    exact h0.trans (hF0.le.trans (hlarge.le.trans hFa))

/-- Appending the best-approximation error keeps a family dominant. -/
theorem dominant_snoc (hQ : Q.Anisotropic) {k : ℕ} (e : Fin k → V) (he : Dominant Q e) (x : V)
    (a₀ : Fin k → K)
    (hmin : ∀ a : Fin k → K, val (Q (x - ∑ j, a₀ j • e j)) ≤ val (Q (x - ∑ j, a j • e j))) :
    Dominant Q (Fin.snoc e (x - ∑ j, a₀ j • e j) : Fin (k + 1) → V) := by
  set y := x - ∑ j, a₀ j • e j with hy
  intro b i
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  set w := ∑ j : Fin k, b j.castSucc • e j with hw
  set t := b (Fin.last k) with ht
  have key : val (Q (t • y)) ≤ val (Q (w + t • y)) := by
    by_cases ht0 : t = 0
    · simp [ht0]
    · have hrw : w + t • y = t • (x - ∑ j, (a₀ j - t⁻¹ * b j.castSucc) • e j) := by
        simp only [hy, hw, smul_sub, Finset.smul_sum, smul_smul, sub_smul,
          Finset.sum_sub_distrib, mul_inv_cancel_left₀ ht0]
        abel
      rw [hrw, QuadraticMap.map_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul]
      simp only [map_mul]
      exact mul_le_mul_right (hmin fun j => a₀ j - t⁻¹ * b j.castSucc) _
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using key
  · simp only [Fin.snoc_castSucc]
    calc val (Q (b j.castSucc • e j)) ≤ val (Q w) := he (fun j => b j.castSucc) j
      _ ≤ max (val (Q (w + t • y))) (val (Q (t • y))) := by
          have := val_map_sub_le Q hQ (w + t • y) (t • y)
          simpa using this
      _ = val (Q (w + t • y)) := max_eq_left key

/-- An anisotropic form has a dominant family of nonzero vectors of every length up to the
dimension. -/
theorem exists_dominant [FiniteDimensional K V] (hQ : Q.Anisotropic) :
    ∀ k ≤ Module.finrank K V, ∃ e : Fin k → V, (∀ j, e j ≠ 0) ∧ Dominant Q e := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨Fin.elim0, fun j => j.elim0, fun _ i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨e, he0, he⟩ := ih (Nat.le_of_succ_le hk)
    have hspan : Submodule.span K (Set.range e) ≠ ⊤ := by
      intro htop
      have h1 := finrank_range_le_card (R := K) e
      rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at h1
      omega
    obtain ⟨x, hx⟩ : ∃ x, x ∉ Submodule.span K (Set.range e) := by
      by_contra! h
      exact hspan (Submodule.eq_top_iff'.mpr h)
    obtain ⟨a₀, hmin⟩ := exists_min Q hQ e he0 he x
    refine ⟨Fin.snoc e (x - ∑ j, a₀ j • e j), fun j => ?_, dominant_snoc Q hQ e he x a₀ hmin⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last]
      intro h
      apply hx
      rw [sub_eq_zero] at h
      rw [h]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simpa only [Fin.snoc_castSucc] using he0 j

omit [Module K V] in
/-- Every nonzero value is a square class of `1` or of a fixed element. -/
theorem exists_normalizer : ∃ ϖ : K, ϖ ≠ 0 ∧ ∀ γ : ValueGroupWithZero K, γ ≠ 0 →
    ∃ c : K, c ≠ 0 ∧ (val c * val c * γ = 1 ∨ val c * val c * γ = val ϖ) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_zpow_surjective (G := (ValueGroupWithZero K)ˣ)
  obtain ⟨ϖ, hϖ⟩ := valuation_surjective (K := K) (g : ValueGroupWithZero K)
  refine ⟨ϖ, ?_, fun γ hγ => ?_⟩
  · intro h
    rw [h, map_zero] at hϖ
    exact g.ne_zero hϖ.symm
  · obtain ⟨k, hk⟩ := hg (Units.mk0 γ hγ)
    obtain ⟨c, hc⟩ := valuation_surjective (K := K)
      ((g ^ (-(k / 2)) : (ValueGroupWithZero K)ˣ) : ValueGroupWithZero K)
    refine ⟨c, ?_, ?_⟩
    · intro h
      rw [h, map_zero] at hc
      exact Units.ne_zero _ hc.symm
    · have hγ' : γ = ((g ^ k : (ValueGroupWithZero K)ˣ) : ValueGroupWithZero K) := by
        simp only at hk
        rw [hk, Units.val_mk0]
      have hval : val c * val c * γ =
          ((g ^ (-(k / 2) + -(k / 2) + k) : (ValueGroupWithZero K)ˣ) : ValueGroupWithZero K) := by
        rw [hc, hγ', zpow_add, zpow_add, Units.val_mul, Units.val_mul]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        have : -(k / 2) + -(k / 2) + k = 0 := by omega
        rw [hval, this, zpow_zero, Units.val_one]
      · right
        have : -(k / 2) + -(k / 2) + k = 1 := by omega
        rw [hval, this, zpow_one, hϖ]

omit [Module K V] in
/-- Residue lemma: a quadratic form whose values on integral vectors have value at most
`v c`, with equality on primitive vectors, lives in at most two variables. -/
theorem card_le_two_of_residue {ι : Type w} [Fintype ι] (q : QuadraticForm K (ι → K)) (c : K)
    (hc : c ≠ 0) (h1 : ∀ a : ι → K, (∀ i, val (a i) ≤ 1) → val (q a) ≤ val c)
    (h2 : ∀ a : ι → K, (∀ i, val (a i) ≤ 1) → (∃ i, val (a i) = 1) → val (q a) = val c) :
    Fintype.card ι ≤ 2 := by
  classical
  let : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  have hcpos : (0 : ValueGroupWithZero K) < val c := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc)
  let T : ι → ι → K := fun i j =>
    q.toBilin (Pi.basisFun K ι) (Pi.single i 1) (Pi.single j 1)
  have hq : ∀ a, q a = ∑ i, ∑ j, a i * (a j * T i j) := by
    intro a
    have h := LinearMap.BilinMap.toQuadraticMap_apply (q.toBilin (Pi.basisFun K ι)) a
    rw [q.toQuadraticMap_toBilin] at h
    rw [h]
    conv_lhs => rw [← Matrix.toLinearMap₂'_toMatrix' (R := K) (q.toBilin (Pi.basisFun K ι))]
    rw [Matrix.toLinearMap₂'_apply]
    simp only [smul_eq_mul]
    rfl
  have hint : ∀ a : ι → K, (∀ i, val (a i) ≤ 1) → val (c⁻¹ * q a) ≤ 1 := by
    intro a ha
    rw [map_mul, map_inv₀, inv_mul_le_one₀ hcpos]
    exact h1 a ha
  have hsingle : ∀ (i : ι) (l : ι), val ((Pi.single i 1 : ι → K) l) ≤ 1 := by
    intro i l
    by_cases hl : l = i
    · subst hl; simp
    · simp [hl]
  have hpair : ∀ (i j : ι) (l : ι), val ((Pi.single i 1 + Pi.single j 1 : ι → K) l) ≤ 1 := by
    intro i j l
    simp only [Pi.add_apply]
    exact Valuation.map_add_le _ (hsingle i l) (hsingle j l)
  have hT : ∀ i j, val (c⁻¹ * T i j) ≤ 1 := by
    intro i j
    have hb := q.toBilin_apply (Pi.basisFun K ι) i j
    simp only [Pi.basisFun_apply] at hb
    simp only [T]
    rw [hb]
    split_ifs
    · exact hint _ (hsingle i)
    · rw [polar, mul_sub, mul_sub]
      exact Valuation.map_sub_le _ (Valuation.map_sub_le _ (hint _ (hpair i j))
        (hint _ (hsingle i))) (hint _ (hsingle j))
    · simp
  let M : Matrix ι ι 𝒪[K] := fun i j => ⟨c⁻¹ * T i j, hT i j⟩
  let Qbar : QuadraticForm 𝓀[K] (ι → 𝓀[K]) :=
    LinearMap.BilinMap.toQuadraticMap
      (Matrix.toLinearMap₂' 𝓀[K] (S₁ := 𝓀[K]) (S₂ := 𝓀[K]) (M.map (IsLocalRing.residue 𝒪[K])))
  have hQbar : Qbar.Anisotropic := by
    intro abar habar
    by_contra hne
    obtain ⟨i₀, hi₀⟩ : ∃ i, abar i ≠ 0 := by
      by_contra! h
      exact hne (funext h)
    choose a ha using fun i => IsLocalRing.residue_surjective (R := 𝒪[K]) (abar i)
    have hunit : IsUnit (a i₀) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ha]
      exact hi₀
    have hv1 : val ((a i₀ : 𝒪[K]) : K) = 1 := by
      have h := Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := a i₀)
      have hle : val ((a i₀ : 𝒪[K]) : K) ≤ 1 := (a i₀).2
      exact le_antisymm hle (not_lt.mp fun hlt => h.mpr hlt hunit)
    have hval : val (c⁻¹ * q (fun i => (a i : K))) = 1 := by
      rw [map_mul, map_inv₀, h2 _ (fun i => (a i).2) ⟨i₀, hv1⟩, inv_mul_cancel₀ hcpos.ne']
    let S : 𝒪[K] := ∑ i, ∑ j, a i * (a j * M i j)
    have hS : (S : K) = c⁻¹ * q (fun i => (a i : K)) := by
      rw [hq]
      simp only [S, M, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have hres : IsLocalRing.residue 𝒪[K] S = 0 := by
      rw [← habar]
      simp only [S, Qbar, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply,
        map_sum, map_mul, Matrix.map_apply, ha, smul_eq_mul]
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one, hS, hval] at hres
    exact lt_irrefl _ hres
  have := Fintype.ofFinite 𝓀[K]
  have := QuadraticPolynomial.finiteField_finrank_le_two Qbar hQbar
  simpa using this

end Langlands.LocalQuadraticAnisotropic

namespace Langlands

open ValuativeRel Langlands.LocalQuadraticAnisotropic

/-- Every anisotropic quadratic form over a nonarchimedean local field has dimension at most
four, in every characteristic. -/
theorem localQuadraticAnisotropicDimensionBound :
    LocalQuadraticAnisotropicDimensionBoundStatement.{u, v} := by
  intro K _ _ _ _ V _ _ _ Q hQ
  classical
  set n := Module.finrank K V with hn
  obtain ⟨e, he0, he⟩ := exists_dominant Q hQ n le_rfl
  obtain ⟨ϖ, hϖ, hnorm⟩ := exists_normalizer (K := K)
  have hval : ∀ i, valuation K (Q (e i)) ≠ 0 := fun i h =>
    he0 i (hQ _ ((Valuation.zero_iff (valuation K)).mp h))
  choose c hc0 hc using fun i => hnorm _ (hval i)
  let f : Fin n → V := fun i => c i • e i
  have hf : Dominant Q f := by
    intro a i
    have := he (fun j => a j * c j) i
    simpa [f, smul_smul] using this
  have hfval : ∀ i, valuation K (Q (f i)) = 1 ∨ valuation K (Q (f i)) = valuation K ϖ := by
    intro i
    simp only [f, QuadraticMap.map_smul, smul_eq_mul, map_mul]
    exact hc i
  have hclass : ∀ (s : Finset (Fin n)) (d : K), d ≠ 0 →
      (∀ i ∈ s, valuation K (Q (f i)) = valuation K d) → s.card ≤ 2 := by
    intro s d hd hs
    have hext : ∀ a : s → K,
        ∑ j, (if h : j ∈ s then a ⟨j, h⟩ else 0) • f j = ∑ i : s, a i • f i := by
      intro a
      rw [← Finset.sum_subset (Finset.subset_univ s) (by intro j _ hj; simp [hj]),
        Finset.sum_subtype s (p := fun j => j ∈ s) (fun _ => Iff.rfl)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [i.2]
    have := card_le_two_of_residue (ι := s)
      (Q.comp (Fintype.linearCombination K (fun i : s => f i))) d hd ?_ ?_
    · simpa using this
    · intro a ha
      simp only [QuadraticMap.comp_apply, Fintype.linearCombination_apply]
      apply val_map_sum_le Q hQ
      intro i _
      rw [QuadraticMap.map_smul, smul_eq_mul, map_mul, map_mul, hs i i.2]
      calc valuation K (a i) * valuation K (a i) * valuation K d
          ≤ 1 * 1 * valuation K d := by gcongr <;> exact ha i
        _ = valuation K d := by simp
    · intro a ha ⟨i₀, hi₀⟩
      simp only [QuadraticMap.comp_apply, Fintype.linearCombination_apply]
      refine le_antisymm ?_ ?_
      · apply val_map_sum_le Q hQ
        intro i _
        rw [QuadraticMap.map_smul, smul_eq_mul, map_mul, map_mul, hs i i.2]
        calc valuation K (a i) * valuation K (a i) * valuation K d
            ≤ 1 * 1 * valuation K d := by gcongr <;> exact ha i
          _ = valuation K d := by simp
      · have hdom := hf (fun j => if h : j ∈ s then a ⟨j, h⟩ else 0) i₀
        rw [hext] at hdom
        simp only [i₀.2, dite_true] at hdom
        refine le_trans ?_ hdom
        rw [QuadraticMap.map_smul, smul_eq_mul, map_mul, map_mul, hi₀, hs i₀ i₀.2]
        simp
  let s0 := Finset.univ.filter fun i => valuation K (Q (f i)) = 1
  let s1 := Finset.univ.filter fun i => valuation K (Q (f i)) = valuation K ϖ
  have hcover : n ≤ s0.card + s1.card := by
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (s0 ∪ s1).card := Finset.card_le_card fun i _ => by
          rcases hfval i with h | h <;> simp [s0, s1, h]
      _ ≤ _ := Finset.card_union_le _ _
  have h0 := hclass s0 1 one_ne_zero (by simp [s0])
  have h1 := hclass s1 ϖ hϖ (by simp [s1])
  omega

end Langlands
