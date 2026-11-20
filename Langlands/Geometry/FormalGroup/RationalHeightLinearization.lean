import Langlands.Geometry.FormalGroup.RationalHeightJets
import Langlands.Geometry.FormalGroup.TruncatedPoints

/-! # Scalar linearization in rectangular field jets -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.RationalHeightLinearization

open CategoryTheory FiniteKernelComposition MvPolynomial RationalHeightJets

variable {k : Type v} [Field k] {σ τ : Type}

section Average

variable {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The average that extracts the eigenvalue `c` from a cyclic action. -/
private def weightedAverage (m : ℕ) (c : k) (x : ℕ → V) : V :=
  (m : k)⁻¹ • ∑ j ∈ Finset.range m, c⁻¹ ^ j • x j

private theorem map_weightedAverage (L : V →ₗ[k] W) (m : ℕ) (c : k) (x : ℕ → V) :
    L (weightedAverage m c x) = weightedAverage m c (L ∘ x) := by
  simp [weightedAverage]

private theorem weightedAverage_shift {m : ℕ} {c : k} (hm : m ≠ 0) (hc : c ^ m = 1)
    (x : ℕ → V) (hx : x m = x 0) :
    weightedAverage m c (fun j => x (j + 1)) = c • weightedAverage m c x := by
  have hc₀ : c ≠ 0 := fun h => by simp [h, hm] at hc
  let y := fun j => c⁻¹ ^ j • x j
  have hy : y m = y 0 := by simp [y, inv_pow, hc, hx]
  have hs : ∑ j ∈ Finset.range m, y (j + 1) = ∑ j ∈ Finset.range m, y j := by
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [Finset.sum_range_succ (fun j => y (j + 1)), Finset.sum_range_succ', hy, add_comm]
  have hsum : ∑ j ∈ Finset.range m, c⁻¹ ^ j • x (j + 1) =
      c • ∑ j ∈ Finset.range m, y j := by
    rw [← hs, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show y (j + 1) = c⁻¹ ^ (j + 1) • x (j + 1) from rfl, smul_smul, pow_succ',
      ← mul_assoc, mul_inv_cancel₀ hc₀, one_mul]
  unfold weightedAverage
  rw [hsum]
  exact smul_comm (m : k)⁻¹ c _

private theorem weightedAverage_smul_pows {m : ℕ} {c : k} (hm : (m : k) ≠ 0)
    (hc : c ≠ 0) (x : V) :
    weightedAverage m c (fun j => c ^ j • x) = x := by
  simp only [weightedAverage, smul_smul, ← mul_pow, inv_mul_cancel₀ hc, one_pow, one_smul,
    Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul k, inv_smul_smul₀ hm]

end Average

section Scaling

/-- The simultaneous scaling of the polynomial variables by `c`. -/
def scale (c : k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => c • X i

@[simp]
theorem scale_X (c : k) (i : σ) : scale c (X i) = c • X i :=
  aeval_X _ _

theorem scale_one : scale (1 : k) = AlgHom.id k (MvPolynomial σ k) :=
  MvPolynomial.algHom_ext fun i => by simp

theorem scale_comp (c d : k) :
    (scale (σ := σ) c).comp (scale d) = scale (d * c) :=
  MvPolynomial.algHom_ext fun i => by simp [smul_smul]

end Scaling

section Substitution

variable [Finite σ] {p : ℕ} [ExpChar k p]

/-- Substitute augmentation elements for the variables of a characteristic-power jet. -/
def substitute (e : ℕ) (y : σ → truncAlg k σ (p ^ e))
    (hy : ∀ i, y i ∈ augmentation k σ (p ^ e)) :
    truncAlg k σ (p ^ e) →ₐ[k] truncAlg k σ (p ^ e) :=
  Ideal.Quotient.liftₐ _ (aeval y) (by
    have h : truncIdeal k σ (p ^ e) ≤ RingHom.ker (aeval y).toRingHom := by
      rw [truncIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change aeval y (X i ^ (p ^ e)) = 0
      rw [map_pow, aeval_X]
      exact nilpotent_pow_eq_zero e (augmentation_le_nilradical _ (hy i))
    exact fun _ hx => h hx)

@[simp]
theorem substitute_X (e : ℕ) (y : σ → truncAlg k σ (p ^ e))
    (hy : ∀ i, y i ∈ augmentation k σ (p ^ e)) (i : σ) :
    substitute e y hy (truncProj k σ (p ^ e) (X i)) = y i :=
  aeval_X y i

private def scaleJet (e : ℕ) (c : k) : truncAlg k σ (p ^ e) →ₐ[k] truncAlg k σ (p ^ e) :=
  substitute e (fun i => c • truncProj k σ (p ^ e) (X i)) fun i =>
    Submodule.smul_of_tower_mem _ _ (truncProj_X_mem_augmentation _ i)

@[simp]
private theorem scaleJet_X (e : ℕ) (c : k) (i : σ) :
    scaleJet (p := p) e c (truncProj k σ (p ^ e) (X i)) =
      c • truncProj k σ (p ^ e) (X i) :=
  substitute_X _ _ _ _

private theorem scaleJet_truncProj (e : ℕ) (c : k) (Q : MvPolynomial σ k) :
    scaleJet (p := p) e c (truncProj k σ (p ^ e) Q) =
      truncProj k σ (p ^ e) (scale c Q) :=
  DFunLike.congr_fun (show (scaleJet (p := p) e c).comp (truncProj k σ (p ^ e)) =
    (truncProj k σ (p ^ e)).comp (scale c) from
      MvPolynomial.algHom_ext fun _ => by simp) Q

end Substitution

private theorem scale_weightedAverage {m : ℕ} {c : k} (hm : m ≠ 0) (hc : c ^ m = 1)
    (Q : MvPolynomial σ k) :
    scale c (weightedAverage m c (fun j => scale (c ^ j) Q)) =
      c • weightedAverage m c (fun j => scale (c ^ j) Q) := by
  change (scale c).toLinearMap (weightedAverage m c (fun j => scale (c ^ j) Q)) = _
  rw [map_weightedAverage]
  have h : (scale c).toLinearMap ∘ (fun j => scale (c ^ j) Q) =
      (fun j => scale (c ^ (j + 1)) Q) := by
    funext j
    rw [Function.comp_apply, AlgHom.toLinearMap_apply, ← AlgHom.comp_apply, scale_comp, pow_succ]
  rw [h]
  apply weightedAverage_shift hm hc (fun j => scale (c ^ j) Q)
  rw [hc, pow_zero]

section Invertibility

variable [Finite σ] {n : ℕ}

omit [Finite σ] in
/-- Substitutions tangent to the identity are the identity on the associated graded. -/
private theorem sub_mem_augmentation_pow
    (T : truncAlg k σ n →ₐ[k] truncAlg k σ n)
    (hT : ∀ i, T (truncProj k σ n (X i)) - truncProj k σ n (X i) ∈ augmentation k σ n ^ 2)
    (j : ℕ) {x : truncAlg k σ n} (hx : x ∈ augmentation k σ n ^ j) :
    T x - x ∈ augmentation k σ n ^ (j + 1) := by
  let I := augmentation k σ n
  let ρ := Ideal.Quotient.mkₐ k (I ^ 2)
  have hr : ρ.comp T = ρ := truncAlg_hom_ext fun i => by
    apply sub_eq_zero.mp
    rw [AlgHom.comp_apply, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hT i)
  have hd (y : truncAlg k σ n) : T y - y ∈ I ^ 2 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change ρ (T y - y) = 0
    rw [map_sub, ← AlgHom.comp_apply, hr, sub_self]
  change T x - x ∈ I ^ (j + 1)
  change x ∈ I ^ j at hx
  induction j generalizing x with
  | zero =>
    exact Ideal.pow_le_pow_right (by decide : 0 + 1 ≤ 2) (hd x)
  | succ j ih =>
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z hy hz => ?_)
    · have hyT : T y ∈ I := by
        rw [← sub_add_cancel (T y) y]
        exact I.add_mem (Ideal.pow_le_self (by decide) (hd y)) hy
      rw [map_mul, show T y * T z - y * z = T y * (T z - z) + (T y - y) * z by ring]
      apply Ideal.add_mem
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hyT (ih hz)
      · rw [show j + 1 + 1 = 2 + j by omega, pow_add]
        exact Ideal.mul_mem_mul (hd y) hz
    · rw [map_add, add_sub_add_comm]
      exact Ideal.add_mem _ hy hz

theorem bijective_of_tangent_id (hn : 0 < n)
    (T : truncAlg k σ n →ₐ[k] truncAlg k σ n)
    (hT : ∀ i, T (truncProj k σ n (X i)) - truncProj k σ n (X i) ∈ augmentation k σ n ^ 2) :
    Function.Bijective T := by
  let : NeZero n := ⟨hn.ne'⟩
  let : Module.Finite k (truncAlg k σ n) := truncAlg_finite n
  have hinj : Function.Injective T.toLinearMap := by
    -- Test a kernel element in every power of the nilpotent augmentation ideal.
    intro x y he
    have hz : T (x - y) = 0 := by rw [map_sub, show T x = T y from he, sub_self]
    obtain ⟨N, hN⟩ := augmentation_isNilpotent (k := k) (σ := σ) n
    have hm (j : ℕ) : x - y ∈ augmentation k σ n ^ j := by
      induction j with
      | zero => simp
      | succ j ih =>
        have h := sub_mem_augmentation_pow T hT j ih
        rwa [hz, zero_sub, Ideal.neg_mem_iff] at h
    exact sub_eq_zero.mp (show x - y = 0 by simpa [hN] using hm N)
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

end Invertibility

section Scalar

variable {O : Type u} [CommRing O] [Algebra O k] [Finite σ]
variable {p : ℕ} [ExpChar k p] (M : ModuleLaw O k σ)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Pullback along a formal scalar action in the rectangular jet. -/
def scalarJet (e : ℕ) (a : O) :
    truncAlg k σ (p ^ e) →ₐ[k] truncAlg k σ (p ^ e) :=
  mapJet (p := p) e (M.scalarHom a)

@[simp]
theorem scalarJet_X (e : ℕ) (a : O) (i : σ) :
    scalarJet M e a (truncProj k σ (p ^ e) (X i)) =
      coord M (a • truncPoint M (p ^ e)) i := by
  rw [scalarJet, mapJet_X, scalarHom_onAlgebraPoints]

omit [ExpChar k p] in
private theorem coord_scalar_sub_mem (e : ℕ) (he : 1 < p ^ e) (a : O) (i : σ) :
    coord M (a • truncPoint M (p ^ e)) i -
      algebraMap O k a • truncProj k σ (p ^ e) (X i) ∈ augmentation k σ (p ^ e) ^ 2 := by
  classical
  let n := p ^ e
  let F := (M.action a).toCoordinateMap
  let x := truncPoint M n
  let P := truncBox n (F.series i)
  have hx (j : σ) : coord M x j ^ n = 0 := by
    rw [show x = truncPoint M n from rfl, coord_truncPoint, truncProj_X_pow]
  have hP : coord M (a • x) i = truncProj k σ n P := by
    change MvPowerSeries.constantCoeff
      ((SeriesPoint.eval (F.map (algebraMap k (truncAlg k σ n))) x).val i) = _
    rw [constantCoeff_eval_map F x hx]
    have ha : aeval (coord M x) = truncProj k σ n :=
      MvPolynomial.algHom_ext fun j => by rw [aeval_X, show x = truncPoint M n from rfl,
        coord_truncPoint]
    exact DFunLike.congr_fun ha P
  change coord M (a • x) i - algebraMap O k a • truncProj k σ n (X i) ∈
    augmentation k σ n ^ 2
  rw [hP, ← map_smul, ← map_sub, augmentation, ← Ideal.map_pow]
  apply Ideal.mem_map_of_mem
  rw [mem_pow_idealOfVars_iff']
  intro μ hμ
  have hbox (j : σ) : μ j < n := by
    have hj : Finsupp.single j (μ j) ≤ μ := Finsupp.single_le_iff.mpr le_rfl
    have h := Finsupp.degree_mono hj
    rw [Finsupp.degree_single] at h
    exact h.trans_lt (show μ.degree < n by omega)
  rw [coeff_sub, coeff_smul, coeff_X, coeff_truncBox_of_mem _ hbox]
  rcases Nat.eq_zero_or_pos μ.degree with h0 | hpos
  · have hzero : μ = 0 := (Finsupp.degree_eq_zero_iff μ).mp h0
    subst μ
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, F.constantCoeff_eq_zero]
  · have h1 : μ.degree = 1 := by omega
    obtain ⟨j, hj⟩ : μ.support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      contrapose! hpos
      simp [hpos]
    have hle : Finsupp.single j 1 ≤ μ := Finsupp.single_le_iff.mpr
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj))
    obtain ⟨d, hd⟩ := le_iff_exists_add.mp hle
    have h0 : d.degree = 0 := by simpa [hd] using h1
    have heq : μ = Finsupp.single j 1 := by
      simpa [(Finsupp.degree_eq_zero_iff d).mp h0] using hd
    rw [heq]
    change F.linearCoeff i j - algebraMap O k a • (if Finsupp.single i 1 =
      Finsupp.single j 1 then 1 else 0) = 0
    rw [show F.linearCoeff i j = _ from M.linear_natural a i j]
    by_cases hij : j = i
    · subst j
      simp [CoordinateMap.scalarLinearCoeff]
    · simp [CoordinateMap.scalarLinearCoeff, hij, Ne.symm hij,
        Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]

private theorem scalarJet_coord (e : ℕ) (a b : O) (i : σ) :
    scalarJet M e a (coord M (b • truncPoint M (p ^ e)) i) =
      coord M ((b * a) • truncPoint M (p ^ e)) i := by
  rw [← coord_algebraMapPoints, map_smul, scalarJet, mapJet_point,
    scalarHom_onAlgebraPoints, mul_smul]

private def averageCoord (e : ℕ) (a : O) (m : ℕ) (c : k) (i : σ) :
    truncAlg k σ (p ^ e) :=
  weightedAverage m c fun j => coord M (a ^ j • truncPoint M (p ^ e)) i

omit [ExpChar k p] in
private theorem averageCoord_sub_mem (e : ℕ) (he : 1 < p ^ e) (a : O) {m : ℕ} {c : k}
    (ha : algebraMap O k a = c) (hm : (m : k) ≠ 0) (hc : c ≠ 0) (i : σ) :
    averageCoord M e a m c i - truncProj k σ (p ^ e) (X i) ∈
      augmentation k σ (p ^ e) ^ 2 := by
  let q := Ideal.Quotient.mkₐ k (augmentation k σ (p ^ e) ^ 2)
  have h j :
      q (coord M (a ^ j • truncPoint M (p ^ e)) i) =
        c ^ j • q (truncProj k σ (p ^ e) (X i)) := by
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← ha, ← map_pow]
    exact coord_scalar_sub_mem M e he (a ^ j) i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (_ - _) = 0
  rw [map_sub, sub_eq_zero]
  change q.toLinearMap (weightedAverage m c (fun j =>
    coord M (a ^ j • truncPoint M (p ^ e)) i)) = _
  rw [map_weightedAverage]
  rw [show q.toLinearMap ∘ (fun j => coord M (a ^ j • truncPoint M (p ^ e)) i) =
    (fun j => c ^ j • q (truncProj k σ (p ^ e) (X i))) from funext h]
  exact weightedAverage_smul_pows hm hc _

omit [ExpChar k p] in
private theorem averageCoord_mem (e : ℕ) (he : 1 < p ^ e) (a : O) {m : ℕ} {c : k}
    (ha : algebraMap O k a = c) (hm : (m : k) ≠ 0) (hc : c ≠ 0) (i : σ) :
    averageCoord M e a m c i ∈ augmentation k σ (p ^ e) := by
  rw [← sub_add_cancel (averageCoord M e a m c i) (truncProj k σ (p ^ e) (X i))]
  exact Ideal.add_mem _ (Ideal.pow_le_self (by decide) (averageCoord_sub_mem M e he a ha hm hc i))
    (truncProj_X_mem_augmentation _ _)

/-- Averaging the coordinate functions gives an invertible change of variables. -/
private def linearize (e : ℕ) (he : 1 < p ^ e) (a : O) {m : ℕ} {c : k}
    (ha : algebraMap O k a = c) (hm : (m : k) ≠ 0) (hc : c ≠ 0) :
    truncAlg k σ (p ^ e) ≃ₐ[k] truncAlg k σ (p ^ e) :=
  AlgEquiv.ofBijective (substitute e (averageCoord M e a m c)
    (averageCoord_mem M e he a ha hm hc)) <|
      bijective_of_tangent_id (zero_lt_one.trans he) _ fun i => by
        rw [substitute_X]
        exact averageCoord_sub_mem M e he a ha hm hc i

@[simp]
private theorem linearize_X (e : ℕ) (he : 1 < p ^ e) (a : O) {m : ℕ} {c : k}
    (ha : algebraMap O k a = c) (hm : (m : k) ≠ 0) (hc : c ≠ 0) (i : σ) :
    linearize M e he a ha hm hc (truncProj k σ (p ^ e) (X i)) =
      averageCoord M e a m c i :=
  substitute_X _ _ (averageCoord_mem M e he a ha hm hc) _

private theorem scalarJet_averageCoord (e : ℕ) (a : O) {m : ℕ} {c : k}
    (hm : m ≠ 0) (hc : c ^ m = 1)
    (hfix : a ^ m • truncPoint M (p ^ e) = truncPoint M (p ^ e)) (i : σ) :
    scalarJet (p := p) M e a (averageCoord (p := p) M e a m c i) =
      c • averageCoord (p := p) M e a m c i := by
  change (scalarJet (p := p) M e a).toLinearMap (weightedAverage m c (fun j =>
    coord M (a ^ j • truncPoint M (p ^ e)) i)) = _
  rw [map_weightedAverage]
  have h j : scalarJet (p := p) M e a (coord M (a ^ j • truncPoint M (p ^ e)) i) =
      coord M (a ^ (j + 1) • truncPoint M (p ^ e)) i := by
    rw [scalarJet_coord, pow_succ]
  rw [show (scalarJet (p := p) M e a).toLinearMap ∘
    (fun j => coord M (a ^ j • truncPoint M (p ^ e)) i) =
      (fun j => coord M (a ^ (j + 1) • truncPoint M (p ^ e)) i) from funext h]
  exact weightedAverage_shift hm hc (fun j => coord M (a ^ j • truncPoint M (p ^ e)) i)
    (by rw [hfix, pow_zero, one_smul])

omit [ExpChar k p] in
private theorem restrictJet_averageCoord {e e' : ℕ} (hle : p ^ e ≤ p ^ e') (a : O)
    (m : ℕ) (c : k) (i : σ) :
    restrictJet hle (averageCoord M e' a m c i) = averageCoord M e a m c i := by
  change (restrictJet hle).toLinearMap (weightedAverage m c (fun j =>
    coord M (a ^ j • truncPoint M (p ^ e')) i)) = _
  rw [map_weightedAverage]
  congr 1
  funext j
  change restrictJet hle (coord M (a ^ j • truncPoint M (p ^ e')) i) =
    coord M (a ^ j • truncPoint M (p ^ e)) i
  rw [← coord_algebraMapPoints, map_smul, restrictJet_point]

private theorem scalarJet_linearize (e : ℕ) (he : 1 < p ^ e) (a : O) {m : ℕ} {c : k}
    (ha : algebraMap O k a = c) (hm : (m : k) ≠ 0) (hc : c ^ m = 1)
    (hc₀ : c ≠ 0) (hfix : a ^ m • truncPoint M (p ^ e) = truncPoint M (p ^ e)) :
    (scalarJet M e a).comp (linearize M e he a ha hm hc₀).toAlgHom =
      (linearize M e he a ha hm hc₀).toAlgHom.comp (scaleJet (p := p) e c) := by
  apply truncAlg_hom_ext
  intro i
  simp only [AlgHom.comp_apply, scaleJet_X, map_smul, AlgEquiv.toAlgHom_apply, linearize_X]
  have hm' : m ≠ 0 := fun h => hm (by simp [h])
  exact scalarJet_averageCoord M e a hm' hc hfix i

private theorem restrictJet_linearize {e e' : ℕ} (hle : p ^ e ≤ p ^ e')
    (he : 1 < p ^ e) (he' : 1 < p ^ e') (a : O) {m : ℕ} {c : k}
    (ha : algebraMap O k a = c) (hm : (m : k) ≠ 0) (hc₀ : c ≠ 0)
    (x : truncAlg k σ (p ^ e')) :
    restrictJet hle (linearize M e' he' a ha hm hc₀ x) =
      linearize M e he a ha hm hc₀ (restrictJet hle x) := by
  have h : (restrictJet hle).comp (linearize M e' he' a ha hm hc₀).toAlgHom =
      (linearize M e he a ha hm hc₀).toAlgHom.comp (restrictJet hle) := by
    apply truncAlg_hom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, restrictJet_truncProj, linearize_X]
    exact restrictJet_averageCoord M hle a m c i
  exact DFunLike.congr_fun h x

end Scalar

section Equations

variable {O : Type u} [CommRing O] [Algebra O k] [Finite σ] [Finite τ]
variable {p : ℕ} [ExpChar k p] {M : ModuleLaw O k σ} {N : ModuleLaw O k τ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

omit [Finite σ] in
private theorem map_augmentation_equiv {n : ℕ} (hn : 0 < n)
    (T : truncAlg k σ n ≃ₐ[k] truncAlg k σ n) :
    (augmentation k σ n).map T.toAlgHom.toRingHom =
      augmentation k σ n := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_augmentation_of_nilpotent hn
      ((mem_nilradical.mp (augmentation_le_nilradical n hx)).map T)
  · intro x hx
    rw [← T.apply_symm_apply x]
    exact Ideal.mem_map_of_mem _ (mem_augmentation_of_nilpotent hn
      ((mem_nilradical.mp (augmentation_le_nilradical n hx)).map T.symm))

private theorem finrank_conjugated_quotient (e : ℕ) (f : Hom M N)
    (T : truncAlg k σ (p ^ e) ≃ₐ[k] truncAlg k σ (p ^ e))
    (U : truncAlg k τ (p ^ e) ≃ₐ[k] truncAlg k τ (p ^ e)) :
    Module.finrank k (truncAlg k σ (p ^ e) ⧸ Ideal.span
      (Set.range fun i => T.symm (mapJet e f (U (truncProj k τ (p ^ e) (X i)))))) =
      Module.finrank k (kerAlg f (p ^ e)) := by
  let J := Ideal.span (Set.range fun i =>
    T.symm (mapJet (p := p) e f (U (truncProj k τ (p ^ e) (X i)))))
  have hJ : J = (((augmentation k τ (p ^ e)).map U.toAlgHom.toRingHom).map
      (mapJet e f).toRingHom).map T.symm.toAlgHom.toRingHom := by
    rw [augmentation_eq_span, Ideal.map_span, Ideal.map_span, Ideal.map_span,
      ← Set.range_comp, ← Set.range_comp, ← Set.range_comp]
    rfl
  rw [map_augmentation_equiv (expChar_pow_pos k p e) U,
    map_augmentation_eq_kerIdeal e f] at hJ
  exact (Ideal.quotientEquivAlg (kerIdeal M f (p ^ e)) J T.symm hJ).symm.toLinearEquiv.finrank_eq

/-- One family of polynomial eigenvectors presents the transported kernel
quotient at the deep width and at every intermediate characteristic-power width. -/
theorem exists_equivariant_equations {e : ℕ} (he : 1 < p ^ e) (f : Hom M N)
    (a : O) {m : ℕ} {c : k} (ha : algebraMap O k a = c) (hm : (m : k) ≠ 0)
    (hc : c ^ m = 1) (hc₀ : c ≠ 0)
    (hM : a ^ m • truncPoint M (p ^ e) = truncPoint M (p ^ e))
    (hN : a ^ m • truncPoint N (p ^ e) = truncPoint N (p ^ e)) :
    ∃ F : τ → MvPolynomial σ k, (∀ i, scale c (F i) = c • F i) ∧
      ∀ b : ℕ, 1 < p ^ b → p ^ b ≤ p ^ e →
        Module.finrank k (truncAlg k σ (p ^ b) ⧸
          Ideal.span (Set.range fun i => truncProj k σ (p ^ b) (F i))) =
          Module.finrank k (kerAlg f (p ^ b)) := by
  let T (b : ℕ) (hb : 1 < p ^ b) := linearize M b hb a ha hm hc₀
  let U (b : ℕ) (hb : 1 < p ^ b) := linearize N b hb a ha hm hc₀
  let g (b : ℕ) (hb : 1 < p ^ b) :=
    (T b hb).symm.toAlgHom.comp ((mapJet (p := p) b f).comp (U b hb).toAlgHom)
  have hcomm (x : truncAlg k τ (p ^ e)) :
      scaleJet e c (g e he x) = g e he (scaleJet e c x) := by
    have hT (y : truncAlg k σ (p ^ e)) :
        scalarJet M e a (T e he y) = T e he (scaleJet e c y) :=
      DFunLike.congr_fun (scalarJet_linearize M e he a ha hm hc hc₀ hM) y
    have hU (y : truncAlg k τ (p ^ e)) :
        scalarJet N e a (U e he y) = U e he (scaleJet e c y) :=
      DFunLike.congr_fun (scalarJet_linearize N e he a ha hm hc hc₀ hN) y
    have hf (y : truncAlg k τ (p ^ e)) :
        scalarJet M e a (mapJet e f y) = mapJet e f (scalarJet N e a y) := by
      apply DFunLike.congr_fun (f := (scalarJet M e a).comp (mapJet e f))
        (g := (mapJet e f).comp (scalarJet N e a)) _ y
      rw [scalarJet, scalarJet, ← mapJet_comp, ← mapJet_comp, f.comp_scalarHom]
    apply (T e he).injective
    simp only [g, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]
    rw [← hT, AlgEquiv.apply_symm_apply, hf, hU, AlgEquiv.apply_symm_apply]
  have hg (b : ℕ) (hb : 1 < p ^ b) (hle : p ^ b ≤ p ^ e)
      (x : truncAlg k τ (p ^ e)) :
      restrictJet hle (g e he x) = g b hb (restrictJet hle x) := by
    apply (T b hb).injective
    simp only [g, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]
    rw [← restrictJet_linearize M hle hb he a ha hm hc₀, AlgEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply]
    have h := DFunLike.congr_fun (restrictJet_mapJet (p := p) hle f) (U e he x)
    simp only [AlgHom.comp_apply] at h
    rw [h, restrictJet_linearize N hle hb he a ha hm hc₀]
  let y : τ → truncAlg k σ (p ^ e) := fun i => g e he (truncProj k τ (p ^ e) (X i))
  have hy (i : τ) : scaleJet e c (y i) = c • y i := by
    change scaleJet e c (g e he (truncProj k τ (p ^ e) (X i))) = c • y i
    rw [hcomm, scaleJet_X, map_smul]
  choose Q hQ using fun i => truncProj_surjective (p ^ e) (y i)
  let F (i : τ) := weightedAverage m c (fun j => scale (c ^ j) (Q i))
  have hF (i : τ) : truncProj k σ (p ^ e) (F i) = y i := by
    have h j : truncProj k σ (p ^ e) (scale (c ^ j) (Q i)) = c ^ j • y i := by
      induction j with
      | zero => simp [scale_one, hQ]
      | succ j ih =>
        rw [pow_succ', mul_comm c, ← scale_comp, AlgHom.comp_apply,
          ← scaleJet_truncProj (p := p), ih, map_smul, hy, smul_smul, mul_comm]
    change (truncProj k σ (p ^ e)).toLinearMap
      (weightedAverage m c (fun j => scale (c ^ j) (Q i))) = _
    rw [map_weightedAverage]
    rw [show (truncProj k σ (p ^ e)).toLinearMap ∘ (fun j => scale (c ^ j) (Q i)) =
      (fun j => c ^ j • y i) from funext h]
    exact weightedAverage_smul_pows hm hc₀ _
  have hm' : m ≠ 0 := fun h => hm (by simp [h])
  refine ⟨F, fun i => scale_weightedAverage hm' hc (Q i), fun b hb hle => ?_⟩
  have h (i : τ) : truncProj k σ (p ^ b) (F i) = g b hb (truncProj k τ (p ^ b) (X i)) := by
    have hr := hg b hb hle (truncProj k τ (p ^ e) (X i))
    change restrictJet hle (y i) = _ at hr
    rw [← restrictJet_truncProj hle, hF, hr, restrictJet_truncProj]
  rw [show (fun i => truncProj k σ (p ^ b) (F i)) =
    (fun i => g b hb (truncProj k τ (p ^ b) (X i))) from funext h]
  exact finrank_conjugated_quotient b f (T b hb) (U b hb)

end Equations

end Langlands.FormalGroup.ModuleLaw.RationalHeightLinearization
