import Langlands.Geometry.Analytic.DrinfeldExhaustion
import Langlands.Geometry.Analytic.AtlasTopology.Colimit

/-! # Projective linear transformations of Drinfeld's upper half space -/

noncomputable section

universe u v

namespace Langlands.Analytic

open Set Topology Metric PresentedAffinoidAlgebra GeneralizedTateAlgebra CategoryTheory

namespace AnalyticAffineSpace

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] (d : ℕ)

theorem linearForm_add (m : ℕ) (a b : Fin (d + 1) → K) :
    linearForm K d m (a + b) = linearForm K d m a + linearForm K d m b := by
  simp only [linearForm, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
  abel

theorem linearForm_zero (m : ℕ) : linearForm K d m 0 = 0 := by
  simp [linearForm]

theorem linearForm_sum (m : ℕ) {ι : Type*} (s : Finset ι) (c : ι → Fin (d + 1) → K) :
    linearForm K d m (∑ i ∈ s, c i) = ∑ i ∈ s, linearForm K d m (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linearForm_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, linearForm_add, ih]

/-- The norm of an affine-linear function in the polydisc algebra. -/
theorem norm_linearForm_le (m : ℕ) (c : Fin (d + 1) → K) {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ i, ‖c i‖ ≤ B) : ‖linearForm K d m c‖ ≤ (d + 1) * B * radius K m := by
  have h1 := one_le_radius K m
  have hone : ‖(1 : disc K d m)‖ ≤ 1 := norm_one_le K (disc K d m)
  have halg : ∀ t : K, ‖algebraMap K (disc K d m) t‖ ≤ ‖t‖ := fun t => by
    rw [Algebra.algebraMap_eq_smul_one, norm_smul]
    exact (mul_le_mul_of_nonneg_left hone (norm_nonneg t)).trans (mul_one _).le
  have hsum : ‖∑ i : Fin d, c i.succ • coordinate K (disc K d m) i‖ ≤
      ∑ i : Fin d, B * radius K m := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    exact mul_le_mul (hc _) (norm_coordinate_le K (disc K d m) i) (norm_nonneg _) hB
  calc ‖linearForm K d m c‖
      ≤ ‖algebraMap K (disc K d m) (c 0)‖ +
          ‖∑ i : Fin d, c i.succ • coordinate K (disc K d m) i‖ := norm_add_le _ _
    _ ≤ B * radius K m + ∑ i : Fin d, B * radius K m := by
        refine add_le_add ?_ hsum
        calc ‖algebraMap K (disc K d m) (c 0)‖ ≤ ‖c 0‖ := halg _
          _ ≤ B := hc 0
          _ = B * 1 := (mul_one B).symm
          _ ≤ B * radius K m := mul_le_mul_of_nonneg_left h1 hB
    _ = (d + 1) * B * radius K m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end AnalyticAffineSpace

namespace DrinfeldUpperHalfSpace

open AnalyticAffineSpace

variable (F : Type v) [NontriviallyNormedField F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] (d : ℕ)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem coefficients_vecMul (a : Fin (d + 1) → F) (g : Fin (d + 1) → Fin (d + 1) → F) :
    coefficients F K d (Matrix.vecMul a g) =
      ∑ k, algebraMap F K (a k) • coefficients F K d (g k) := by
  ext j
  simp [coefficients, Matrix.vecMul, dotProduct, map_sum, Finset.sum_apply, Algebra.smul_def]

omit [CompleteSpace K] in
/-- `ℓ_{a g} = Σ_k a_k ℓ_{g_k}`: the linear form of `a ᵥ* g` in terms of the rows of `g`. -/
theorem linearForm_vecMul (m : ℕ) (a : Fin (d + 1) → F)
    (g : Fin (d + 1) → Fin (d + 1) → F) :
    linearForm K d m (coefficients F K d (Matrix.vecMul a g)) =
      ∑ k, algebraMap K (disc K d m) (algebraMap F K (a k)) *
        linearForm K d m (coefficients F K d (g k)) := by
  rw [coefficients_vecMul, linearForm_sum]
  exact Finset.sum_congr rfl fun k _ => linearForm_smul K d m _ _

variable [ProperSpace F]

omit [CompleteSpace K] in
/-- On `V_N`, every vector of the shell has `|ℓ_a| ≥ δ_N / 2`. -/
theorem half_threshold_le {N : ℕ} {y : BanachSpectrum (disc K d N)}
    (hy : y ∈ (exhaustionChart F K d N).locus) {a : Fin (d + 1) → F}
    (ha : a ∈ shell F d (bigScalar F)) :
    threshold N / 2 ≤ y (linearForm K d N (coefficients F K d a)) := by
  rw [mem_locus_exhaustionChart] at hy
  obtain ⟨b, hb, hab⟩ := exists_mem_net F K d N ha
  have h1 := linearForm_coefficients_ge F K d N y a b
  have h2 : (d + 1) * ‖a - b‖ * radius K N < threshold N / 2 := by
    rw [← mesh_mul K d N]
    have : (0 : ℝ) < d + 1 := by positivity
    have := radius_pos K N
    gcongr
  have := hy b hb
  linarith

/-- A fixed rescaling of a nonzero coefficient vector into the shell. -/
def shellScale {c : Fin (d + 1) → F} (hc : c ≠ 0) : F :=
  (exists_smul_mem_shell F d (one_lt_norm_bigScalar F) hc).choose

omit [ProperSpace F] in
theorem shellScale_ne_zero {c : Fin (d + 1) → F} (hc : c ≠ 0) : shellScale F d hc ≠ 0 :=
  (exists_smul_mem_shell F d (one_lt_norm_bigScalar F) hc).choose_spec.1

omit [ProperSpace F] in
theorem shellScale_smul_mem {c : Fin (d + 1) → F} (hc : c ≠ 0) :
    shellScale F d hc • c ∈ shell F d (bigScalar F) :=
  (exists_smul_mem_shell F d (one_lt_norm_bigScalar F) hc).choose_spec.2

/-- The explicit lower bound `‖t_c‖⁻¹ δ_N / 2` for `|ℓ_c|` on `V_N`. -/
def lowerBound {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) : ℝ :=
  ‖shellScale F d hc‖⁻¹ * (threshold N / 2)

omit [ProperSpace F] in
theorem lowerBound_pos {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) :
    0 < lowerBound F d hc N :=
  mul_pos (inv_pos.2 (norm_pos_iff.2 (shellScale_ne_zero F d hc)))
    (half_pos (threshold_pos N))

omit [CompleteSpace K] in
theorem lowerBound_le {c : Fin (d + 1) → F} (hc : c ≠ 0) {N : ℕ}
    {y : BanachSpectrum (disc K d N)} (hy : y ∈ (exhaustionChart F K d N).locus) :
    lowerBound F d hc N ≤ y (linearForm K d N (coefficients F K d c)) := by
  have h := half_threshold_le F K d hy (shellScale_smul_mem F d hc)
  rw [coefficients_smul, linearForm_smul, map_mul y.toMulRingSeminorm] at h
  change threshold N / 2 ≤ y (algebraMap K (disc K d N) (algebraMap F K (shellScale F d hc))) *
    y (linearForm K d N (coefficients F K d c)) at h
  rw [BanachSpectrum.algebraMap_apply, norm_algebraMap'] at h
  have hpos : 0 < ‖shellScale F d hc‖ := norm_pos_iff.2 (shellScale_ne_zero F d hc)
  unfold lowerBound
  rw [inv_mul_le_iff₀ hpos]
  exact h

/-! ## The inverse of a nonvanishing linear form on `V_N` -/

/-- The Laurent chart `{y | r_N ≤ |ℓ_c(y)|}` of the `N`-th polydisc, with the
explicit lower bound `r_N`; it contains `V_N`. -/
abbrev boundChart {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) : RationalChart K (disc K d N) :=
  laurentChart K d N (coefficients F K d c) (lowerBound F d hc N) (lowerBound_pos F d hc N)

theorem hasImageIn_boundChart {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) :
    HasImageIn K (exhaustionChart F K d N).baseMap (boundChart F K d hc N).locus := by
  intro x
  have hx : BanachSpectrum.comap (exhaustionChart F K d N).baseMap.toBoundedRingHom x ∈
      (exhaustionChart F K d N).locus := by
    rw [← (RationalChart.represents (exhaustionChart F K d N)).2.1]
    exact mem_range_self x
  rw [mem_locus_laurentChart]
  exact lowerBound_le F K d hc hx

/-- The map from the Laurent chart algebra to the chart algebra of `V_N`. -/
def boundChartMap {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) :
    BoundedAlgHom K (boundChart F K d hc N).algebra (exhaustionChart F K d N).algebra :=
  ((RationalChart.represents (boundChart F K d hc N)).2.2 _ _
    (hasImageIn_boundChart F K d hc N)).exists.choose

theorem boundChartMap_comp_baseMap {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) :
    (boundChartMap F K d hc N).comp (boundChart F K d hc N).baseMap =
      (exhaustionChart F K d N).baseMap :=
  ((RationalChart.represents (boundChart F K d hc N)).2.2 _ _
    (hasImageIn_boundChart F K d hc N)).exists.choose_spec

/-- The fraction coordinate `1 / ℓ_c` of the Laurent chart. -/
def boundFraction {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) : (boundChart F K d hc N).algebra :=
  RationalPresentation.fraction K (disc K d N)
    (boundChart F K d hc N).radii (boundChart F K d hc N).denominator
    (boundChart F K d hc N).numerators (0 : Fin 1)

omit [CompleteSpace K] [ProperSpace F] in
theorem norm_boundFraction_le {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) :
    ‖boundFraction F K d hc N‖ ≤ (lowerBound F d hc N)⁻¹ :=
  RationalPresentation.norm_fraction_le K (disc K d N) _ _ _ (0 : Fin 1)

/-- The inverse of `ℓ_c` in the chart algebra of `V_N`. -/
def inverse {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) : (exhaustionChart F K d N).algebra :=
  boundChartMap F K d hc N (boundFraction F K d hc N)

omit [CompleteSpace K] [ProperSpace F] in
theorem boundFraction_equation {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) :
    (boundChart F K d hc N).baseMap (linearForm K d N (coefficients F K d c)) *
      boundFraction F K d hc N = 1 := by
  have h := RationalPresentation.fraction_equation K (disc K d N)
    (boundChart F K d hc N).radii (boundChart F K d hc N).denominator
    (boundChart F K d hc N).numerators (0 : Fin 1)
  have e1 : presentationMap K (disc K d N) (boundChart F K d hc N).denominator =
      linearForm K d N (coefficients F K d c) := presentationMap_linearSeries K d N _
  have e2 : presentationMap K (disc K d N) ((boundChart F K d hc N).numerators (0 : Fin 1)) =
      1 := map_one _
  rw [e1, e2, map_one] at h
  exact h

theorem linearForm_mul_inverse {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) :
    (exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d c)) *
      inverse F K d hc N = 1 := by
  have hb : (exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d c)) =
      boundChartMap F K d hc N
        ((boundChart F K d hc N).baseMap (linearForm K d N (coefficients F K d c))) :=
    (congrArg (fun φ : BoundedAlgHom K _ _ => φ (linearForm K d N (coefficients F K d c)))
      (boundChartMap_comp_baseMap F K d hc N)).symm
  rw [hb]
  change (boundChartMap F K d hc N).toAlgHom _ *
    (boundChartMap F K d hc N).toAlgHom (boundFraction F K d hc N) = 1
  rw [← map_mul, boundFraction_equation, map_one]

theorem norm_inverse_pow_le {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖inverse F K d hc N ^ n‖ ≤ C * (lowerBound F d hc N)⁻¹ ^ n := by
  obtain ⟨C, hC, hbound⟩ := (boundChartMap F K d hc N).bounded
  refine ⟨C, hC, fun n => ?_⟩
  have hZ := norm_boundFraction_le F K d hc N
  have hpow : ‖boundFraction F K d hc N ^ n‖ ≤ (lowerBound F d hc N)⁻¹ ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, pow_zero]
      exact norm_one_le K (boundChart F K d hc N).algebra
    · exact (norm_pow_le' _ hn).trans (pow_le_pow_left₀ (norm_nonneg _) hZ n)
  have heq : inverse F K d hc N ^ n =
      (boundChartMap F K d hc N).toAlgHom (boundFraction F K d hc N ^ n) := by
    rw [map_pow]
    rfl
  rw [heq]
  exact (hbound _).trans (mul_le_mul_of_nonneg_left hpow hC.le)

/-! ## The evaluation map of a projective linear transformation -/

variable {F d}
variable (g : Fin (d + 1) → Fin (d + 1) → F) (hg : g 0 ≠ 0)

/-- `|ℓ_{g_k}|` is bounded by the total row norm `Σ_k ‖g_k‖`. -/
def rowBound : ℝ := ∑ k, ‖g k‖

omit [ProperSpace F] in
theorem rowBound_nonneg : 0 ≤ rowBound g := Finset.sum_nonneg fun _ _ => norm_nonneg _

omit [ProperSpace F] in
theorem norm_row_le_rowBound (k : Fin (d + 1)) : ‖g k‖ ≤ rowBound g :=
  Finset.single_le_sum (f := fun k => ‖g k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)

/-- The image of `Tᵢ`: the function `ℓ_{g_{i+1}} / ℓ_{g_0}` on `V_N`. -/
def actionTuple (N : ℕ) : Fin d → (exhaustionChart F K d N).algebra := fun i =>
  (exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d (g i.succ))) *
    inverse F K d hg N

/-- The constant of the norm bound of the inverse. -/
def inverseConst (N : ℕ) : ℝ := (norm_inverse_pow_le F K d hg N).choose

theorem inverseConst_pos (N : ℕ) : 0 < inverseConst K g hg N :=
  (norm_inverse_pow_le F K d hg N).choose_spec.1

theorem norm_inverse_le (N : ℕ) :
    ‖inverse F K d hg N‖ ≤ inverseConst K g hg N * (lowerBound F d hg N)⁻¹ := by
  have h := (norm_inverse_pow_le F K d hg N).choose_spec.2 1
  rw [pow_one, pow_one] at h
  exact h

/-- The bound `(d + 1) (Σ_k ‖g_k‖) ‖ϖ‖⁻ᴺ · C r_N⁻¹` for the image tuple. -/
def actionBound (N : ℕ) : ℝ :=
  ((d + 1) * rowBound g * radius K N) * (inverseConst K g hg N * (lowerBound F d hg N)⁻¹)

theorem norm_actionTuple_le (N : ℕ) (i : Fin d) :
    ‖actionTuple K g hg N i‖ ≤ actionBound K g hg N := by
  have hℓ : ‖(exhaustionChart F K d N).baseMap
      (linearForm K d N (coefficients F K d (g i.succ)))‖ ≤ (d + 1) * rowBound g * radius K N :=
    (PresentedAffinoidAlgebra.RationalPresentation.norm_baseMap_le K (disc K d N) _ _ _ _).trans
      (norm_linearForm_le K d N _ (rowBound_nonneg g) fun j => by
        rw [coefficients, norm_algebraMap']
        exact (norm_le_pi_norm (g i.succ) j).trans (norm_row_le_rowBound g i.succ))
  exact (norm_mul_le _ _).trans (mul_le_mul hℓ (norm_inverse_le K g hg N) (norm_nonneg _)
    (by have := rowBound_nonneg g; have := radius_pos K N; positivity))

/-- The bounded evaluation `Tᵢ ↦ ℓ_{g_{i+1}} / ℓ_{g_0}` from the `n`-th polydisc
algebra to the chart algebra of `V_N`, for `n` large enough. -/
def actionHom (N n : ℕ) (hn : actionBound K g hg N ≤ radius K n) :
    BoundedAlgHom K (disc K d n) (exhaustionChart F K d N).algebra := by
  letI := (disc K d n).ideal_closed
  exact BoundedAlgHom.liftQuotient K (disc K d n).ideal
    (evaluateHom (polyradius K d n) K _ (actionTuple K g hg N)
      ⟨1, one_pos, fun e => by
        rw [one_mul]
        exact monomialValue_norm_le_weight _ _ (norm_one_le K _) _
          (fun i => (norm_actionTuple_le K g hg N i).trans hn) e⟩)
    (by
      intro a ha
      have ha0 : a = 0 := ha
      rw [ha0, map_zero])

theorem actionHom_coordinate (N n : ℕ) (hn : actionBound K g hg N ≤ radius K n)
    (i : Fin d) :
    actionHom K g hg N n hn (coordinate K (disc K d n) i) = actionTuple K g hg N i :=
  evaluate_X (polyradius K d n) K _ _ i

/-- The evaluation map sends `ℓ_a` to `ℓ_{a g} / ℓ_{g_0}`. -/
theorem actionHom_linearForm (N n : ℕ) (hn : actionBound K g hg N ≤ radius K n)
    (a : Fin (d + 1) → F) :
    actionHom K g hg N n hn (linearForm K d n (coefficients F K d a)) =
      (exhaustionChart F K d N).baseMap
        (linearForm K d N (coefficients F K d (Matrix.vecMul a g))) * inverse F K d hg N := by
  set A := (exhaustionChart F K d N).algebra
  set β := (exhaustionChart F K d N).baseMap
  set u := inverse F K d hg N
  have hlhs : actionHom K g hg N n hn (linearForm K d n (coefficients F K d a)) =
      algebraMap K A (algebraMap F K (a 0)) +
        ∑ i : Fin d, algebraMap K A (algebraMap F K (a i.succ)) * actionTuple K g hg N i := by
    change (actionHom K g hg N n hn).toAlgHom (algebraMap K (disc K d n) (algebraMap F K (a 0)) +
      ∑ i : Fin d, algebraMap F K (a i.succ) • coordinate K (disc K d n) i) = _
    rw [map_add, AlgHom.commutes, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
    congr 1
    exact actionHom_coordinate K g hg N n hn i
  have hrhs : β (linearForm K d N (coefficients F K d (Matrix.vecMul a g))) * u =
      ∑ k, algebraMap K A (algebraMap F K (a k)) *
        (β (linearForm K d N (coefficients F K d (g k))) * u) := by
    rw [linearForm_vecMul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes, mul_assoc]
  rw [hlhs, hrhs, Fin.sum_univ_succ]
  have h0 : β (linearForm K d N (coefficients F K d (g 0))) * u = 1 :=
    linearForm_mul_inverse F K d hg N
  rw [h0, mul_one]
  rfl

theorem inverse_apply_ne_zero (N : ℕ) (x : BanachSpectrum (exhaustionChart F K d N).algebra) :
    x (inverse F K d hg N) ≠ 0 := by
  intro h
  have h1 := congrArg x.toMulRingSeminorm (linearForm_mul_inverse F K d hg N)
  rw [map_mul x.toMulRingSeminorm, map_one x.toMulRingSeminorm] at h1
  change _ * x (inverse F K d hg N) = 1 at h1
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

variable (F d) in
theorem baseMap_linearForm_ne_zero (N : ℕ) (x : BanachSpectrum (exhaustionChart F K d N).algebra)
    {a : Fin (d + 1) → F} (ha : a ≠ 0) :
    x ((exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d a))) ≠ 0 := by
  have hx : BanachSpectrum.comap (exhaustionChart F K d N).baseMap.toBoundedRingHom x ∈
      (exhaustionChart F K d N).locus := by
    rw [← (RationalChart.represents (exhaustionChart F K d N)).2.1]
    exact mem_range_self x
  exact exhaustion_subset_omega F K d N ⟨_, hx, rfl⟩ a ha

/-- The image point `g · x` in the `n`-th closed polydisc. -/
def actionPoint (N n : ℕ) (hn : actionBound K g hg N ≤ radius K n)
    (x : BanachSpectrum (exhaustionChart F K d N).algebra) : Space K d :=
  chart K d n (BanachSpectrum.comap (actionHom K g hg N n hn).toBoundedRingHom x)

theorem linearNorm_actionPoint (N n : ℕ) (hn : actionBound K g hg N ≤ radius K n)
    (x : BanachSpectrum (exhaustionChart F K d N).algebra) (a : Fin (d + 1) → F) :
    linearNorm K d (coefficients F K d a) (actionPoint K g hg N n hn x) =
      x ((exhaustionChart F K d N).baseMap
        (linearForm K d N (coefficients F K d (Matrix.vecMul a g)))) *
        x (inverse F K d hg N) := by
  rw [actionPoint, linearNorm_chart]
  change x (actionHom K g hg N n hn (linearForm K d n (coefficients F K d a))) = _
  rw [actionHom_linearForm, map_mul x.toMulRingSeminorm]

end DrinfeldUpperHalfSpace

namespace DrinfeldUpperHalfSpace

open AnalyticAffineSpace

variable {F : Type v} [NontriviallyNormedField F]
  {d : ℕ} (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F)

theorem vecMul_ne_zero {a : Fin (d + 1) → F} (ha : a ≠ 0) :
    Matrix.vecMul a (γ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ≠ 0 := by
  intro h
  apply ha
  have h1 : (γ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) *
      ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc a = Matrix.vecMul a 1 := (Matrix.vecMul_one a).symm
    _ = Matrix.vecMul (Matrix.vecMul a (γ : Matrix (Fin (d + 1)) (Fin (d + 1)) F))
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by rw [Matrix.vecMul_vecMul, h1]
    _ = 0 := by rw [h, Matrix.zero_vecMul]

theorem row_zero_ne_zero : (γ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) 0 ≠ 0 := by
  have h := vecMul_ne_zero γ (a := Pi.single 0 1) (fun h => by
    simpa using congrFun h (0 : Fin (d + 1)))
  rwa [Matrix.single_one_vecMul] at h

/-- The entries of an invertible matrix, as a plain function. -/
def entries : Fin (d + 1) → Fin (d + 1) → F :=
  fun i j => (γ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j

theorem entries_row_zero_ne_zero : entries γ 0 ≠ 0 := row_zero_ne_zero γ

theorem vecMul_entries_ne_zero {a : Fin (d + 1) → F} (ha : a ≠ 0) :
    Matrix.vecMul a (entries γ) ≠ 0 := vecMul_ne_zero γ ha

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] [ProperSpace F]

/-- `g · x` lies in `Ω` for invertible `g`. -/
theorem actionPoint_mem_omega (N n : ℕ)
    (hn : actionBound K (entries γ) (entries_row_zero_ne_zero γ) N ≤ radius K n)
    (x : BanachSpectrum (exhaustionChart F K d N).algebra) :
    actionPoint K (entries γ) (entries_row_zero_ne_zero γ) N n hn x ∈ Omega F K d := by
  intro a ha
  rw [linearNorm_actionPoint]
  exact mul_ne_zero (baseMap_linearForm_ne_zero F K d N x (vecMul_entries_ne_zero γ ha))
    (inverse_apply_ne_zero K _ (entries_row_zero_ne_zero γ) N x)

end DrinfeldUpperHalfSpace

/-! ## Compatibility with the restrictions of the exhaustion -/

namespace DrinfeldUpperHalfSpace

open AnalyticAffineSpace

variable {F : Type v} [NontriviallyNormedField F] [ProperSpace F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ} [NeZero d]

theorem atlas_restriction_linearForm {m q : ℕ}
    (h : Set.range ((AnalyticAffineSpace.atlas K d).chart m) ⊆
      Set.range ((AnalyticAffineSpace.atlas K d).chart q)) (c : Fin (d + 1) → K) :
    (AnalyticAffineSpace.atlas K d).restriction m q h (linearForm K d q c) = linearForm K d m c :=
  restriction_linearForm K d ((range_chart_subset_iff K d).1 h) c

theorem atlas_restriction_coordinate {m q : ℕ}
    (h : Set.range ((AnalyticAffineSpace.atlas K d).chart m) ⊆
      Set.range ((AnalyticAffineSpace.atlas K d).chart q)) (i : Fin d) :
    (AnalyticAffineSpace.atlas K d).restriction m q h (coordinate K (disc K d q) i) =
      coordinate K (disc K d m) i :=
  Polydisc.restriction_coordinate _ _ _ i

/-- The restriction between members of the exhaustion, typed in the chart algebras. -/
def exhaustionRes {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1) :
    BoundedAlgHom K (exhaustionChart F K d V.level).algebra
      (exhaustionChart F K d U.level).algebra :=
  (exhaustionInclusion F K d h).restriction

/-- The restriction between members of the exhaustion preserves the affine-linear
functions. -/
theorem exhaustionRestriction_baseMap {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1)
    (c : Fin (d + 1) → K) :
    exhaustionRes K h
        ((exhaustionChart F K d V.level).baseMap (linearForm K d V.level c)) =
      (exhaustionChart F K d U.level).baseMap (linearForm K d U.level c) := by
  obtain ⟨q, hUq', hVq'⟩ : ∃ q : ℕ, U.level ≤ q ∧ V.level ≤ q :=
    ⟨max U.level V.level, le_max_left _ _, le_max_right _ _⟩
  have hUq : Set.range ((AnalyticAffineSpace.atlas K d).chart U.level) ⊆
      Set.range ((AnalyticAffineSpace.atlas K d).chart q) := range_chart_mono K d hUq'
  have hVq : Set.range ((AnalyticAffineSpace.atlas K d).chart V.level) ⊆
      Set.range ((AnalyticAffineSpace.atlas K d).chart q) := range_chart_mono K d hVq'
  have h1 := congrArg (fun φ : BoundedAlgHom K (disc K d q)
      (exhaustionChart F K d U.level).algebra => φ (linearForm K d q c))
    ((exhaustionInclusion F K d h).comp_baseMap q hUq hVq)
  change exhaustionRes K h ((exhaustionChart F K d V.level).baseMap
      ((AnalyticAffineSpace.atlas K d).restriction V.level q hVq (linearForm K d q c))) =
    (exhaustionChart F K d U.level).baseMap ((AnalyticAffineSpace.atlas K d).restriction
      U.level q hUq (linearForm K d q c)) at h1
  rw [atlas_restriction_linearForm, atlas_restriction_linearForm] at h1
  exact h1

variable (g : Fin (d + 1) → Fin (d + 1) → F) (hg : g 0 ≠ 0)

theorem exhaustionRestriction_inverse {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1) :
    exhaustionRes K h (inverse F K d hg V.level) = inverse F K d hg U.level := by
  have h1 := congrArg (fun a => exhaustionRes K h a) (linearForm_mul_inverse F K d hg V.level)
  simp only [map_mul, map_one] at h1
  rw [exhaustionRestriction_baseMap] at h1
  have h2 := linearForm_mul_inverse F K d hg U.level
  calc exhaustionRes K h (inverse F K d hg V.level)
      = 1 * exhaustionRes K h (inverse F K d hg V.level) :=
        (one_mul _).symm
    _ = ((exhaustionChart F K d U.level).baseMap
          (linearForm K d U.level (coefficients F K d (g 0))) * inverse F K d hg U.level) *
          exhaustionRes K h (inverse F K d hg V.level) := by rw [h2]
    _ = inverse F K d hg U.level * ((exhaustionChart F K d U.level).baseMap
          (linearForm K d U.level (coefficients F K d (g 0))) *
          exhaustionRes K h (inverse F K d hg V.level)) := by ring
    _ = inverse F K d hg U.level := by rw [h1, mul_one]

theorem exhaustionRestriction_actionTuple {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1)
    (i : Fin d) :
    exhaustionRes K h (actionTuple K g hg V.level i) = actionTuple K g hg U.level i := by
  unfold actionTuple
  rw [map_mul, exhaustionRestriction_baseMap, exhaustionRestriction_inverse]

/-- The image point does not depend on the member of the exhaustion or on the
target polydisc used to compute it. -/
theorem actionPoint_restriction {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1) (n n' : ℕ)
    (hn : actionBound K g hg U.level ≤ radius K n)
    (hn' : actionBound K g hg V.level ≤ radius K n')
    (x : BanachSpectrum (exhaustionChart F K d U.level).algebra) :
    actionPoint K g hg V.level n' hn'
        (BanachSpectrum.comap (exhaustionRes K h).toBoundedRingHom x) =
      actionPoint K g hg U.level n hn x := by
  obtain ⟨m, hnm, hn'm⟩ : ∃ m : ℕ, n ≤ m ∧ n' ≤ m :=
    ⟨max n n', le_max_left _ _, le_max_right _ _⟩
  have hmaps : (actionHom K g hg U.level n hn).comp (restriction K d hnm) =
      (exhaustionRes K h).comp ((actionHom K g hg V.level n' hn').comp (restriction K d hn'm)) := by
    apply hom_ext_coordinate
    intro i
    change actionHom K g hg U.level n hn (restriction K d hnm (coordinate K (disc K d m) i)) =
      exhaustionRes K h (actionHom K g hg V.level n' hn'
        (restriction K d hn'm (coordinate K (disc K d m) i)))
    calc actionHom K g hg U.level n hn (restriction K d hnm (coordinate K (disc K d m) i))
        = actionHom K g hg U.level n hn (coordinate K (disc K d n) i) :=
          congrArg _ (Polydisc.restriction_coordinate _ _ _ i)
      _ = actionTuple K g hg U.level i := actionHom_coordinate K g hg U.level n hn i
      _ = exhaustionRes K h (actionTuple K g hg V.level i) :=
          (exhaustionRestriction_actionTuple K g hg h i).symm
      _ = exhaustionRes K h (actionHom K g hg V.level n' hn' (coordinate K (disc K d n') i)) :=
          congrArg _ (actionHom_coordinate K g hg V.level n' hn' i).symm
      _ = exhaustionRes K h (actionHom K g hg V.level n' hn'
            (restriction K d hn'm (coordinate K (disc K d m) i))) :=
          congrArg _ (congrArg _ (Polydisc.restriction_coordinate _ _ _ i).symm)
  unfold actionPoint
  rw [← chart_pull K d hnm, ← chart_pull K d hn'm]
  congr 1
  apply BanachSpectrum.ext
  intro f
  exact (congrArg (fun φ : BoundedAlgHom K (disc K d m) (exhaustionChart F K d U.level).algebra =>
    x (φ f)) hmaps).symm

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem exists_radius_ge (r : ℝ) : ∃ n : ℕ, r ≤ radius K n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt r (one_lt_inv_norm_scale K)
  exact ⟨n, hn.le⟩

/-- The first polydisc whose radius dominates the action bound on `V_N`. -/
def actionLevel (N : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_radius_ge K (actionBound K g hg N))

omit [NeZero d] in
theorem actionLevel_spec (N : ℕ) : actionBound K g hg N ≤ radius K (actionLevel K g hg N) := by
  classical
  exact Nat.find_spec (exists_radius_ge K (actionBound K g hg N))

/-- The image `g · x` of a point of the chart of a member of the exhaustion. -/
def chartAction (U : ExhaustionIndex F K d)
    (x : BanachSpectrum (exhaustionChart F K d U.level).algebra) : Space K d :=
  actionPoint K g hg U.level (actionLevel K g hg U.level) (actionLevel_spec K g hg U.level) x

omit [NeZero d] in
theorem continuous_chartAction (U : ExhaustionIndex F K d) :
    Continuous (chartAction K g hg U) :=
  (continuous_chart K d _).comp (BanachSpectrum.comapContinuous _).continuous

theorem chartAction_restriction {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1)
    (x : BanachSpectrum (exhaustionChart F K d U.level).algebra) :
    chartAction K g hg V (BanachSpectrum.comap (exhaustionRes K h).toBoundedRingHom x) =
      chartAction K g hg U x :=
  actionPoint_restriction K g hg h _ _ _ _ x

end DrinfeldUpperHalfSpace

/-! ## The continuous map of an invertible matrix on `Ω` -/

namespace DrinfeldUpperHalfSpace

open AnalyticAffineSpace

variable {F : Type v} [NontriviallyNormedField F] [ProperSpace F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ} [NeZero d] (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F)

/-- The chart-member family of the exhaustion atlas. -/
abbrev exhaustionFamily : Set (Set (Omega F K d)) :=
  Set.range fun U : ExhaustionIndex F K d => Set.range (exhaustionChartMap F K d U)

theorem isNet_exhaustionFamily :
    AtlasTopology.IsNet (exhaustionFamily (F := F) K (d := d)) :=
  (exhaustionAtlas F K d).isNet_chartFamily

theorem isEmbedding_exhaustionChartMap (U : ExhaustionIndex F K d) :
    IsEmbedding (exhaustionChartMap F K d U) :=
  ((continuous_exhaustionChartMap F K d U).isClosedEmbedding
    (injective_exhaustionChartMap F K d U)).isEmbedding

theorem exhaustionChartMap_res {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1)
    (x : BanachSpectrum (exhaustionChart F K d U.level).algebra) :
    exhaustionChartMap F K d V (BanachSpectrum.comap (exhaustionRes K h).toBoundedRingHom x) =
      exhaustionChartMap F K d U x :=
  Subtype.ext (IndexedAffinoidAtlas.DirectedDomain.Inclusion.ambientMap_naturality
    (exhaustionInclusion F K d h) x)

/-- An index whose chart image is the given member. -/
def memberIndex (W : AtlasTopology.Member (exhaustionFamily (F := F) K (d := d))) :
    ExhaustionIndex F K d :=
  W.2.choose

theorem range_memberIndex (W : AtlasTopology.Member (exhaustionFamily (F := F) K (d := d))) :
    Set.range (exhaustionChartMap F K d (memberIndex K W)) = W.1 :=
  W.2.choose_spec

omit [NeZero d] in
theorem chartAction_mem_omega (U : ExhaustionIndex F K d)
    (x : BanachSpectrum (exhaustionChart F K d U.level).algebra) :
    chartAction K (entries γ) (entries_row_zero_ne_zero γ) U x ∈ Omega F K d :=
  actionPoint_mem_omega γ K _ _ _ x

/-- The action on one member, computed through its chart. -/
def memberMap (W : AtlasTopology.Member (exhaustionFamily (F := F) K (d := d))) :
    C(W.1, Omega F K d) where
  toFun w :=
    ⟨chartAction K (entries γ) (entries_row_zero_ne_zero γ) (memberIndex K W)
      ((isEmbedding_exhaustionChartMap K (memberIndex K W)).toHomeomorph.symm
        ⟨w.1, by rw [range_memberIndex]; exact w.2⟩),
      chartAction_mem_omega K γ _ _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ((continuous_chartAction K _ _ _).comp
      ((Homeomorph.continuous _).comp (Continuous.subtype_mk continuous_subtype_val _))) _

theorem memberMap_chart (W : AtlasTopology.Member (exhaustionFamily (F := F) K (d := d)))
    (x : BanachSpectrum (exhaustionChart F K d (memberIndex K W).level).algebra)
    (hx : exhaustionChartMap F K d (memberIndex K W) x ∈ W.1) :
    (memberMap K γ W ⟨_, hx⟩).1 =
      chartAction K (entries γ) (entries_row_zero_ne_zero γ) (memberIndex K W) x := by
  show chartAction K _ _ _ ((isEmbedding_exhaustionChartMap K
    (memberIndex K W)).toHomeomorph.symm
      ⟨exhaustionChartMap F K d (memberIndex K W) x, mem_range_self x⟩) = _
  exact congrArg _ (IsEmbedding.toHomeomorph_symm_apply _ x)

/-- The compatible family of member maps. -/
def compatibleMaps : AtlasTopology.CompatibleMaps (exhaustionFamily (F := F) K (d := d))
    (Omega F K d) where
  map := memberMap K γ
  comm W W' h w := by
    have hUV : (memberIndex K W).1 ⊆ (memberIndex K W').1 := by
      rw [← range_exhaustionChartMap_subset_iff F K d, range_memberIndex, range_memberIndex]
      exact h
    have hw : w.1 ∈ Set.range (exhaustionChartMap F K d (memberIndex K W)) := by
      rw [range_memberIndex]
      exact w.2
    obtain ⟨x, hx⟩ := hw
    have hx' : exhaustionChartMap F K d (memberIndex K W')
        (BanachSpectrum.comap (exhaustionRes K hUV).toBoundedRingHom x) = w.1 :=
      (exhaustionChartMap_res K hUV x).trans hx
    apply Subtype.ext
    have e1 : (memberMap K γ W' (Set.inclusion h w)).1 =
        chartAction K (entries γ) (entries_row_zero_ne_zero γ) (memberIndex K W')
          (BanachSpectrum.comap (exhaustionRes K hUV).toBoundedRingHom x) := by
      have := memberMap_chart K γ W'
        (BanachSpectrum.comap (exhaustionRes K hUV).toBoundedRingHom x)
        (by rw [hx']; exact h w.2)
      rw [← this]
      congr 2
      exact Subtype.ext hx'.symm
    have e2 : (memberMap K γ W w).1 =
        chartAction K (entries γ) (entries_row_zero_ne_zero γ) (memberIndex K W) x := by
      have := memberMap_chart K γ W x (by rw [hx]; exact w.2)
      rw [← this]
      congr 2
      exact Subtype.ext hx.symm
    rw [e1, e2]
    exact chartAction_restriction K _ _ hUV x

/-- The continuous map `z ↦ γ · z` of `Ω`. -/
def actionMap : C(Omega F K d, Omega F K d) :=
  AtlasTopology.IsNet.glue (isNet_exhaustionFamily (F := F) K (d := d)) (compatibleMaps K γ)

end DrinfeldUpperHalfSpace

/-! ## Independence of the polydisc and restriction of coordinates -/

namespace AnalyticAffineSpace

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (d : ℕ)

omit [CompleteSpace K] in
theorem disc_restriction_coordinate {m k : ℕ} (h : m ≤ k) (i : Fin d) :
    restriction K d h (coordinate K (disc K d k) i) = coordinate K (disc K d m) i :=
  Polydisc.restriction_coordinate _ _ _ i

end AnalyticAffineSpace

namespace DrinfeldUpperHalfSpace

open AnalyticAffineSpace ExhaustionIndex

variable {F : Type v} [NontriviallyNormedField F] [ProperSpace F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ}

section

variable (g : Fin (d + 1) → Fin (d + 1) → F) (hg : g 0 ≠ 0)

theorem actionHom_comp_restriction (N : ℕ) {n m : ℕ} (h : n ≤ m)
    (hn : actionBound K g hg N ≤ radius K n) (hm : actionBound K g hg N ≤ radius K m) :
    (actionHom K g hg N n hn).comp (restriction K d h) = actionHom K g hg N m hm := by
  apply hom_ext_coordinate
  intro i
  change actionHom K g hg N n hn (restriction K d h (coordinate K (disc K d m) i)) =
    actionHom K g hg N m hm (coordinate K (disc K d m) i)
  exact (congrArg _ (disc_restriction_coordinate K d h i)).trans
    ((actionHom_coordinate K g hg N n hn i).trans (actionHom_coordinate K g hg N m hm i).symm)

/-- The image point does not depend on the target polydisc. -/
theorem actionPoint_mono (N : ℕ) {n m : ℕ} (h : n ≤ m)
    (hn : actionBound K g hg N ≤ radius K n) (hm : actionBound K g hg N ≤ radius K m)
    (x : BanachSpectrum (exhaustionChart F K d N).algebra) :
    actionPoint K g hg N m hm x = actionPoint K g hg N n hn x := by
  unfold actionPoint
  rw [← chart_pull K d h]
  congr 1
  apply BanachSpectrum.ext
  intro f
  exact (congrArg (fun φ : BoundedAlgHom K (disc K d m) (exhaustionChart F K d N).algebra =>
    x (φ f)) (actionHom_comp_restriction K g hg N h hn hm)).symm

end

variable [NeZero d]

theorem exhaustionRes_baseMap_restriction {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1)
    {q : ℕ} (hU : U.level ≤ q) (hV : V.level ≤ q) (f : disc K d q) :
    exhaustionRes K h ((exhaustionChart F K d V.level).baseMap (restriction K d hV f)) =
      (exhaustionChart F K d U.level).baseMap (restriction K d hU f) :=
  congrArg (fun φ : BoundedAlgHom K (disc K d q) (exhaustionChart F K d U.level).algebra => φ f)
    ((exhaustionInclusion F K d h).comp_baseMap q (range_chart_mono K d hU)
      (range_chart_mono K d hV))

theorem exhaustionRes_coordinate {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1) (i : Fin d) :
    exhaustionRes K h
        ((exhaustionChart F K d V.level).baseMap (coordinate K (disc K d V.level) i)) =
      (exhaustionChart F K d U.level).baseMap (coordinate K (disc K d U.level) i) := by
  have e := exhaustionRes_baseMap_restriction K h (le_max_left U.level V.level)
    (le_max_right U.level V.level) (coordinate K (disc K d (max U.level V.level)) i)
  rw [disc_restriction_coordinate, disc_restriction_coordinate] at e
  exact e

variable (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F)

/-- The value of the glued map on a chart point is the chart action. -/
theorem actionMap_chart (U : ExhaustionIndex F K d)
    (x : BanachSpectrum (exhaustionChart F K d U.level).algebra) :
    (actionMap K γ (exhaustionChartMap F K d U x)).1 =
      chartAction K (entries γ) (entries_row_zero_ne_zero γ) U x := by
  let W : AtlasTopology.Member (exhaustionFamily (F := F) K (d := d)) :=
    ⟨Set.range (exhaustionChartMap F K d U), ⟨U, rfl⟩⟩
  have hglue := AtlasTopology.IsNet.glue_apply (isNet_exhaustionFamily (F := F) K (d := d))
    (compatibleMaps K γ) W ⟨exhaustionChartMap F K d U x, mem_range_self x⟩
  have hsub : U.1 ⊆ (memberIndex K W).1 := by
    rw [← range_exhaustionChartMap_subset_iff F K d, range_memberIndex]
  have hx : exhaustionChartMap F K d (memberIndex K W)
      (BanachSpectrum.comap (exhaustionRes K hsub).toBoundedRingHom x) ∈ W.1 := by
    rw [exhaustionChartMap_res]
    exact mem_range_self x
  have e := memberMap_chart K γ W _ hx
  rw [chartAction_restriction] at e
  change (AtlasTopology.IsNet.glue (isNet_exhaustionFamily (F := F) K (d := d))
    (compatibleMaps K γ) (exhaustionChartMap F K d U x)).1 = _
  rw [hglue, ← e]
  change (memberMap K γ W _).1 = (memberMap K γ W _).1
  congr 2
  exact Subtype.ext (exhaustionChartMap_res K hsub x).symm

omit [NeZero d] in
theorem exists_chartAction_subset (U : ExhaustionIndex F K d) :
    ∃ N, ∀ x, chartAction K (entries γ) (entries_row_zero_ne_zero γ) U x ∈
      exhaustion F K d N := by
  obtain ⟨N, hN⟩ := exists_subset_exhaustion F K d
    (isCompact_range (continuous_chartAction K (entries γ) (entries_row_zero_ne_zero γ) U))
    (by
      rintro _ ⟨x, rfl⟩
      exact chartAction_mem_omega K γ U x)
  exact ⟨N, fun x => hN ⟨x, rfl⟩⟩

/-- The first member of the exhaustion that contains the image of a chart. -/
def targetLevel (U : ExhaustionIndex F K d) : ℕ := by
  classical
  exact Nat.find (exists_chartAction_subset K γ U)

omit [NeZero d] in
theorem chartAction_mem_targetLevel (U : ExhaustionIndex F K d)
    (x : BanachSpectrum (exhaustionChart F K d U.level).algebra) :
    chartAction K (entries γ) (entries_row_zero_ne_zero γ) U x ∈
      exhaustion F K d (targetLevel K γ U) := by
  classical
  exact Nat.find_spec (exists_chartAction_subset K γ U) x

theorem targetLevel_mono {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1) :
    targetLevel K γ U ≤ targetLevel K γ V := by
  classical
  refine Nat.find_min' (exists_chartAction_subset K γ U) fun x => ?_
  rw [← chartAction_restriction K _ _ h x]
  exact chartAction_mem_targetLevel K γ V _

/-- The chosen target chart: the member `V_{N'}` for the first `N'` containing the image. -/
def targetIndex (U : ExhaustionIndex F K d) : ExhaustionIndex F K d :=
  ofLevel (targetLevel K γ U)

theorem targetIndex_mono {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1) :
    (targetIndex K γ U).1 ⊆ (targetIndex K γ V).1 :=
  exhaustion_mono F K d (targetLevel_mono K γ h)

omit [NeZero d] in
theorem exhaustion_targetIndex_level (U : ExhaustionIndex F K d) :
    exhaustion F K d (targetIndex K γ U).level = exhaustion F K d (targetLevel K γ U) :=
  (targetIndex K γ U).exhaustion_level

/-- A polydisc containing the target chart on which the evaluation map is defined. -/
def sourceLevel (U : ExhaustionIndex F K d) : ℕ :=
  max (targetIndex K γ U).level (actionLevel K (entries γ) (entries_row_zero_ne_zero γ) U.level)

omit [NeZero d] in
theorem le_sourceLevel (U : ExhaustionIndex F K d) :
    (targetIndex K γ U).level ≤ sourceLevel K γ U :=
  le_max_left _ _

omit [NeZero d] in
theorem actionBound_le_sourceLevel (U : ExhaustionIndex F K d) :
    actionBound K (entries γ) (entries_row_zero_ne_zero γ) U.level ≤
      radius K (sourceLevel K γ U) :=
  (actionLevel_spec K _ _ U.level).trans ((radius_le_radius_iff K).2 (le_max_right _ _))

/-- The target member as a domain of the polydisc `sourceLevel U`. -/
def targetDomain (U : ExhaustionIndex F K d) : Domain K (disc K d (sourceLevel K γ U)) :=
  (AnalyticAffineSpace.atlas K d).extendDomain (targetIndex K γ U).level (sourceLevel K γ U)
    (range_chart_mono K d (le_sourceLevel K γ U))
    (exhaustionChart F K d (targetIndex K γ U).level).toDomain

theorem hasImageIn_targetDomain (U : ExhaustionIndex F K d) :
    HasImageIn K (actionHom K (entries γ) (entries_row_zero_ne_zero γ) U.level
      (sourceLevel K γ U) (actionBound_le_sourceLevel K γ U)) (targetDomain K γ U).locus := by
  intro x
  have hx := chartAction_mem_targetLevel K γ U x
  rw [← exhaustion_targetIndex_level] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  refine ⟨y, hy, ?_⟩
  apply (isClosedEmbedding_chart K d (sourceLevel K γ U)).injective
  refine ((AnalyticAffineSpace.atlas K d).restriction_chart _ _
    (range_chart_mono K d (le_sourceLevel K γ U)) y).trans (hxy.trans ?_)
  exact (actionPoint_mono K _ _ U.level (le_max_right _ _) (actionLevel_spec K _ _ U.level)
    (actionBound_le_sourceLevel K γ U) x).symm

/-- The pullback of functions along `γ` from the target chart to the source chart. -/
def pullback (U : ExhaustionIndex F K d) :
    BoundedAlgHom K (exhaustionChart F K d (targetIndex K γ U).level).algebra
      (exhaustionChart F K d U.level).algebra :=
  ((targetDomain K γ U).represents.2.2 _ _ (hasImageIn_targetDomain K γ U)).exists.choose

theorem pullback_comp_baseMap (U : ExhaustionIndex F K d) :
    (pullback K γ U).comp (targetDomain K γ U).baseMap =
      actionHom K (entries γ) (entries_row_zero_ne_zero γ) U.level (sourceLevel K γ U)
        (actionBound_le_sourceLevel K γ U) :=
  ((targetDomain K γ U).represents.2.2 _ _ (hasImageIn_targetDomain K γ U)).exists.choose_spec

theorem pullback_targetDomain_coordinate (U : ExhaustionIndex F K d) (i : Fin d) :
    pullback K γ U ((targetDomain K γ U).baseMap (coordinate K (disc K d (sourceLevel K γ U)) i)) =
      actionTuple K (entries γ) (entries_row_zero_ne_zero γ) U.level i :=
  (congrArg (fun φ : BoundedAlgHom K _ _ => φ (coordinate K (disc K d (sourceLevel K γ U)) i))
    (pullback_comp_baseMap K γ U)).trans (actionHom_coordinate K _ _ _ _ _ i)

theorem targetDomain_coordinate (U : ExhaustionIndex F K d) (i : Fin d) :
    (targetDomain K γ U).baseMap (coordinate K (disc K d (sourceLevel K γ U)) i) =
      (exhaustionChart F K d (targetIndex K γ U).level).baseMap
        (coordinate K (disc K d (targetIndex K γ U).level) i) :=
  congrArg (exhaustionChart F K d (targetIndex K γ U).level).baseMap
    (disc_restriction_coordinate K d (le_sourceLevel K γ U) i)

/-- The pullback sends the coordinate `Tᵢ` of the target chart to `ℓ_{g_{i+1}} / ℓ_{g_0}`. -/
theorem pullback_coordinate (U : ExhaustionIndex F K d) (i : Fin d) :
    pullback K γ U ((exhaustionChart F K d (targetIndex K γ U).level).baseMap
        (coordinate K (disc K d (targetIndex K γ U).level) i)) =
      actionTuple K (entries γ) (entries_row_zero_ne_zero γ) U.level i := by
  rw [← targetDomain_coordinate]
  exact pullback_targetDomain_coordinate K γ U i

theorem chart_pullback (U : ExhaustionIndex F K d)
    (x : BanachSpectrum (exhaustionChart F K d U.level).algebra) :
    exhaustionChartMap F K d (targetIndex K γ U)
        (BanachSpectrum.comap (pullback K γ U).toBoundedRingHom x) =
      actionMap K γ (exhaustionChartMap F K d U x) := by
  apply Subtype.ext
  rw [actionMap_chart]
  have e : BanachSpectrum.comap ((AnalyticAffineSpace.atlas K d).restriction _ _
        (range_chart_mono K d (le_sourceLevel K γ U))).toBoundedRingHom
      (BanachSpectrum.comap
        (exhaustionChart F K d (targetIndex K γ U).level).baseMap.toBoundedRingHom
        (BanachSpectrum.comap (pullback K γ U).toBoundedRingHom x)) =
      BanachSpectrum.comap (actionHom K (entries γ) (entries_row_zero_ne_zero γ) U.level
        (sourceLevel K γ U) (actionBound_le_sourceLevel K γ U)).toBoundedRingHom x := by
    apply BanachSpectrum.ext
    intro f
    exact congrArg (fun φ : BoundedAlgHom K (disc K d (sourceLevel K γ U))
      (exhaustionChart F K d U.level).algebra => x (φ f)) (pullback_comp_baseMap K γ U)
  change chart K d (targetIndex K γ U).level (BanachSpectrum.comap
    (exhaustionChart F K d (targetIndex K γ U).level).baseMap.toBoundedRingHom
      (BanachSpectrum.comap (pullback K γ U).toBoundedRingHom x)) = _
  refine ((AnalyticAffineSpace.atlas K d).restriction_chart _ _
    (range_chart_mono K d (le_sourceLevel K γ U)) _).symm.trans ?_
  exact (congrArg ((AnalyticAffineSpace.atlas K d).chart (sourceLevel K γ U)) e).trans
    (actionPoint_mono K _ _ U.level (le_max_right _ _) (actionLevel_spec K _ _ U.level)
      (actionBound_le_sourceLevel K γ U) x)

theorem pullback_restriction {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1) :
    (exhaustionRes K h).comp (pullback K γ V) =
      (pullback K γ U).comp (exhaustionRes K (targetIndex_mono K γ h)) := by
  apply (targetDomain K γ V).represents.hom_ext
  apply hom_ext_coordinate
  intro i
  change exhaustionRes K h (pullback K γ V ((targetDomain K γ V).baseMap
      (coordinate K (disc K d (sourceLevel K γ V)) i))) =
    pullback K γ U (exhaustionRes K (targetIndex_mono K γ h) ((targetDomain K γ V).baseMap
      (coordinate K (disc K d (sourceLevel K γ V)) i)))
  calc exhaustionRes K h (pullback K γ V ((targetDomain K γ V).baseMap
        (coordinate K (disc K d (sourceLevel K γ V)) i)))
      = exhaustionRes K h (actionTuple K (entries γ) (entries_row_zero_ne_zero γ) V.level i) :=
        congrArg _ (pullback_targetDomain_coordinate K γ V i)
    _ = actionTuple K (entries γ) (entries_row_zero_ne_zero γ) U.level i :=
        exhaustionRestriction_actionTuple K _ _ h i
    _ = pullback K γ U ((exhaustionChart F K d (targetIndex K γ U).level).baseMap
          (coordinate K (disc K d (targetIndex K γ U).level) i)) :=
        (pullback_coordinate K γ U i).symm
    _ = pullback K γ U (exhaustionRes K (targetIndex_mono K γ h)
          ((exhaustionChart F K d (targetIndex K γ V).level).baseMap
            (coordinate K (disc K d (targetIndex K γ V).level) i))) :=
        congrArg _ (exhaustionRes_coordinate K (targetIndex_mono K γ h) i).symm
    _ = pullback K γ U (exhaustionRes K (targetIndex_mono K γ h) ((targetDomain K γ V).baseMap
          (coordinate K (disc K d (sourceLevel K γ V)) i))) :=
        congrArg _ (congrArg _ (targetDomain_coordinate K γ V i).symm)

/-- The morphism of atlas presentations of `Ω` given by an invertible matrix `γ`:
the map `z ↦ γ · z` with its chart pullbacks. -/
def presentationHom :
    AffinoidAtlasPresentation.Hom (exhaustionPresentation F K d) (exhaustionPresentation F K d) where
  baseMap := actionMap K γ
  indexMap := targetIndex K γ
  index_mono _ _ h := (range_exhaustionChartMap_subset_iff F K d).2
    (targetIndex_mono K γ ((range_exhaustionChartMap_subset_iff F K d).1 h))
  pullback := pullback K γ
  chart_comm := chart_pullback K γ
  restriction_comm _ _ h :=
    pullback_restriction K γ ((range_exhaustionChartMap_subset_iff F K d).1 h)

end DrinfeldUpperHalfSpace

end Langlands.Analytic
