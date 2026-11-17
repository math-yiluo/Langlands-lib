import Langlands.Geometry.Analytic.AffineAnalytificationSeminormStatement

/-! # Proof: points of the affine analytification as multiplicative seminorms -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

open Set Topology Filter PresentedAffinoidAlgebra AnalyticAffineSpace

namespace SeminormComparison

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type v} [CommRing A] [Algebra K A]

/-- A multiplicative seminorm extending the norm of `K` is at most one on naturals. -/
theorem natCast_le_one {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) (n : ℕ) :
    ν (n : A) ≤ 1 := by
  rw [← map_natCast (algebraMap K A) n, hν]
  exact IsUltrametricDist.norm_natCast_le_one K n

/-- The triangle inequality for finite sums. -/
theorem map_sum_le_sum (ν : MulRingSeminorm A) {ι : Type*} (s : Finset ι) (g : ι → A) :
    ν (∑ k ∈ s, g k) ≤ ∑ k ∈ s, ν (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    exact (map_add_le_add ν _ _).trans (add_le_add le_rfl ih)

/-- A multiplicative seminorm extending the norm of the ultrametric field `K` is
ultrametric: the binomial expansion bounds `ν (a + b) ^ N` by `(N + 1) M ^ N`. -/
theorem add_le_max {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) (a b : A) :
    ν (a + b) ≤ max (ν a) (ν b) := by
  set M := max (ν a) (ν b) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (apply_nonneg ν a)
  have key : ∀ N : ℕ, ν (a + b) ^ N ≤ (N + 1) * M ^ N := by
    intro N
    rw [← map_pow, add_pow]
    calc ν (∑ k ∈ Finset.range (N + 1), a ^ k * b ^ (N - k) * (N.choose k : A))
        ≤ ∑ k ∈ Finset.range (N + 1), ν (a ^ k * b ^ (N - k) * (N.choose k : A)) :=
          map_sum_le_sum ν _ _
      _ ≤ ∑ _k ∈ Finset.range (N + 1), M ^ N := by
          apply Finset.sum_le_sum
          intro k hk
          have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [map_mul, map_mul, map_pow, map_pow]
          calc ν a ^ k * ν b ^ (N - k) * ν (N.choose k : A)
              ≤ M ^ k * M ^ (N - k) * 1 := by
                apply mul_le_mul _ (natCast_le_one hν _) (apply_nonneg ν _)
                  (mul_nonneg (pow_nonneg hM0 _) (pow_nonneg hM0 _))
                exact mul_le_mul (pow_le_pow_left₀ (apply_nonneg ν a) (le_max_left _ _) k)
                  (pow_le_pow_left₀ (apply_nonneg ν b) (le_max_right _ _) _)
                  (pow_nonneg (apply_nonneg ν b) _) (pow_nonneg hM0 _)
            _ = M ^ N := by rw [mul_one, ← pow_add, Nat.add_sub_cancel' hkN]
      _ = (N + 1) * M ^ N := by simp
  refine not_lt.mp fun h => ?_
  rcases hM0.eq_or_lt with h0 | h0
  · have h1 := key 1
    rw [← h0] at h1 h
    simp at h1
    linarith
  · obtain ⟨N, hN⟩ := Real.exists_natCast_add_one_lt_pow_of_one_lt ((one_lt_div h0).mpr h)
    rw [div_pow, lt_div_iff₀ (pow_pos h0 N)] at hN
    linarith [key N]

/-- The ultrametric bound for finite sums. -/
theorem map_sum_le_of_le {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) {ι : Type*}
    (s : Finset ι) (g : ι → A) {C : ℝ} (hC : 0 ≤ C) (h : ∀ i ∈ s, ν (g i) ≤ C) :
    ν (∑ i ∈ s, g i) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact (add_le_max hν _ _).trans (max_le (h k (Finset.mem_insert_self k s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

variable (P : FinitePolynomialPresentation K A)

omit [IsUltrametricDist K] in
/-- A monomial evaluated at the generators is bounded by its coefficient norm times
the corresponding power of a bound for the generator values. -/
theorem map_monomial_le {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) {R : ℝ}
    (hR : ∀ i, ν (P.map (MvPolynomial.X i)) ≤ R) (d : Fin P.arity →₀ ℕ) (c : K) :
    ν (P.map (MvPolynomial.monomial d c)) ≤ ‖c‖ * d.prod (fun _ n => R ^ n) := by
  rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.algHom_C, map_mul, hν]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
  rw [Finsupp.prod, Finsupp.prod, map_prod, map_prod]
  refine Finset.prod_le_prod₀ (fun i _ => apply_nonneg ν _) ?_
  intro i _
  rw [map_pow, map_pow]
  exact pow_le_pow_left₀ (apply_nonneg ν _) (hR i) _

/-- The Gauss bound: on polynomials, `p ↦ ν (p(x))` is bounded by the weighted
Gauss norm at a radius dominating the values of the generators. -/
theorem gauss_bound {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) {m : ℕ}
    (hR : ∀ i, ν (P.map (MvPolynomial.X i)) ≤ radius K m)
    (p : MvPolynomial (Fin P.arity) K) :
    ν (P.map p) ≤
      ‖GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K p‖ := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply map_sum_le_of_le hν _ _ (norm_nonneg _)
  intro d _
  refine (map_monomial_le P hν hR d (p.coeff d)).trans ?_
  have h := GeneralizedTateAlgebra.weighted_norm_coeff_le (polyradius K P.arity m) K
    (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K p) d
  rw [GeneralizedTateAlgebra.coeff_polynomialMap] at h
  exact h

/-- The extension of `p ↦ ν (p(x))` to the Tate algebra, by the 1-Lipschitz
infimum formula. -/
def tateValue (ν : MulRingSeminorm A) (m : ℕ)
    (f : GeneralizedTateAlgebra (polyradius K P.arity m) K) : ℝ :=
  ⨅ p : MvPolynomial (Fin P.arity) K,
    (ν (P.map p) + ‖f - GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K p‖)

variable {P}

theorem tateValue_bddBelow (ν : MulRingSeminorm A) (m : ℕ)
    (f : GeneralizedTateAlgebra (polyradius K P.arity m) K) :
    BddBelow (range fun p : MvPolynomial (Fin P.arity) K =>
      ν (P.map p) + ‖f - GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K p‖) :=
  ⟨0, by
    rintro _ ⟨p, rfl⟩
    exact add_nonneg (apply_nonneg ν _) (norm_nonneg _)⟩

theorem tateValue_le (ν : MulRingSeminorm A) (m : ℕ)
    (f : GeneralizedTateAlgebra (polyradius K P.arity m) K) (p : MvPolynomial (Fin P.arity) K) :
    tateValue P ν m f ≤
      ν (P.map p) + ‖f - GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K p‖ :=
  ciInf_le (tateValue_bddBelow ν m f) p

theorem tateValue_polynomial {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) {m : ℕ}
    (hR : ∀ i, ν (P.map (MvPolynomial.X i)) ≤ radius K m) (q : MvPolynomial (Fin P.arity) K) :
    tateValue P ν m (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K q) =
      ν (P.map q) := by
  apply le_antisymm
  · simpa using tateValue_le ν m
      (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K q) q
  · apply le_ciInf
    intro p
    have h1 : ν (P.map q) ≤ ν (P.map p) + ν (P.map q - P.map p) := by
      simpa using map_add_le_add ν (P.map p) (P.map q - P.map p)
    have h2 : ν (P.map q - P.map p) ≤
        ‖GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K q -
          GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K p‖ := by
      rw [← map_sub, ← map_sub]
      exact gauss_bound P hν hR (q - p)
    linarith

theorem tateValue_le_add (ν : MulRingSeminorm A) (m : ℕ)
    (f g : GeneralizedTateAlgebra (polyradius K P.arity m) K) :
    tateValue P ν m f ≤ tateValue P ν m g + ‖f - g‖ := by
  have h : tateValue P ν m f - ‖f - g‖ ≤ tateValue P ν m g := by
    apply le_ciInf
    intro p
    have h1 := tateValue_le ν m f p
    have h2 := norm_sub_le_norm_sub_add_norm_sub f g
      (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K p)
    linarith
  linarith

theorem continuous_tateValue (ν : MulRingSeminorm A) (m : ℕ) :
    Continuous (tateValue P ν m) :=
  (LipschitzWith.of_le_add fun f g => by
    rw [dist_eq_norm]
    exact tateValue_le_add ν m f g).continuous

/-- The point of the spectrum of the Tate algebra defined by `ν`. -/
def tatePoint {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) {m : ℕ}
    (hR : ∀ i, ν (P.map (MvPolynomial.X i)) ≤ radius K m) :
    BanachSpectrum (GeneralizedTateAlgebra (polyradius K P.arity m) K) where
  toFun := tateValue P ν m
  map_zero' := by
    rw [← map_zero (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K),
      tateValue_polynomial hν hR, map_zero, map_zero]
  map_one' := by
    rw [← map_one (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K),
      tateValue_polynomial hν hR, map_one, map_one]
  map_mul' f g := by
    refine isClosed_property2 (p := fun f g => tateValue P ν m (f * g) =
        tateValue P ν m f * tateValue P ν m g)
      (GeneralizedTateAlgebra.denseRange_polynomialMap (polyradius K P.arity m) K) ?_ ?_ f g
    · exact isClosed_eq ((continuous_tateValue ν m).comp continuous_mul)
        (((continuous_tateValue ν m).comp continuous_fst).mul
          ((continuous_tateValue ν m).comp continuous_snd))
    · intro a b
      rw [← map_mul, tateValue_polynomial hν hR, tateValue_polynomial hν hR,
        tateValue_polynomial hν hR, map_mul, map_mul]
  add_le' f g := by
    refine isClosed_property2 (p := fun f g => tateValue P ν m (f + g) ≤
        tateValue P ν m f + tateValue P ν m g)
      (GeneralizedTateAlgebra.denseRange_polynomialMap (polyradius K P.arity m) K) ?_ ?_ f g
    · exact isClosed_le ((continuous_tateValue ν m).comp continuous_add)
        (((continuous_tateValue ν m).comp continuous_fst).add
          ((continuous_tateValue ν m).comp continuous_snd))
    · intro a b
      rw [← map_add, tateValue_polynomial hν hR, tateValue_polynomial hν hR,
        tateValue_polynomial hν hR, map_add]
      exact map_add_le_add ν _ _
  neg' f := by
    refine isClosed_property (p := fun f => tateValue P ν m (-f) = tateValue P ν m f)
      (GeneralizedTateAlgebra.denseRange_polynomialMap (polyradius K P.arity m) K) ?_ ?_ f
    · exact isClosed_eq ((continuous_tateValue ν m).comp continuous_neg)
        (continuous_tateValue ν m)
    · intro a
      rw [← map_neg, tateValue_polynomial hν hR, tateValue_polynomial hν hR, map_neg,
        map_neg_eq_map]
  le_norm f := by
    refine isClosed_property (p := fun f => tateValue P ν m f ≤ ‖f‖)
      (GeneralizedTateAlgebra.denseRange_polynomialMap (polyradius K P.arity m) K) ?_ ?_ f
    · exact isClosed_le (continuous_tateValue ν m) continuous_norm
    · intro a
      rw [tateValue_polynomial hν hR]
      exact gauss_bound P hν hR a

theorem tatePoint_apply {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) {m : ℕ}
    (hR : ∀ i, ν (P.map (MvPolynomial.X i)) ≤ radius K m)
    (f : GeneralizedTateAlgebra (polyradius K P.arity m) K) :
    tatePoint hν hR f = tateValue P ν m f :=
  rfl

/-- `ν` kills the closed relation ideal of the `m`-th chart. -/
theorem ideal_le_kernel {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) {m : ℕ}
    (hR : ∀ i, ν (P.map (MvPolynomial.X i)) ≤ radius K m) :
    (algebra K P m).ideal ≤ (tatePoint hν hR).kernel := by
  have hclosed : IsClosed (((tatePoint hν hR).kernel :
      Ideal (GeneralizedTateAlgebra (polyradius K P.arity m) K)) :
        Set (GeneralizedTateAlgebra (polyradius K P.arity m) K)) :=
    isClosed_eq (continuous_tateValue ν m) continuous_const
  have hspan : Ideal.span (PolynomialLocus.relations P (polyradius K P.arity m)) ≤
      (tatePoint hν hR).kernel := by
    rw [Ideal.span_le]
    rintro _ ⟨p, hp, rfl⟩
    change tateValue P ν m _ = 0
    rw [tateValue_polynomial hν hR]
    have hp' : P.map p = 0 := RingHom.mem_ker.mp hp
    rw [hp', map_zero]
  intro f hf
  have hf' : f ∈ closure (Ideal.span (PolynomialLocus.relations P
      (polyradius K P.arity m)) : Set (GeneralizedTateAlgebra (polyradius K P.arity m) K)) := by
    rw [← Ideal.coe_closure]
    exact hf
  exact closure_minimal hspan hclosed hf'

/-- The point of the `m`-th chart defined by `ν`. -/
def chartPoint {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) {m : ℕ}
    (hR : ∀ i, ν (P.map (MvPolynomial.X i)) ≤ radius K m) :
    BanachSpectrum (algebra K P m) :=
  letI := (algebra K P m).ideal_closed
  BanachSpectrum.descend (algebra K P m).ideal (tatePoint hν hR) (ideal_le_kernel hν hR)

theorem chartSeminorm_chartPoint {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) {m : ℕ}
    (hR : ∀ i, ν (P.map (MvPolynomial.X i)) ≤ radius K m) :
    chartSeminorm K P m (chartPoint hν hR) = ν := by
  ext a
  obtain ⟨p, rfl⟩ := P.surjective a
  rw [chartSeminorm_apply, PolynomialLocus.algebraMap_map]
  change tateValue P ν m (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K p) = _
  exact tateValue_polynomial hν hR p

omit [IsUltrametricDist K] in
theorem exists_level {ν : MulRingSeminorm A} :
    ∃ m, ∀ i, ν (P.map (MvPolynomial.X i)) ≤ radius K m := by
  obtain ⟨m, hm⟩ := exists_radius_gt K (∑ i, ν (P.map (MvPolynomial.X i)))
  exact ⟨m, fun i => (Finset.single_le_sum (fun j _ => apply_nonneg ν
    (P.map (MvPolynomial.X j))) (Finset.mem_univ i)).trans hm.le⟩

variable (K P)

/-- A spectrum point is a 1-Lipschitz function on its algebra. -/
theorem continuous_spectrum_apply {B : Type*} [NormedCommRing B] (s : BanachSpectrum B) :
    Continuous (fun b : B => s b) :=
  (LipschitzWith.of_le_add fun a b => by
    rw [dist_eq_norm]
    have h := map_add_le_add s.toMulRingSeminorm b (a - b)
    rw [add_sub_cancel] at h
    exact h.trans (add_le_add le_rfl (s.le_norm (a - b)))).continuous

theorem denseRange_chartAlgebraMap (m : ℕ) :
    DenseRange (PolynomialLocus.algebraMap P (polyradius K P.arity m)) := by
  have h : DenseRange (PolynomialLocus.polynomialMap P (polyradius K P.arity m)) :=
    (presentationMap_surjective K (algebra K P m)).denseRange.comp
      (GeneralizedTateAlgebra.denseRange_polynomialMap (polyradius K P.arity m) K)
      (presentationMap K (algebra K P m)).continuous
  refine Dense.mono ?_ h
  rintro _ ⟨p, rfl⟩
  exact ⟨P.map p, PolynomialLocus.algebraMap_map P _ p⟩

theorem chartSeminorm_injective (m : ℕ) : Function.Injective (chartSeminorm K P m) := by
  intro s t h
  apply BanachSpectrum.ext
  intro b
  have e := Continuous.ext_on (denseRange_chartAlgebraMap K P m)
    (continuous_spectrum_apply s) (continuous_spectrum_apply t) (by
      rintro _ ⟨a, rfl⟩
      exact congrArg (fun ν : MulRingSeminorm A => ν a) h)
  exact congrFun e b

variable [CompleteSpace K]

theorem range_pointSeminorm :
    range (pointSeminorm K P) = {ν : MulRingSeminorm A | ExtendsNorm K ν} := by
  ext ν
  constructor
  · rintro ⟨x, rfl⟩
    exact pointSeminorm_extendsNorm K P x
  · intro hν
    obtain ⟨m, hm⟩ := exists_level (P := P) (ν := ν)
    exact ⟨chart K P m (chartPoint hν hm), by
      rw [pointSeminorm_chart, chartSeminorm_chartPoint]⟩

theorem pointSeminorm_injective : Function.Injective (pointSeminorm K P) := by
  intro x y h
  obtain ⟨m, s, rfl⟩ := exists_chart K P x
  obtain ⟨k, t, rfl⟩ := exists_chart K P y
  rw [← chart_pull K P (le_max_left m k) s, ← chart_pull K P (le_max_right m k) t] at h ⊢
  rw [pointSeminorm_chart, pointSeminorm_chart] at h
  rw [chartSeminorm_injective K P _ h]

theorem coordinateNorm_eq (i : Fin P.arity) (z : Space K P) :
    coordinateNorm K P i z = pointSeminorm K P z (P.map (MvPolynomial.X i)) := by
  obtain ⟨m, s, rfl⟩ := exists_chart K P z
  rw [coordinateNorm_chart, pointSeminorm_chart, chartSeminorm_apply,
    PolynomialLocus.algebraMap_map, PolynomialLocus.polynomialMap_X]

theorem isEmbedding_pointSeminorm :
    IsEmbedding (fun (x : Space K P) (a : A) => pointSeminorm K P x a) := by
  set Φ := fun (x : Space K P) (a : A) => pointSeminorm K P x a with hΦ
  have hΦc : Continuous Φ := continuous_pi fun a => continuous_pointSeminorm_apply K P a
  have hΦi : Function.Injective Φ := fun x y h =>
    pointSeminorm_injective K P (MulRingSeminorm.ext fun a => congrFun h a)
  refine ⟨?_, hΦi⟩
  rw [isInducing_iff_nhds]
  intro x
  refine le_antisymm (hΦc.tendsto x).le_comap ?_
  intro U hU
  obtain ⟨m, s, rfl⟩ := exists_chart K P x
  have hx : chart K P m s ∈ openDisc K P m := range_chart_subset_openDisc K P m ⟨s, rfl⟩
  obtain ⟨t, ht⟩ := openDisc_subset_range_chart K P m hx
  have hg : IsClosedEmbedding (Φ ∘ chart K P (m + 1)) :=
    (hΦc.comp (continuous_chart K P (m + 1))).isClosedEmbedding
      (hΦi.comp (isClosedEmbedding_chart K P (m + 1)).injective)
  have hU' : chart K P (m + 1) ⁻¹' U ∈ 𝓝 t :=
    (continuous_chart K P (m + 1)).continuousAt.preimage_mem_nhds (by rw [ht]; exact hU)
  rw [hg.isInducing.nhds_eq_comap t] at hU'
  obtain ⟨V, hV, hVU⟩ := hU'
  let W : Set (A → ℝ) := {f | ∀ i, f (P.map (MvPolynomial.X i)) < radius K (m + 1)}
  have hW : IsOpen W := by
    have e : W = ⋂ i, {f : A → ℝ | f (P.map (MvPolynomial.X i)) < radius K (m + 1)} := by
      ext f
      simp [W]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply _) continuous_const
  have hxW : Φ (chart K P m s) ∈ W := fun i => by
    have := hx i
    rw [coordinateNorm_eq] at this
    exact this
  have hV' : V ∈ 𝓝 (Φ (chart K P m s)) := by
    rw [Function.comp_apply, ht] at hV
    exact hV
  refine Filter.mem_comap.mpr ⟨V ∩ W, inter_mem hV' (hW.mem_nhds hxW), ?_⟩
  rintro z ⟨hzV, hzW⟩
  have hzD : z ∈ openDisc K P m := fun i => by
    rw [coordinateNorm_eq]
    exact hzW i
  obtain ⟨u, rfl⟩ := openDisc_subset_range_chart K P m hzD
  exact hVU hzV

end SeminormComparison

open SeminormComparison in
/-- Berkovich 1990, Remark 3.4.2 with the topology of Definition 1.5.1, for the
polynomial-locus affine analytification. -/
theorem affineAnalytificationSeminorm : AffineAnalytificationSeminormStatement.{u, v} := by
  intro K _ _ _ A _ _ P
  exact ⟨isEmbedding_pointSeminorm K P, range_pointSeminorm K P⟩

end Langlands.Analytic.AffineAnalytification
