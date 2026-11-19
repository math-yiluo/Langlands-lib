import Langlands.Geometry.Analytic.AffineAnalytificationLocalDomainMaps
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Langlands.Geometry.Analytic.MonicPresentationFiniteness
import Langlands.Geometry.Analytic.FiniteBanachCancellation
import Langlands.Geometry.Analytic.FiniteBanachModule
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Finite algebra maps give finite Banach chart maps on analytifications -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification.FiniteCharts

open Set Polynomial PresentedAffinoidAlgebra AnalyticAffineSpace IndexedAffinoidAtlas
  LocalDomainMaps

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]

section RootBound

variable {B : Type w} [CommRing B] [Algebra K B]

/-- Ultrametric root bound: if `b ^ n + ∑_{j < n} a_j b ^ j = 0` and a multiplicative
seminorm extending the norm of `K` is at most `C` on every `a_j`, then it is at most
`max 1 C` at `b`. -/
theorem map_le_max_of_root {ν : MulRingSeminorm B} (hν : ExtendsNorm K ν) (b : B) (n : ℕ)
    (a : ℕ → B) {C : ℝ} (hC : ∀ j < n, ν (a j) ≤ C)
    (h0 : b ^ n + ∑ j ∈ Finset.range n, a j * b ^ j = 0) :
    ν b ≤ max 1 C := by
  by_contra hlt
  push Not at hlt
  have ht1 : 1 < ν b := lt_of_le_of_lt (le_max_left _ _) hlt
  have ht0 : 0 < ν b := zero_lt_one.trans ht1
  have hM0 : 0 ≤ max 1 C := le_max_of_le_left zero_le_one
  cases n with
  | zero =>
    have h1 : (1 : B) = 0 := by simpa using h0
    have hb : b = 0 := by rw [← mul_one b, h1, mul_zero]
    rw [hb, map_zero] at ht0
    exact lt_irrefl _ ht0
  | succ k =>
    set S := ∑ j ∈ Finset.range (k + 1), a j * b ^ j with hS
    have hbound : ν S ≤ max 1 C * ν b ^ k := by
      apply SeminormComparison.map_sum_le_of_le hν _ _ (mul_nonneg hM0 (pow_nonneg ht0.le k))
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [map_mul, map_pow]
      exact mul_le_mul ((hC j (Finset.mem_range.mp hj)).trans (le_max_right _ _))
        (pow_le_pow_right₀ ht1.le hjk) (pow_nonneg ht0.le _) hM0
    have hpow : ν b ^ (k + 1) ≤ max 1 C * ν b ^ k := by
      have e : b ^ (k + 1) = -S := eq_neg_of_add_eq_zero_left h0
      rw [← map_pow, e, map_neg_eq_map]
      exact hbound
    have hlt' : max 1 C * ν b ^ k < ν b ^ (k + 1) := by
      rw [pow_succ']
      exact mul_lt_mul_of_pos_right hlt (pow_pos ht0 k)
    linarith

end RootBound

section Coefficients

omit [IsUltrametricDist K] in
/-- Scaling the roots of a monic polynomial by a scalar `t` of norm at most one gives
coefficients of norm at most one, as soon as `‖t‖ * C ≤ 1` for a bound `C` on the old
coefficients. -/
theorem norm_coeff_scaleRoots_le {R : Type w} [NormedCommRing R] [NormedAlgebra K R]
    (h1 : ‖(1 : R)‖ ≤ 1) (p : R[X]) (hp : p.Monic) (t : K) (ht : ‖t‖ ≤ 1) {C : ℝ}
    (hC : ∀ j, ‖p.coeff j‖ ≤ C) (htC : ‖t‖ * C ≤ 1) (j : ℕ) :
    ‖(scaleRoots p (algebraMap K R t)).coeff j‖ ≤ 1 := by
  rw [coeff_scaleRoots, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, norm_smul,
    norm_pow]
  rcases lt_or_ge j p.natDegree with hj | hj
  · calc
      _ ≤ ‖t‖ * C := mul_le_mul (pow_le_of_le_one (norm_nonneg _) ht (by omega)) (hC j)
          (norm_nonneg _) (norm_nonneg _)
      _ ≤ 1 := htC
  · rw [Nat.sub_eq_zero_of_le hj, pow_zero, one_mul]
    rcases hj.lt_or_eq with hj | hj
    · rw [coeff_eq_zero_of_natDegree_lt hj, norm_zero]
      exact zero_le_one
    · rw [← hj, hp.coeff_natDegree]
      exact h1

/-- The coefficients of `X - C a` have norm at most one when `a` and `1` do. -/
theorem norm_coeff_X_sub_C_le {R : Type w} [NormedCommRing R] (h1 : ‖(1 : R)‖ ≤ 1) (a : R)
    (ha : ‖a‖ ≤ 1) (j : ℕ) : ‖(X - C a).coeff j‖ ≤ 1 := by
  rcases j with _ | _ | j
  · rw [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, norm_neg]
    exact ha
  · rw [coeff_sub, coeff_X_one, coeff_C_succ, sub_zero]
    exact h1
  · rw [coeff_sub, coeff_X_of_ne_one (by omega), coeff_C_succ, sub_zero, norm_zero]
    exact zero_le_one

omit [IsUltrametricDist K] in
/-- Over a nontrivially normed field, a module-finite bounded map of Banach algebras is
finite in Berkovich's Banach sense, by the open mapping theorem. -/
theorem isFiniteBanach_of_finite {R : Type v} {S : Type w} [NormedCommRing R]
    [NormedCommRing S] [NormedAlgebra K R] [NormedAlgebra K S] [CompleteSpace R]
    [CompleteSpace S] (φ : BoundedAlgHom K R S) (hφ : φ.toAlgHom.toRingHom.Finite) :
    φ.IsFiniteBanach := by
  obtain ⟨n, b, hb⟩ := φ.finite_iff_exists_surjective_coefficientMap.mp hφ
  obtain ⟨C, hC, hpre⟩ := φ.coefficientMap_exists_preimage_norm_le b hb
  exact ⟨n, b, C, hC, hpre⟩

end Coefficients

variable [CompleteSpace K] {A : Type v} [CommRing A] [Algebra K A]
  {B : Type w} [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

section Bound

/-- Integral equations bound the coordinates of points over a target chart: if the
`k`-th generator of `B` is a root of a monic polynomial over `A` whose coefficients have
norm at most `C` in the `n`-th chart algebra of `P`, then its coordinate norm is at most
`max 1 C` at every point mapping into the `n`-th chart. -/
theorem coordinateNorm_le_of_monic (n : ℕ) (k : Fin Q.arity) (q : A[X]) (hq : q.Monic)
    (hz : q.eval₂ f.toRingHom (Q.map (MvPolynomial.X k)) = 0) {C : ℝ}
    (hC : ∀ j, ‖PolynomialLocus.algebraMap P (polyradius K P.arity n) (q.coeff j)‖ ≤ C)
    (y : Space K Q) (hy : baseMap K P Q f y ∈ range (chart K P n)) :
    coordinateNorm K Q k y ≤ max 1 C := by
  obtain ⟨w, hw⟩ := hy
  rw [SeminormComparison.coordinateNorm_eq]
  apply map_le_max_of_root (pointSeminorm_extendsNorm K Q y) _
    q.natDegree (fun j => f (q.coeff j))
  · intro j _
    rw [← pointSeminorm_baseMap, ← hw, pointSeminorm_chart, chartSeminorm_apply]
    exact (w.le_norm _).trans (hC j)
  · have h := congrArg (fun p => p.eval₂ f.toRingHom (Q.map (MvPolynomial.X k))) hq.as_sum
    simp only [eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C] at h
    rw [← hz, h]
    rfl

end Bound

section Chart

/-- The Weierstrass chart of the `m`-th chart algebra of `Q` cut out by the conditions
`|f(xₜ)| ≤ radius n` on the images of the generators of `A`. -/
def preimageChart (m n : ℕ) : RationalChart K (algebra K Q m) where
  arity := P.arity
  radii := polyradius K P.arity n
  denominator := 1
  numerators := fun t =>
    GeneralizedTateAlgebra.polynomialMap (polyradius K Q.arity m) K (generatorLift K P Q f t)
  generates := by
    apply Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert _ _))
    rw [map_one]
    exact isUnit_one

omit [CompleteSpace K] in
theorem preimageChart_locus (m n : ℕ) :
    (preimageChart P Q f m n).locus =
      {x | ∀ t, x (generatorValue K P Q f m t) ≤ radius K n} := by
  ext x
  change (∀ t, x (presentationMap K (algebra K Q m)
      ((preimageChart P Q f m n).numerators t)) ≤
    polyradius K P.arity n t * x (presentationMap K (algebra K Q m) 1)) ↔ _
  simp only [map_one, mul_one]
  rfl

omit [CompleteSpace K] in
theorem preimageChart_fraction (m n : ℕ) (t : Fin P.arity) :
    coordinate K (preimageChart P Q f m n).algebra (Fin.natAdd Q.arity t) =
      (preimageChart P Q f m n).baseMap (generatorValue K P Q f m t) :=
  RationalPresentation.weierstrass_fraction K (algebra K Q m) _ _ t

omit [CompleteSpace K] in
theorem preimageChart_coordinate (m n : ℕ) (k : Fin Q.arity) :
    coordinate K (preimageChart P Q f m n).algebra (Fin.castAdd P.arity k) =
      (preimageChart P Q f m n).baseMap (coordinate K (algebra K Q m) k) :=
  (PresentedAffinoidAlgebra.RationalPresentation.baseMap_coordinate (A := algebra K Q m) (i := k) ..).symm

/-- The Weierstrass chart as a local domain of the atlas of `Q`, transported to the
selected representative of the `m`-th chart. -/
def preimageDomain (m n : ℕ) : LocalDomain (atlas K Q) :=
  ⟨representative K Q m,
    Domain.transportBase (representativeEquiv K Q m).symm (preimageChart P Q f m n).toDomain⟩

theorem localAlgebraMap_preimageDomain (m n : ℕ) (b : B) :
    localAlgebraMap Q (preimageDomain P Q f m n) b =
      (preimageChart P Q f m n).baseMap
        (PolynomialLocus.algebraMap Q (polyradius K Q.arity m) b) := by
  change (preimageChart P Q f m n).baseMap ((representativeEquiv K Q m)
      (PolynomialLocus.algebraMap Q (polyradius K Q.arity (representative K Q m).val) b)) = _
  rw [representativeEquiv, equalRangeEquiv_algebraMap]

theorem preimageDomain_ambientMap (m n : ℕ)
    (x : BanachSpectrum (preimageDomain P Q f m n).algebra) :
    (preimageDomain P Q f m n).ambientMap x =
      chart K Q m (BanachSpectrum.comap
        (preimageChart P Q f m n).baseMap.toBoundedRingHom x) := by
  rw [← affinoidBaseMap_localAlgebraMap]
  symm
  apply chart_comap_eq_affinoidBaseMap
  intro b
  exact (localAlgebraMap_preimageDomain P Q f m n b).symm

theorem preimageDomain_locus (m n : ℕ) :
    (preimageDomain P Q f m n).locus =
      chart K Q m '' {x | ∀ t, x (generatorValue K P Q f m t) ≤ radius K n} := by
  rw [← LocalDomain.range_ambientMap, ← preimageChart_locus,
    ← (preimageChart P Q f m n).represents.2.1]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, (preimageDomain_ambientMap P Q f m n x).symm⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, preimageDomain_ambientMap P Q f m n x⟩

theorem chart_image_subset_preimage (m n : ℕ) :
    chart K Q m '' {x | ∀ t, x (generatorValue K P Q f m t) ≤ radius K n} ⊆
      baseMap K P Q f ⁻¹' range (chart K P n) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_preimage, mem_range_chart_iff]
  intro t
  rw [coordinateNorm_baseMap_chart]
  exact hx t

theorem chart_image_eq_preimage (m n : ℕ)
    (hm : ∀ y, baseMap K P Q f y ∈ range (chart K P n) → y ∈ range (chart K Q m)) :
    chart K Q m '' {x | ∀ t, x (generatorValue K P Q f m t) ≤ radius K n} =
      baseMap K P Q f ⁻¹' range (chart K P n) := by
  refine (chart_image_subset_preimage P Q f m n).antisymm fun y hy => ?_
  obtain ⟨x, rfl⟩ := hm y hy
  refine ⟨x, fun t => ?_, rfl⟩
  rw [← coordinateNorm_baseMap_chart]
  exact (mem_range_chart_iff K P n _).mp hy t

end Chart

section Finite

theorem preimageDomain_coordinate_castAdd (m n : ℕ) (k : Fin Q.arity) :
    coordinate K (preimageDomain P Q f m n).algebra (Fin.castAdd P.arity k) =
      localAlgebraMap Q (preimageDomain P Q f m n) (Q.map (MvPolynomial.X k)) := by
  rw [localAlgebraMap_preimageDomain, ← coordinate_eq_algebraMap]
  exact preimageChart_coordinate P Q f m n k

theorem preimageDomain_coordinate_natAdd (m n : ℕ) (t : Fin P.arity) :
    coordinate K (preimageDomain P Q f m n).algebra (Fin.natAdd Q.arity t) =
      localAlgebraMap Q (preimageDomain P Q f m n) (f (P.map (MvPolynomial.X t))) := by
  rw [localAlgebraMap_preimageDomain, ← generatorValue_eq_algebraMap K P Q f m t]
  exact preimageChart_fraction P Q f m n t

/-- The `n`-th chart algebra of `P` maps boundedly to the Weierstrass preimage domain,
compatibly with `f`. -/
theorem exists_preimageDomain_lift (m n : ℕ) :
    ∃ ψ : BoundedAlgHom K (algebra K P n) (preimageDomain P Q f m n).algebra,
      ∀ a, ψ (PolynomialLocus.algebraMap P (polyradius K P.arity n) a) =
        localAlgebraMap Q (preimageDomain P Q f m n) (f a) := by
  apply exists_chart_lift P n _ ((localAlgebraMap Q (preimageDomain P Q f m n)).comp f)
  intro x
  rw [← baseMap_affinoidBaseMap P Q f, affinoidBaseMap_localAlgebraMap]
  apply chart_image_subset_preimage P Q f m n
  rw [← preimageDomain_locus, ← LocalDomain.range_ambientMap]
  exact mem_range_self x

/-- If the generators of `B` satisfy monic equations over `A` whose coefficients have norm
at most `radius m` in the `n`-th chart algebra of `P`, then the lift of `f` to the
Weierstrass preimage domain is module-finite. -/
theorem finite_of_preimageDomain_lift (m n : ℕ) (q : Fin Q.arity → A[X])
    (hq : ∀ k, (q k).Monic)
    (hz : ∀ k, (q k).eval₂ f.toRingHom (Q.map (MvPolynomial.X k)) = 0)
    (hC : ∀ k j, ‖PolynomialLocus.algebraMap P (polyradius K P.arity n) ((q k).coeff j)‖ ≤
      radius K m)
    (ψ : BoundedAlgHom K (algebra K P n) (preimageDomain P Q f m n).algebra)
    (hψ : ∀ a, ψ (PolynomialLocus.algebraMap P (polyradius K P.arity n) a) =
      localAlgebraMap Q (preimageDomain P Q f m n) (f a)) :
    ψ.toAlgHom.toRingHom.Finite := by
  classical
  have hscale (k : ℕ) : ‖((scale K)⁻¹ ^ k : K)‖ = radius K k := by
    rw [norm_pow, norm_inv]
    rfl
  have hsr (k : ℕ) : ‖(scale K ^ k : K)‖ * radius K k = 1 := by
    rw [norm_pow, radius, ← mul_pow, mul_inv_cancel₀ (norm_scale_pos K).ne', one_pow]
  have hle (k : ℕ) : ‖(scale K ^ k : K)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_scale_lt_one K).le
  have hcomp : ψ.toAlgHom.toRingHom.comp
      (PolynomialLocus.algebraMap P (polyradius K P.arity n)).toRingHom =
      (localAlgebraMap Q (preimageDomain P Q f m n)).toRingHom.comp f.toRingHom :=
    RingHom.ext hψ
  have key (k : Fin Q.arity) : (q k).eval₂ (ψ.toAlgHom.toRingHom.comp
      (PolynomialLocus.algebraMap P (polyradius K P.arity n)).toRingHom)
      (localAlgebraMap Q (preimageDomain P Q f m n) (Q.map (MvPolynomial.X k))) = 0 := by
    rw [hcomp]
    have e := hom_eval₂ (q k) f.toRingHom (localAlgebraMap Q (preimageDomain P Q f m n)).toRingHom
      (Q.map (MvPolynomial.X k))
    rw [hz k, map_zero] at e
    exact e.symm
  let c : Fin (Q.arity + P.arity) → K :=
    Fin.addCases (fun _ => (scale K)⁻¹ ^ m) (fun _ => (scale K)⁻¹ ^ n)
  let p : Fin (Q.arity + P.arity) → (algebra K P n)[X] :=
    Fin.addCases
      (fun k => scaleRoots ((q k).map (PolynomialLocus.algebraMap P (polyradius K P.arity n)).toRingHom)
        (algebraMap K (algebra K P n) (scale K ^ m)))
      (fun t => X - C ((scale K ^ n : K) • coordinate K (algebra K P n) t))
  have hc : ∀ i : Fin (Q.arity + P.arity),
      ‖c i‖ = (preimageDomain P Q f m n).algebra.polyradius i := by
    intro i
    refine Fin.addCases (fun k => ?_) (fun t => ?_) i
    · show ‖c (Fin.castAdd P.arity k)‖ =
        ((polyradius K Q.arity m).append (polyradius K P.arity n)) (Fin.castAdd P.arity k)
      rw [PositivePolyradius.append_castAdd]
      simp only [c, Fin.addCases_left]
      exact hscale m
    · show ‖c (Fin.natAdd Q.arity t)‖ =
        ((polyradius K Q.arity m).append (polyradius K P.arity n)) (Fin.natAdd Q.arity t)
      rw [PositivePolyradius.append_natAdd]
      simp only [c, Fin.addCases_right]
      exact hscale n
  have hm : ∀ i, (p i).Monic := by
    intro i
    refine Fin.addCases (fun k => ?_) (fun t => ?_) i
    · simp only [p, Fin.addCases_left]
      exact (monic_scaleRoots_iff _).mpr ((hq k).map _)
    · simp only [p, Fin.addCases_right]
      exact monic_X_sub_C _
  have hu : ∀ i j, ‖(p i).coeff j‖ ≤ 1 := by
    intro i
    refine Fin.addCases (fun k => ?_) (fun t => ?_) i
    · simp only [p, Fin.addCases_left]
      refine norm_coeff_scaleRoots_le (PresentedAffinoidAlgebra.norm_one_le K _) _
        ((hq k).map _) _ (hle m) (C := radius K m) (fun j => ?_) (hsr m).le
      rw [coeff_map]
      exact hC k j
    · simp only [p, Fin.addCases_right]
      refine norm_coeff_X_sub_C_le (PresentedAffinoidAlgebra.norm_one_le K _) _ ?_
      rw [norm_smul, ← hsr n]
      exact mul_le_mul_of_nonneg_left
        (PresentedAffinoidAlgebra.norm_coordinate_le K (algebra K P n) t) (norm_nonneg _)
  have hz' : ∀ i : Fin (Q.arity + P.arity), (p i).eval₂ ψ.toAlgHom.toRingHom
      ((c i)⁻¹ • coordinate K (preimageDomain P Q f m n).algebra i) = 0 := by
    intro i
    refine Fin.addCases (fun k => ?_) (fun t => ?_) i
    · simp only [p, c, Fin.addCases_left]
      rw [inv_pow, inv_inv]
      refine (congrArg (fun z => eval₂ ψ.toAlgHom.toRingHom ((scale K ^ m : K) • z)
        (scaleRoots ((q k).map (PolynomialLocus.algebraMap P (polyradius K P.arity n)).toRingHom)
          (algebraMap K (algebra K P n) (scale K ^ m))))
        (preimageDomain_coordinate_castAdd P Q f m n k)).trans ?_
      rw [Algebra.smul_def]
      have hs : algebraMap K (preimageDomain P Q f m n).algebra (scale K ^ m) =
          ψ.toAlgHom.toRingHom (algebraMap K (algebra K P n) (scale K ^ m)) :=
        (ψ.toAlgHom.commutes _).symm
      rw [hs, scaleRoots_eval₂_mul, eval₂_map, key k, mul_zero]
    · simp only [p, c, Fin.addCases_right]
      rw [inv_pow, inv_inv]
      refine (congrArg (fun z => eval₂ ψ.toAlgHom.toRingHom ((scale K ^ n : K) • z)
        (X - C ((scale K ^ n : K) • coordinate K (algebra K P n) t)))
        (preimageDomain_coordinate_natAdd P Q f m n t)).trans ?_
      rw [eval₂_sub, eval₂_X, eval₂_C, sub_eq_zero]
      change _ = ψ.toAlgHom ((scale K ^ n : K) • coordinate K (algebra K P n) t)
      rw [map_smul, ← hψ]
      exact congrArg (fun z => (scale K ^ n : K) • ψ.toAlgHom z)
        (coordinate_eq_algebraMap P n t).symm
  exact finite_of_monic_normalized_coordinates ψ c hc p hm hu hz'

/-- **Finite chart maps.** If `f` is module-finite, then for every original chart `n` of
`Spec(A)ᵃⁿ` the preimage of its range under the induced map is the range of a single chart
`S` of the saturated atlas of `Spec(B)ᵃⁿ`, and the bounded pullback of the saturated morphism
from the original chart `n` to `S` is finite in Berkovich's Banach sense. -/
theorem exists_isFiniteBanach_preimage (hf : f.toRingHom.Finite) (n : ChartIndex K P) :
    ∃ S : (saturated K Q).presentation.atlas.Index,
      ∃ h : (saturatedHom K P Q f).baseMap ''
          range ((saturated K Q).presentation.atlas.chart S) ⊆
          range ((saturated K P).presentation.atlas.chart
            ((presentation K P).atlas.originalSaturatedIndex n)),
        range ((saturated K Q).presentation.atlas.chart S) =
            baseMap K P Q f ⁻¹' range (chart K P n.val) ∧
          ((saturatedHom K P Q f).pullback S
            ((presentation K P).atlas.originalSaturatedIndex n) h).IsFiniteBanach := by
  classical
  choose q hq hz using fun k : Fin Q.arity => hf.to_isIntegral (Q.map (MvPolynomial.X k))
  obtain ⟨m, hmM⟩ := exists_radius_gt K (∑ k, ∑ j ∈ Finset.range ((q k).natDegree + 1),
    ‖PolynomialLocus.algebraMap P (polyradius K P.arity n.val) ((q k).coeff j)‖)
  have hC : ∀ k j, ‖PolynomialLocus.algebraMap P (polyradius K P.arity n.val)
      ((q k).coeff j)‖ ≤ radius K m := by
    intro k j
    rcases le_or_gt j (q k).natDegree with hj | hj
    · refine le_trans ?_ hmM.le
      refine le_trans ?_ (Finset.single_le_sum (fun k _ => Finset.sum_nonneg
        (fun j _ => norm_nonneg _)) (Finset.mem_univ k))
      exact Finset.single_le_sum (f := fun j =>
          ‖PolynomialLocus.algebraMap P (polyradius K P.arity n.val) ((q k).coeff j)‖)
        (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    · rw [coeff_eq_zero_of_natDegree_lt hj, map_zero, norm_zero]
      exact (radius_pos K m).le
  have hmrange : ∀ y, baseMap K P Q f y ∈ range (chart K P n.val) →
      y ∈ range (chart K Q m) := by
    intro y hy
    rw [mem_range_chart_iff]
    intro k
    exact (coordinateNorm_le_of_monic P Q f n.val k (q k) (hq k) (hz k) (hC k) y hy).trans
      (max_le (one_le_radius K m) le_rfl)
  let U₀ := preimageDomain P Q f m n.val
  have hlocus : U₀.locus = baseMap K P Q f ⁻¹' range (chart K P n.val) :=
    (preimageDomain_locus P Q f m n.val).trans (chart_image_eq_preimage P Q f m n.val hmrange)
  let S : (saturated K Q).presentation.atlas.Index := ⟨U₀.locus, ⟨U₀, rfl⟩⟩
  let T := (presentation K P).atlas.originalSaturatedIndex n
  have hS : range ((saturated K Q).presentation.atlas.chart S) = U₀.locus :=
    (presentation K Q).atlas.range_saturatedChart S
  have hT : range ((saturated K P).presentation.atlas.chart T) = range (chart K P n.val) :=
    (presentation K P).atlas.saturatedAtlas_original_range n
  have h : (saturatedHom K P Q f).baseMap ''
      range ((saturated K Q).presentation.atlas.chart S) ⊆
      range ((saturated K P).presentation.atlas.chart T) := by
    rw [hS, hT, hlocus, saturatedHom_baseMap]
    exact image_preimage_subset _ _
  refine ⟨S, h, hS.trans hlocus, ?_⟩
  -- the lift of `f` to the Weierstrass preimage domain is finite Banach
  obtain ⟨ψ, hψ⟩ := exists_preimageDomain_lift P Q f m n.val
  have hψfin : ψ.IsFiniteBanach :=
    isFiniteBanach_of_finite ψ (finite_of_preimageDomain_lift P Q f m n.val q hq hz hC ψ hψ)
  -- comparison of the two presentations of the same local domain
  let rS := (presentation K Q).atlas.saturatedRepresentative S
  have hrS : rS.locus = U₀.locus := (presentation K Q).atlas.saturatedRepresentative_locus S
  let ρ := (LocalDomain.Inclusion.ofSubset rS U₀ hrS.subset).restriction
  let ρ' := (LocalDomain.Inclusion.ofSubset U₀ rS hrS.symm.subset).restriction
  have hρρ' : ρ.comp ρ' = BoundedAlgHom.id K rS.algebra := by
    apply localDomain_hom_ext Q rS
    intro b
    rw [BoundedAlgHom.comp_apply,
      inclusion_localAlgebraMap Q (LocalDomain.Inclusion.ofSubset U₀ rS hrS.symm.subset) b,
      inclusion_localAlgebraMap Q (LocalDomain.Inclusion.ofSubset rS U₀ hrS.subset) b]
    rfl
  have hρ : ρ.IsFiniteBanach := by
    have hid := BoundedAlgHom.isFiniteBanach_id (K := K) (R := rS.algebra)
    exact ((congrArg BoundedAlgHom.IsFiniteBanach hρρ').mpr hid).of_comp
  -- the original target chart
  let rT := (presentation K P).atlas.saturatedRepresentative T
  obtain ⟨γ, hγ⟩ := exists_chart_lift P n.val rT.algebra (localAlgebraMap P rT) (fun x => by
    have hx : rT.ambientMap x ∈ rT.locus :=
      (LocalDomain.range_ambientMap rT).subset (mem_range_self x)
    have hx' : rT.ambientMap x ∈ range (chart K P n.val) :=
      ((presentation K P).atlas.saturatedRepresentative_locus T).subset hx
    exact (congrArg (· ∈ range (chart K P n.val)) (affinoidBaseMap_localAlgebraMap P rT x)).mpr
      hx')
  have hcomm : ((saturatedHom K P Q f).pullback S T h).comp γ = ρ.comp ψ := by
    apply chart_hom_ext P n.val
    intro a
    exact (congrArg ((saturatedHom K P Q f).pullback S T h) (hγ a)).trans
      ((saturatedHom_pullback_localAlgebraMap P Q f S T h a).trans
        ((inclusion_localAlgebraMap Q (LocalDomain.Inclusion.ofSubset rS U₀ hrS.subset)
          (f a)).symm.trans (congrArg ρ (hψ a).symm)))
  have hfin : (((saturatedHom K P Q f).pullback S T h).comp γ).IsFiniteBanach :=
    (congrArg BoundedAlgHom.IsFiniteBanach hcomm).mpr (hρ.comp hψfin)
  exact hfin.of_comp

end Finite

end Langlands.Analytic.AffineAnalytification.FiniteCharts
