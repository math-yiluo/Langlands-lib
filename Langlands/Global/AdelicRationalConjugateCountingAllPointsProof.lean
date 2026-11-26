import Langlands.Analysis.DiscreteProductSubgroupCounting
import Langlands.Global.AdelicRationalConjugateCountingAllPointsStatement

/-! # Rational points in adelic conjugates of compact sets, at every adelic point -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory NumberField Filter MeasureTheory Metric Set Topology
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Global

namespace RationalConjugateCountingAllPoints

section Packing

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A set of points mapped into a ball of radius `R` with images pairwise at distance at least
`2ε` is finite, with at most `((R + ε) / ε)^dim` elements. -/
theorem finite_and_ncard_le_of_separated {α : Type v} (P : Set α) (f : α → E)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hs : ∀ i ∈ P, ‖f i‖ ≤ R)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ε + ε ≤ dist (f i) (f j)) :
    P.Finite ∧ (P.ncard : ℝ) ≤ ((R + ε) / ε) ^ Module.finrank ℝ E := by
  have key : ∀ s : Finset α, (s : Set α) ⊆ P →
      (s.card : ℝ) ≤ ((R + ε) / ε) ^ Module.finrank ℝ E := fun s hsP =>
    Langlands.Analysis.card_le_of_separated_centres s f hR hε (fun i hi => hs i (hsP hi))
      (fun i hi j hj hij => hsep i (hsP hi) j (hsP hj) hij)
  have hfin : P.Finite := by
    by_contra hinf
    obtain ⟨s, hsP, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (⌈((R + ε) / ε) ^ Module.finrank ℝ E⌉₊ + 1)
    have h := key s hsP
    rw [hcard] at h
    push_cast at h
    linarith [Nat.le_ceil (((R + ε) / ε) ^ Module.finrank ℝ E)]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card P hfin]
  exact key _ (by simp)

end Packing

section ProductFormula

variable (F : Type u) [Field F] [NumberField F]

/-- Product formula: if the finite norms of a nonzero `a ∈ F` have product at most `t⁻¹`, with
`0 < t ≤ 1`, then some archimedean norm of `a` is at least `t`. -/
theorem le_pi_norm_infinite {a : F} (ha : a ≠ 0) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hfin : ∏ᶠ v : FinitePlace F, ‖(algebraMap F (Adeles F) a).2 v‖ ≤ t⁻¹) :
    t ≤ ‖((fun w => (algebraMap F (Adeles F) a).1 w) :
      (w : InfinitePlace F) → w.Completion)‖ := by
  set x : (w : InfinitePlace F) → w.Completion := fun w => (algebraMap F (Adeles F) a).1 w
    with hx
  set N0 : ℝ := |((Algebra.norm ℚ a : ℚ) : ℝ)| with hN0
  have hN0pos : 0 < N0 := by
    rw [hN0, abs_pos]
    exact_mod_cast (Algebra.norm_ne_zero_iff).mpr ha
  have hinf : ∏ w : InfinitePlace F, ‖x w‖ ^ w.mult = N0 := by
    have h := InfiniteAdeleRing.coe_norm_eq_abs_norm (K := F) a
    rw [InfiniteAdeleRing.norm_def] at h
    calc ∏ w : InfinitePlace F, ‖x w‖ ^ w.mult
        = ∏ v : InfinitePlace F, ‖(algebraMap F (InfiniteAdeleRing F) a) v‖ ^ v.mult := rfl
      _ = _ := h
      _ = N0 := by rw [hN0, Rat.cast_abs]
  have hunit : IsUnit (algebraMap F (FiniteAdeles F) a) := (IsUnit.mk0 a ha).map _
  have hfinprod : ∏ᶠ v : FinitePlace F, ‖(algebraMap F (Adeles F) a).2 v‖ = N0⁻¹ := by
    have h := FiniteAdeleRing.coe_norm_eq_inv_abs_norm (K := F) ha
    rw [FiniteAdeleRing.norm_eq_finprod_of_isUnit hunit] at h
    have h' : ∏ᶠ v : FinitePlace F, ‖(algebraMap F (Adeles F) a).2 v‖ =
        ∏ᶠ v : FinitePlace F, ‖(algebraMap F (FiniteAdeles F) a) v‖ := rfl
    rw [h', h, hN0, Rat.cast_inv, Rat.cast_abs]
  have htN : t ≤ N0 := by
    rw [hfinprod] at hfin
    exact (inv_le_inv₀ hN0pos ht).mp hfin
  by_contra hlt
  push Not at hlt
  have hx1 : ‖x‖ ≤ 1 := hlt.le.trans ht1
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hsum : 1 ≤ ∑ w : InfinitePlace F, w.mult :=
    (Nat.one_le_iff_ne_zero.mpr (InfinitePlace.mult_pos (w := w₀)).ne').trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ w₀))
  have hle : ∏ w : InfinitePlace F, ‖x w‖ ^ w.mult ≤ ‖x‖ := calc
    ∏ w : InfinitePlace F, ‖x w‖ ^ w.mult ≤ ∏ w : InfinitePlace F, ‖x‖ ^ w.mult :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity)
          (fun w _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x w) _)
    _ = ‖x‖ ^ (∑ w : InfinitePlace F, w.mult) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ ‖x‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hx1 hsum
    _ = ‖x‖ := pow_one _
  linarith

end ProductFormula

end RationalConjugateCountingAllPoints

open RationalConjugateCountingAllPoints MatrixInverseHeight AdelicMatrixHeight in
/-- Mœglin–Waldspurger I.2.4, Lemma (a)(i) with `y = x`: the rational points of `x C x⁻¹` number
at most a fixed power of the height of `x`, for every adelic point `x`. -/
theorem adelicRationalConjugateCountingAllPoints :
    AdelicRationalConjugateCountingAllPointsStatement.{u} := by
  classical
  intro F _ _ G _ n rho hn hrho
  choose normedSpace finiteDimensional using
    fun w : InfinitePlace F => exists_normedSpace_real_infiniteCompletion w
  let (w : InfinitePlace F) : NormedSpace ℝ w.Completion := normedSpace w
  let (w : InfinitePlace F) : FiniteDimensional ℝ w.Completion := finiteDimensional w
  let m := Module.finrank ℝ (Fin n → Fin n → (w : InfinitePlace F) → w.Completion)
  refine ⟨6 * m, fun C hC => ?_⟩
  obtain ⟨b, hb⟩ := hC.bddAbove_image
    (RepresentationGrowth.continuous_adelicHeight F G rho hn).continuousOn
  set L : ℝ := max 1 b with hLdef
  have hL : 1 ≤ L := le_max_left _ _
  refine ⟨3 ^ m * L ^ (3 * m), by positivity, fun x => ?_⟩
  intro P
  set H := RepresentationGrowth.adelicHeight F G rho x with hHdef
  have hH : 1 ≤ H := RepresentationGrowth.one_le_adelicHeight F G rho hn x
  set R : ℝ := L * H ^ 2 with hRdef
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le hL (one_le_pow₀ hH)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  let Mx : AdelicGroupPoints F G → AdelicGL F n := RepresentationGrowth.adelicMatrix F G rho
  let p : AdelicGroupPoints F G → (Fin n → Fin n → (w : InfinitePlace F) → w.Completion) :=
    fun γ i j w => (Mx γ i j).1 w
  have hheight : ∀ γ ∈ P, height F n (Mx γ) ≤ R := by
    rintro _ ⟨-, y, hy, rfl⟩
    change RepresentationGrowth.adelicHeight F G rho (x * y * x⁻¹) ≤ R
    calc RepresentationGrowth.adelicHeight F G rho (x * y * x⁻¹)
        ≤ RepresentationGrowth.adelicHeight F G rho (x * y) * H := by
          simpa only [RepresentationGrowth.adelicHeight_inv, H] using
            RepresentationGrowth.adelicHeight_mul_le F G rho hn (x * y) x⁻¹
      _ ≤ (H * RepresentationGrowth.adelicHeight F G rho y) * H :=
          mul_le_mul_of_nonneg_right (RepresentationGrowth.adelicHeight_mul_le F G rho hn x y)
            (zero_le_one.trans hH)
      _ ≤ (H * L) * H := by
          have hy' := (hb ⟨y, hy, rfl⟩).trans (le_max_right 1 b)
          gcongr
      _ = R := by rw [hRdef]; ring
  have hrat : ∀ γ ∈ P, ∃ Q : RationalGL F n, Mx γ = AdelicGL.rational F n Q := by
    rintro _ ⟨⟨r, rfl⟩, -⟩
    refine ⟨GeneralLinearGroupPoints.rationalEquiv F n
      (G.affinePointsTarget rho (CommAlgCat.of F F) r), ?_⟩
    have eq := DFunLike.congr_fun (AdelicGroupPoints.rational_naturality F G rho) r
    change AdelicGroupPoints.rational F _
      (G.affinePointsTarget rho (CommAlgCat.of F F) r) =
        G.affinePointsTarget rho (CommAlgCat.of F (Adeles F))
          (AdelicGroupPoints.rational F G r) at eq
    change GeneralLinearGroupPoints.adelicHomeomorph F n
      (G.affinePointsTarget rho (CommAlgCat.of F (Adeles F))
        (AdelicGroupPoints.rational F G r)) = _
    rw [← eq]
    exact GeneralLinearGroupPoints.adelicHomeomorph_rational F n _
  have hnorm : ∀ γ ∈ P, ‖p γ‖ ≤ R := fun γ hγ => by
    have hb' := sublevel_subset F hn R (hheight γ hγ)
    exact (pi_norm_le_iff_of_nonneg hR0).mpr fun i =>
      (pi_norm_le_iff_of_nonneg hR0).mpr fun j =>
        (pi_norm_le_iff_of_nonneg hR0).mpr fun w => (hb'.1 i j).1 w
  have hfinR : ∀ γ ∈ P, ∏ᶠ v : FinitePlace F, finiteLocal F n (Mx γ) v ≤ R := fun γ hγ => by
    have hA : 1 ≤ ∏ w : InfinitePlace F, ((n : ℝ) * infiniteLocal F n (Mx γ) w) ^ w.mult :=
      Finset.one_le_prod₀ fun w _ =>
        one_le_pow₀ (one_le_nat_mul_localMaximum (infiniteProjection F w) hn (Mx γ))
    have hFp : 1 ≤ ∏ᶠ v : FinitePlace F, finiteLocal F n (Mx γ) v :=
      one_le_finprod (one_le_finiteLocal F n hn (Mx γ))
    exact (le_mul_of_one_le_left (zero_le_one.trans hFp) hA).trans (hheight γ hγ)
  set ε : ℝ := (R * R)⁻¹ / 2 with hεdef
  have hRR : 1 ≤ R * R := one_le_mul_of_one_le_of_one_le hR hR
  have hε : 0 < ε := by positivity
  have hsep : ∀ γ ∈ P, ∀ γ' ∈ P, γ ≠ γ' → ε + ε ≤ dist (p γ) (p γ') := by
    intro γ hγ γ' hγ' hne
    rw [hεdef, add_halves]
    obtain ⟨Q, hQ⟩ := hrat γ hγ
    obtain ⟨Q', hQ'⟩ := hrat γ' hγ'
    have hQne : Q ≠ Q' := by
      rintro rfl
      exact hne ((RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
        (hQ.trans hQ'.symm))
    obtain ⟨i, j, hij⟩ : ∃ i j, Q i j ≠ Q' i j := by
      by_contra h
      push Not at h
      exact hQne (Units.ext (Matrix.ext h))
    have hc : Q i j - Q' i j ≠ 0 := sub_ne_zero.mpr hij
    have hentry : Mx γ i j = algebraMap F (Adeles F) (Q i j) := by rw [hQ]; rfl
    have hentry' : Mx γ' i j = algebraMap F (Adeles F) (Q' i j) := by rw [hQ']; rfl
    have hunit : IsUnit (algebraMap F (FiniteAdeles F) (Q i j - Q' i j)) :=
      (IsUnit.mk0 _ hc).map _
    have hsupp : (fun v : FinitePlace F =>
        ‖(algebraMap F (Adeles F) (Q i j - Q' i j)).2 v‖).HasFiniteMulSupport := by
      have h := FiniteAdeleRing.hasFiniteMulSupport_norm hunit.unit
      simp only [IsUnit.unit_spec] at h
      exact h
    have hcfin : ∏ᶠ v : FinitePlace F,
        ‖(algebraMap F (Adeles F) (Q i j - Q' i j)).2 v‖ ≤ ((R * R)⁻¹)⁻¹ := by
      rw [inv_inv]
      calc ∏ᶠ v : FinitePlace F, ‖(algebraMap F (Adeles F) (Q i j - Q' i j)).2 v‖
          ≤ ∏ᶠ v : FinitePlace F, (finiteLocal F n (Mx γ) v * finiteLocal F n (Mx γ') v) := by
            refine finprod_le_finprod₀ hsupp (fun _ => norm_nonneg _)
              ((hasFiniteMulSupport_finiteLocal F n hn _).mul
                (hasFiniteMulSupport_finiteLocal F n hn _)) fun v => ?_
            have e1 := entry_le_localMaximum (finiteProjection F v) (Mx γ) i j
            have e2 := entry_le_localMaximum (finiteProjection F v) (Mx γ') i j
            have h1 := one_le_finiteLocal F n hn (Mx γ) v
            have h2 := one_le_finiteLocal F n hn (Mx γ') v
            change ‖finiteProjection F v (Mx γ i j)‖ ≤ finiteLocal F n (Mx γ) v at e1
            change ‖finiteProjection F v (Mx γ' i j)‖ ≤ finiteLocal F n (Mx γ') v at e2
            rw [hentry] at e1
            rw [hentry'] at e2
            have hsub : (algebraMap F (Adeles F) (Q i j - Q' i j)).2 v =
                finiteProjection F v (algebraMap F (Adeles F) (Q i j)) +
                  -finiteProjection F v (algebraMap F (Adeles F) (Q' i j)) := by
              rw [← sub_eq_add_neg, ← map_sub, ← map_sub]
              rfl
            show ‖(algebraMap F (Adeles F) (Q i j - Q' i j)).2 v‖ ≤ _
            rw [hsub]
            refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
            rw [norm_neg]
            exact max_le (e1.trans (le_mul_of_one_le_right (zero_le_one.trans h1) h2))
              (e2.trans (le_mul_of_one_le_left (zero_le_one.trans h2) h1))
        _ = (∏ᶠ v : FinitePlace F, finiteLocal F n (Mx γ) v) *
              ∏ᶠ v : FinitePlace F, finiteLocal F n (Mx γ') v :=
            finprod_mul_distrib (hasFiniteMulSupport_finiteLocal F n hn _)
              (hasFiniteMulSupport_finiteLocal F n hn _)
        _ ≤ R * R := mul_le_mul (hfinR γ hγ) (hfinR γ' hγ')
              (finprod_nonneg fun v => zero_le_one.trans (one_le_finiteLocal F n hn _ v)) hR0
    have ht := le_pi_norm_infinite F hc (inv_pos.mpr (by positivity))
      (inv_le_one_of_one_le₀ hRR) hcfin
    have hcomp : ((fun w => (algebraMap F (Adeles F) (Q i j - Q' i j)).1 w) :
        (w : InfinitePlace F) → w.Completion) = (p γ - p γ') i j := by
      funext w
      simp only [p, Pi.sub_apply, hentry, hentry', map_sub]
      rfl
    rw [hcomp] at ht
    calc (R * R)⁻¹ ≤ ‖(p γ - p γ') i j‖ := ht
      _ ≤ ‖(p γ - p γ') i‖ := norm_le_pi_norm ((p γ - p γ') i) j
      _ ≤ ‖p γ - p γ'‖ := norm_le_pi_norm (p γ - p γ') i
      _ = dist (p γ) (p γ') := (dist_eq_norm _ _).symm
  obtain ⟨hPfin, hPcard⟩ := finite_and_ncard_le_of_separated P p hR0 hε hnorm hsep
  refine ⟨hPfin, hPcard.trans ?_⟩
  have hεR : ε ≤ R / 2 := by
    rw [hεdef]
    have : (R * R)⁻¹ ≤ R := (inv_le_one_of_one_le₀ hRR).trans hR
    linarith
  have hkey : 3 * R ^ 3 * ε = 3 * R / 2 := by
    rw [hεdef]
    field_simp
  have hratio : (R + ε) / ε ≤ 3 * R ^ 3 := by
    rw [div_le_iff₀ hε, hkey]
    linarith
  calc ((R + ε) / ε) ^ m ≤ (3 * R ^ 3) ^ m := pow_le_pow_left₀ (by positivity) hratio m
    _ = 3 ^ m * L ^ (3 * m) * H ^ (6 * m) := by rw [hRdef]; ring

end Langlands.Global
