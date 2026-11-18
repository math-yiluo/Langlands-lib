import Langlands.Geometry.Analytic.TruncatedComparisonFlatness
import Langlands.Geometry.Analytic.TateShearPolynomial
import Langlands.Geometry.Analytic.DistinguishedNormalization
import Langlands.Geometry.Analytic.WeierstrassQuotient
import Langlands.Geometry.Analytic.TateNoetherian
import Langlands.Geometry.Analytic.ClosedIdealsBanach
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Flatness of polynomial algebras in strict Tate algebras -/

noncomputable section

universe u v

namespace Langlands.Analytic.TatePolynomialFlatness

open TruncatedComparison

section Quotient

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A membership criterion for bijectivity of an induced quotient map. -/
theorem quotientMap_bijective_of_forall (f : R →+* S) {I : Ideal S} {J : Ideal R}
    (h : J ≤ I.comap f) (hinj : ∀ r, f r ∈ I → r ∈ J) (hsurj : ∀ s, ∃ r, s - f r ∈ I) :
    Function.Bijective (Ideal.quotientMap I f h) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hinj r hx)
  · intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := hsurj s
    refine ⟨Ideal.Quotient.mk J r, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, ← neg_sub]
    exact I.neg_mem hr

/-- Bijectivity of an induced quotient map only depends on the target ideal. -/
theorem quotientMap_bijective_congr (f : R →+* S) {I I' : Ideal S} {J : Ideal R}
    (hI : I = I') {h : J ≤ I.comap f} {h' : J ≤ I'.comap f}
    (hb : Function.Bijective (Ideal.quotientMap I f h)) :
    Function.Bijective (Ideal.quotientMap I' f h') := by
  subst hI
  exact hb

end Quotient

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Nullstellensatz

omit [CompleteSpace K] in
/-- A strict Tate algebra in at least one variable is not a field: its first
coordinate is nonzero and has constant coefficient zero. -/
theorem not_isField_succ (m : ℕ) : ¬ IsField (StrictTateAlgebra (Fin (m + 1)) K) := by
  intro hF
  have hX : StrictTateAlgebra.X (Fin (m + 1)) K 0 ≠ 0 := by
    intro h
    have h1 := StrictTateAlgebra.norm_X (Fin (m + 1)) K 0
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨v, hv⟩ := hF.mul_inv_cancel hX
  have h := congrArg (fun f : StrictTateAlgebra (Fin (m + 1)) K =>
    MvPowerSeries.constantCoeff f.val) hv
  change MvPowerSeries.constantCoeff (MvPowerSeries.X 0 * v.val) =
    MvPowerSeries.constantCoeff (1 : MvPowerSeries (Fin (m + 1)) K) at h
  simp at h

/-- Nullstellensatz for strict Tate algebras: the residue field at a maximal
ideal is finite over `K`. The proof applies Noether normalization to the
quotient, which is a field, and observes that the Noether normalization must
have zero variables. -/
theorem finite_quotient_of_isMaximal {N : ℕ} (𝔪 : Ideal (StrictTateAlgebra (Fin N) K))
    [h𝔪 : 𝔪.IsMaximal] : Module.Finite K (StrictTateAlgebra (Fin N) K ⧸ 𝔪) := by
  let Q : PresentedStrictAffinoidAlgebra K :=
    ⟨N, 𝔪, isClosed_ideal_of_noetherian_banach (K := K) 𝔪⟩
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr h𝔪.ne_top
  obtain ⟨m, -, g, hginj, hgfin⟩ := PresentedStrictAffinoidAlgebra.exists_noetherNormalization Q
  have hfield : IsField Q := (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔪).mp h𝔪
  let _ : Algebra (StrictTateAlgebra (Fin m) K) Q := g.toAlgHom.toRingHom.toAlgebra
  have : Module.Finite (StrictTateAlgebra (Fin m) K) Q := hgfin
  have : Algebra.IsIntegral (StrictTateAlgebra (Fin m) K) Q := Algebra.IsIntegral.of_finite _ _
  have hmfield : IsField (StrictTateAlgebra (Fin m) K) :=
    isField_of_isIntegral_of_isField (fun a b hab => hginj hab) hfield
  obtain rfl : m = 0 := by
    cases m with
    | zero => rfl
    | succ m => exact absurd hmfield (not_isField_succ m)
  have h1 : (algebraMap K (StrictTateAlgebra (Fin 0) K)).Finite :=
    RingHom.Finite.of_surjective _ StrictTateAlgebra.zeroVariables_algebraMap_surjective
  have h2 := RingHom.Finite.comp hgfin h1
  have h3 : g.toAlgHom.toRingHom.comp (algebraMap K (StrictTateAlgebra (Fin 0) K)) =
      algebraMap K Q :=
    RingHom.ext fun a => g.toAlgHom.commutes a
  rw [h3, RingHom.finite_algebraMap] at h2
  exact h2

end Nullstellensatz

section Step

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Over a normed field, a nonzero polynomial has a last coefficient of maximal norm. -/
theorem exists_last_max_coeff (p : Polynomial K) (hp : p ≠ 0) :
    ∃ d, p.coeff d ≠ 0 ∧ (∀ k, ‖p.coeff k‖ ≤ ‖p.coeff d‖) ∧
      ∀ k, d < k → ‖p.coeff k‖ < ‖p.coeff d‖ := by
  classical
  have hne : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  set M := p.support.sup' hne (fun k => ‖p.coeff k‖) with hM
  have hle : ∀ k, ‖p.coeff k‖ ≤ M := by
    intro k
    by_cases hk : k ∈ p.support
    · exact Finset.le_sup' (fun k => ‖p.coeff k‖) hk
    · rw [Polynomial.notMem_support_iff.mp hk, norm_zero]
      obtain ⟨j, hj⟩ := hne
      exact (norm_nonneg _).trans (Finset.le_sup' (fun k => ‖p.coeff k‖) hj)
  obtain ⟨j, hj, hjM⟩ := Finset.exists_mem_eq_sup' hne (fun k => ‖p.coeff k‖)
  let T := p.support.filter (fun k => ‖p.coeff k‖ = M)
  have hT : T.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, hjM.symm⟩⟩
  have hd : T.max' hT ∈ T := T.max'_mem hT
  obtain ⟨hdsupp, hdM⟩ := Finset.mem_filter.mp hd
  refine ⟨T.max' hT, Polynomial.mem_support_iff.mp hdsupp,
    fun k => (hle k).trans_eq hdM.symm, ?_⟩
  intro k hk
  rw [hdM]
  refine lt_of_le_of_ne (hle k) ?_
  intro hkM
  by_cases hks : k ∈ p.support
  · have hkT : k ∈ T := Finset.mem_filter.mpr ⟨hks, hkM⟩
    exact absurd (T.le_max' k hkT) (not_le.mpr hk)
  · rw [Polynomial.notMem_support_iff.mp hks, norm_zero] at hkM
    exact Polynomial.mem_support_iff.mp hdsupp (norm_eq_zero.mp (hdM.trans hkM.symm))

variable (n : ℕ)

omit [CompleteSpace K] in
/-- The image of a scalar polynomial with a last coefficient of maximal norm is
distinguished. -/
theorem isDistinguished_ofPolynomial_map (p : Polynomial K) {d : ℕ} (hd0 : p.coeff d ≠ 0)
    (hle : ∀ k, ‖p.coeff k‖ ≤ ‖p.coeff d‖) (hlt : ∀ k, d < k → ‖p.coeff k‖ < ‖p.coeff d‖) :
    RestrictedSeries.IsDistinguished (RestrictedSeries.ofPolynomial (StrictTateAlgebra (Fin n) K)
      (p.map (algebraMap K (StrictTateAlgebra (Fin n) K)))) d := by
  have hc : ∀ k, RestrictedSeries.coeff (StrictTateAlgebra (Fin n) K) k
      (RestrictedSeries.ofPolynomial _ (p.map (algebraMap K (StrictTateAlgebra (Fin n) K)))) =
        algebraMap K (StrictTateAlgebra (Fin n) K) (p.coeff k) := by
    intro k
    rw [RestrictedSeries.coeff_ofPolynomial, Polynomial.coeff_map]
  have hn : ∀ k, ‖RestrictedSeries.coeff (StrictTateAlgebra (Fin n) K) k
      (RestrictedSeries.ofPolynomial _ (p.map (algebraMap K (StrictTateAlgebra (Fin n) K))))‖ =
        ‖p.coeff k‖ := by
    intro k
    rw [hc, StrictTateAlgebra.norm_algebraMap]
  refine ⟨?_, fun k => ?_, fun k hk => ?_⟩
  · rw [hc]
    exact (isUnit_iff_ne_zero.mpr hd0).map _
  · rw [hn, hn]
    exact hle k
  · rw [hn, hn]
    exact hlt k hk

/-- Every maximal ideal of `A⟨X⟩` (with `A` a strict Tate algebra) contains the
image of a monic polynomial over `A` with coefficients in the unit ball. -/
theorem exists_monic_mem (𝔪 : Ideal (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)))
    [𝔪.IsMaximal] :
    ∃ w : Polynomial (StrictTateAlgebra (Fin n) K), w.Monic ∧ (∀ k, ‖w.coeff k‖ ≤ 1) ∧
      RestrictedSeries.ofPolynomial _ w ∈ 𝔪 := by
  let e := StrictTateAlgebra.regroupEquiv (A := K) n
  let φ : StrictTateAlgebra (Fin (n + 1)) K →+*
      RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K) := e.toRingHom
  let 𝔪' : Ideal (StrictTateAlgebra (Fin (n + 1)) K) := 𝔪.comap φ
  have : 𝔪'.IsMaximal := Ideal.comap_isMaximal_of_surjective φ e.surjective
  have := finite_quotient_of_isMaximal 𝔪'
  obtain ⟨p, hpmon, hp⟩ := Algebra.IsIntegral.isIntegral (R := K)
    (Ideal.Quotient.mk 𝔪' (StrictTateAlgebra.X (Fin (n + 1)) K 0))
  have hmem : Polynomial.aeval (StrictTateAlgebra.X (Fin (n + 1)) K 0) p ∈ 𝔪' := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk K,
      ← Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Polynomial.aeval_def]
    exact hp
  have h1 : φ.comp (algebraMap K (StrictTateAlgebra (Fin (n + 1)) K)) =
      (algebraMap (StrictTateAlgebra (Fin n) K)
        (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K))).comp
        (algebraMap K (StrictTateAlgebra (Fin n) K)) :=
    RingHom.ext fun a => StrictTateAlgebra.regroup_algebraMap n a
  have h2 : φ (StrictTateAlgebra.X (Fin (n + 1)) K 0) =
      RestrictedSeries.ofPolynomial _ Polynomial.X :=
    StrictTateAlgebra.regroup_X_zero n
  have he : φ (Polynomial.aeval (StrictTateAlgebra.X (Fin (n + 1)) K 0) p) =
      RestrictedSeries.ofPolynomial _ (p.map (algebraMap K (StrictTateAlgebra (Fin n) K))) := by
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, h1, h2, ← Polynomial.eval₂_map,
      ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left_apply]
  have hf𝔪 : RestrictedSeries.ofPolynomial _ (p.map (algebraMap K (StrictTateAlgebra (Fin n) K)))
      ∈ 𝔪 := by
    rw [← he]
    exact hmem
  obtain ⟨d, hd0, hle, hlt⟩ := exists_last_max_coeff p hpmon.ne_zero
  obtain ⟨ew, ⟨hfac, hwmon, -, hwunit⟩, -⟩ :=
    RestrictedSeries.existsUnique_distinguished_preparation _ d
      (isDistinguished_ofPolynomial_map n p hd0 hle hlt)
  refine ⟨ew.2, hwmon, hwunit, ?_⟩
  have hw : RestrictedSeries.ofPolynomial _ ew.2 =
      ((ew.1⁻¹ : (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K))ˣ) :
        RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)) *
        RestrictedSeries.ofPolynomial _ (p.map (algebraMap K (StrictTateAlgebra (Fin n) K))) := by
    rw [hfac, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hw]
  exact 𝔪.mul_mem_left _ hf𝔪

omit [CompleteSpace K] in
/-- Powers of a polynomial with coefficients in the unit ball have coefficients
in the unit ball. -/
theorem pow_coeff_le (w : Polynomial (StrictTateAlgebra (Fin n) K))
    (hw : ∀ k, ‖w.coeff k‖ ≤ 1) (k : ℕ) : ∀ j, ‖(w ^ k).coeff j‖ ≤ 1 := by
  have h1 : ‖RestrictedSeries.ofPolynomial _ w‖ ≤ 1 := by
    apply (RestrictedSeries.norm_le_iff _ _ zero_le_one).mpr
    intro j
    rw [RestrictedSeries.coeff_ofPolynomial]
    exact hw j
  have h2 : ‖RestrictedSeries.ofPolynomial _ (w ^ k)‖ ≤ 1 := by
    rw [map_pow]
    exact (norm_pow_le _ k).trans (pow_le_one₀ (norm_nonneg _) h1)
  intro j
  have h3 := (RestrictedSeries.norm_le_iff _ _ zero_le_one).mp h2 j
  rwa [RestrictedSeries.coeff_ofPolynomial] at h3

/-- Every restricted series is congruent to a polynomial modulo a monic
polynomial with coefficients in the unit ball. -/
theorem exists_sub_mem_span (w : Polynomial (StrictTateAlgebra (Fin n) K)) (hw : w.Monic)
    (hunit : ∀ k, ‖w.coeff k‖ ≤ 1)
    (g : RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)) :
    ∃ r, g - RestrictedSeries.ofPolynomial _ r ∈
      Ideal.span {RestrictedSeries.ofPolynomial _ w} := by
  obtain ⟨x, hx⟩ :=
    RestrictedSeries.weierstrassQuotientMap_surjective w hw hunit (Ideal.Quotient.mk _ g)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨r, ?_⟩
  have hx' : Ideal.Quotient.mk (Ideal.span {RestrictedSeries.ofPolynomial _ w})
      (RestrictedSeries.ofPolynomial _ r) = Ideal.Quotient.mk _ g := hx
  exact Ideal.Quotient.eq.mp hx'.symm

/-- The polynomial inclusion `A[X] → A⟨X⟩` over a strict Tate algebra
`A = K⟨T₁, …, Tₙ⟩` is flat. -/
theorem flat_ofPolynomial :
    (RestrictedSeries.ofPolynomial (StrictTateAlgebra (Fin n) K)).toRingHom.Flat := by
  let _ : Algebra (Polynomial (StrictTateAlgebra (Fin n) K))
      (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)) :=
    (RestrictedSeries.ofPolynomial _).toRingHom.toAlgebra
  have : IsNoetherianRing (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)) :=
    isNoetherianRing_of_ringEquiv _ (StrictTateAlgebra.regroupEquiv (A := K) n)
  show Module.Flat (Polynomial (StrictTateAlgebra (Fin n) K))
    (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K))
  apply flat_of_forall_maximal
  intro 𝔪 h𝔪
  obtain ⟨w, hwmon, hwunit, hw𝔪⟩ := exists_monic_mem n 𝔪
  let f := algebraMap (Polynomial (StrictTateAlgebra (Fin n) K))
    (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K))
  let 𝔫 := 𝔪.comap f
  have hw𝔫 : w ∈ 𝔫 := hw𝔪
  have hspan : ∀ k : ℕ, (Ideal.span {w ^ k}).map f =
      Ideal.span {RestrictedSeries.ofPolynomial _ (w ^ k)} := by
    intro k
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hmap : 𝔫.map f = 𝔪 := by
    apply le_antisymm Ideal.map_comap_le
    intro b hb
    obtain ⟨r, hr⟩ := exists_sub_mem_span n w hwmon hwunit b
    have hle : Ideal.span {RestrictedSeries.ofPolynomial _ w} ≤ 𝔫.map f := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem f hw𝔫
    have hr𝔪 : f r ∈ 𝔪 := by
      have h1 : b - f r ∈ 𝔪 := (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hw𝔪)) hr
      have h2 := 𝔪.sub_mem hb h1
      rwa [sub_sub_cancel] at h2
    have hb' : b = (b - f r) + f r := by ring
    rw [hb']
    exact Ideal.add_mem _ (hle hr) (Ideal.mem_map_of_mem f hr𝔪)
  have hbij : ∀ k : ℕ, Function.Bijective
      (Ideal.quotientMap (𝔪 ^ k) f (pow_le_comap_pow (𝔫 := 𝔫) le_rfl k)) := by
    intro k
    have hJ : Function.Bijective
        (Ideal.quotientMap ((Ideal.span {w ^ k}).map f) f Ideal.le_comap_map) := by
      apply quotientMap_bijective_of_forall
      · intro r hr
        rw [hspan] at hr
        exact (RestrictedSeries.ofPolynomial_mem_span_iff (w ^ k) (hwmon.pow k)
          (pow_coeff_le n w hwunit k) r).mp hr
      · intro s
        obtain ⟨r, hr⟩ := exists_sub_mem_span n (w ^ k) (hwmon.pow k)
          (pow_coeff_le n w hwunit k) s
        refine ⟨r, ?_⟩
        rw [hspan]
        exact hr
    have hle : Ideal.span {w ^ k} ≤ 𝔫 ^ k := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.pow_mem_pow hw𝔫 k
    have h2 := quotientMap_bijective_of_le hle hJ
    exact quotientMap_bijective_congr f (by rw [Ideal.map_pow, hmap]) h2
  exact flat_localization (𝔫 := 𝔫) le_rfl hbij

end Step

section Induction

/-- The polynomial map `K[T₁, …, Tₙ] → K⟨T₁, …, Tₙ⟩`. -/
def polynomialMap (n : ℕ) : MvPolynomial (Fin n) K →ₐ[K] StrictTateAlgebra (Fin n) K :=
  MvPolynomial.aeval (StrictTateAlgebra.X (Fin n) K)

omit [CompleteSpace K] in
/-- With no variables, the polynomial map is bijective: both sides are the constants. -/
theorem polynomialMap_zero_bijective : Function.Bijective (polynomialMap (K := K) 0) := by
  constructor
  · intro p q hpq
    obtain ⟨a, rfl⟩ := MvPolynomial.C_surjective (R := K) (Fin 0) p
    obtain ⟨b, rfl⟩ := MvPolynomial.C_surjective (R := K) (Fin 0) q
    simp only [polynomialMap, MvPolynomial.aeval_C] at hpq
    rw [(algebraMap K (StrictTateAlgebra (Fin 0) K)).injective hpq]
  · intro f
    obtain ⟨a, rfl⟩ := StrictTateAlgebra.zeroVariables_algebraMap_surjective f
    exact ⟨MvPolynomial.C a, by simp only [polynomialMap, MvPolynomial.aeval_C]⟩

omit [CompleteSpace K] in
/-- After regrouping the first variable, the polynomial map in `n + 1`
variables is the polynomial map in `n` variables applied coefficientwise,
followed by the inclusion of polynomials into restricted series. -/
theorem regroup_comp_polynomialMap (n : ℕ) :
    (StrictTateAlgebra.regroupEquiv (A := K) n).toRingHom.comp
        (polynomialMap (K := K) (n + 1)).toRingHom =
      (RestrictedSeries.ofPolynomial (StrictTateAlgebra (Fin n) K)).toRingHom.comp
        ((Polynomial.mapRingHom (polynomialMap (K := K) n).toRingHom).comp
          (MvPolynomial.finSuccEquiv K n).toRingEquiv.toRingHom) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    have hL : (StrictTateAlgebra.regroupEquiv (A := K) n).toRingHom
        ((polynomialMap (K := K) (n + 1)).toRingHom (MvPolynomial.C a)) =
          algebraMap (StrictTateAlgebra (Fin n) K)
            (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K))
            (algebraMap K (StrictTateAlgebra (Fin n) K) a) := by
      change StrictTateAlgebra.regroup (polynomialMap (K := K) (n + 1) (MvPolynomial.C a)) = _
      rw [polynomialMap, MvPolynomial.aeval_C]
      exact StrictTateAlgebra.regroup_algebraMap n a
    have hfs : MvPolynomial.finSuccEquiv K n (MvPolynomial.C a) =
        Polynomial.C (MvPolynomial.C a) := by
      simp [MvPolynomial.finSuccEquiv_apply]
    rw [RingHom.comp_apply, hL, RingHom.comp_apply, RingHom.comp_apply]
    change _ = RestrictedSeries.ofPolynomial _
      (Polynomial.map (polynomialMap (K := K) n).toRingHom
        (MvPolynomial.finSuccEquiv K n (MvPolynomial.C a)))
    rw [hfs, Polynomial.map_C]
    change _ = RestrictedSeries.ofPolynomial _
      (Polynomial.C (polynomialMap (K := K) n (MvPolynomial.C a)))
    rw [polynomialMap, MvPolynomial.aeval_C]
    exact ((RestrictedSeries.ofPolynomial _).commutes _).symm
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
      change StrictTateAlgebra.regroupEquiv (A := K) n
          (MvPolynomial.aeval (StrictTateAlgebra.X (Fin (n + 1)) K) (MvPolynomial.X 0)) =
        RestrictedSeries.ofPolynomial _ (Polynomial.map (polynomialMap (K := K) n).toRingHom
          (MvPolynomial.finSuccEquiv K n (MvPolynomial.X 0)))
      rw [MvPolynomial.aeval_X, MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
      exact StrictTateAlgebra.regroup_X_zero n
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
      change StrictTateAlgebra.regroupEquiv (A := K) n
          (MvPolynomial.aeval (StrictTateAlgebra.X (Fin (n + 1)) K) (MvPolynomial.X j.succ)) =
        RestrictedSeries.ofPolynomial _ (Polynomial.map (polynomialMap (K := K) n).toRingHom
          (MvPolynomial.finSuccEquiv K n (MvPolynomial.X j.succ)))
      rw [MvPolynomial.aeval_X, MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
      change _ = RestrictedSeries.ofPolynomial _
        (Polynomial.C (MvPolynomial.aeval (StrictTateAlgebra.X (Fin n) K) (MvPolynomial.X j)))
      rw [MvPolynomial.aeval_X, StrictTateAlgebra.regroup_X_succ n j]
      exact ((RestrictedSeries.ofPolynomial _).commutes _).symm

attribute [local instance] Polynomial.algebra in
/-- Flatness is preserved by passing to polynomial rings in one variable. -/
theorem flat_mapRingHom {R S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : φ.Flat) : (Polynomial.mapRingHom φ).Flat := by
  let _ : Algebra R S := φ.toAlgebra
  exact RingHom.Flat.isStableUnderBaseChange R S (Polynomial R) (Polynomial S) hφ

/-- The polynomial map `K[T₁, …, Tₙ] → K⟨T₁, …, Tₙ⟩` is flat. -/
theorem flat_polynomialMap (n : ℕ) : (polynomialMap (K := K) n).toRingHom.Flat := by
  induction n with
  | zero => exact RingHom.Flat.of_bijective polynomialMap_zero_bijective
  | succ n ih =>
    have hcomp := ((RingHom.Flat.of_bijective
      (f := (MvPolynomial.finSuccEquiv K n).toRingEquiv.toRingHom)
      (MvPolynomial.finSuccEquiv K n).bijective).comp
        (flat_mapRingHom _ ih)).comp (flat_ofPolynomial n)
    rw [← regroup_comp_polynomialMap] at hcomp
    exact (RingHom.Flat.comp_iff_of_bijective_left
      (StrictTateAlgebra.regroupEquiv (A := K) n).bijective).mp hcomp

end Induction

end Langlands.Analytic.TatePolynomialFlatness
