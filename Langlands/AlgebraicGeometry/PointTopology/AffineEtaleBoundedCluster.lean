import Langlands.AlgebraicGeometry.PointTopology.UltrametricNewtonRoot
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Etale.Locus

/-!
# Bounded families of rational points of étale algebras cluster

Let `K` be a henselian ultrametric valued field and `R → A` an étale map of `K`-algebras.
A filter of `K`-points of `A` along which every element of `A` stays bounded, and whose
restrictions to `R` converge to a `K`-point of `R`, has a cluster point among the `K`-points
of `A` (for pointwise convergence). The proof covers `Spec A` by finitely many standard
étale opens, picks one on which the filter stays uniformly inside, and finds the limit
coordinate by the Newton root lemma.
-/

noncomputable section

open Polynomial Filter Topology

namespace Langlands.AlgebraicGeometry.PointTopology

namespace EtaleBoundedCluster

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- An étale algebra is covered by finitely many standard étale basic opens: there are
finitely many elements generating the unit ideal whose localizations are standard étale. -/
theorem exists_finset_isStandardEtale [Algebra.Etale R A] :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ f ∈ s, Algebra.IsStandardEtale R (Localization.Away f) := by
  classical
  let S : Set A := {f | Algebra.IsStandardEtale R (Localization.Away f)}
  have hS : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    have : Algebra.IsEtaleAt R Q :=
      Algebra.FormallyEtale.comp R A (Localization.AtPrime Q)
    obtain ⟨f, hfQ, hf⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
    exact hfQ (hle (Ideal.subset_span hf))
  obtain ⟨s, hsS, hs⟩ := (Ideal.span_eq_top_iff_finite S).mp hS
  exact ⟨s, hs, fun f hf => hsS hf⟩

section Analytic

variable {K : Type*} [NontriviallyNormedField K]

/-- Evaluation of a bivariate polynomial is continuous in its coefficient map and in the two
variables. -/
theorem tendsto_eval₂_eval₂ {ι : Type*} {l : Filter ι} (F : R[X][X]) (ψ : ι → R →+* K)
    (ψ₀ : R →+* K) (hψ : ∀ r, Tendsto (fun i => ψ i r) l (𝓝 (ψ₀ r))) {t u : ι → K} {t₀ u₀ : K}
    (ht : Tendsto t l (𝓝 t₀)) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun i => F.eval₂ (eval₂RingHom (ψ i) (t i)) (u i)) l
      (𝓝 (F.eval₂ (eval₂RingHom ψ₀ t₀) u₀)) := by
  simp only [eval₂_eq_sum_range]
  refine tendsto_finsetSum _ fun j _ => (Tendsto.mul ?_ (hu.pow j))
  simp only [coe_eval₂RingHom, eval₂_eq_sum_range]
  exact tendsto_finsetSum _ fun k _ => (hψ _).mul (ht.pow k)

/-- Evaluation of a polynomial is continuous in its coefficient map and its variable. -/
theorem tendsto_eval_map {ι : Type*} {l : Filter ι} (p : R[X]) (ψ : ι → R →+* K)
    (ψ₀ : R →+* K) (hψ : ∀ r, Tendsto (fun i => ψ i r) l (𝓝 (ψ₀ r))) {t : ι → K} {t₀ : K}
    (ht : Tendsto t l (𝓝 t₀)) :
    Tendsto (fun i => (p.map (ψ i)).eval (t i)) l (𝓝 ((p.map ψ₀).eval t₀)) := by
  simp only [eval_map, eval₂_eq_sum_range]
  exact tendsto_finsetSum _ fun k _ => (hψ _).mul (ht.pow k)

/-- If the coefficient maps converge and the variable stays bounded, the difference of the
evaluations tends to zero. -/
theorem tendsto_eval_map_sub {ι : Type*} {l : Filter ι} (p : R[X]) (ψ : ι → R →+* K)
    (ψ₀ : R →+* K) (hψ : ∀ r, Tendsto (fun i => ψ i r) l (𝓝 (ψ₀ r))) {t : ι → K} {B : ℝ}
    (ht : ∀ᶠ i in l, ‖t i‖ ≤ B) :
    Tendsto (fun i => (p.map (ψ i)).eval (t i) - (p.map ψ₀).eval (t i)) l (𝓝 0) := by
  have e : ∀ i, (p.map (ψ i)).eval (t i) - (p.map ψ₀).eval (t i) =
      ∑ k ∈ Finset.range (p.natDegree + 1), (ψ i (p.coeff k) - ψ₀ (p.coeff k)) * t i ^ k := by
    intro i
    rw [eval_map, eval_map, eval₂_eq_sum_range' (n := p.natDegree + 1) _ (Nat.lt_succ_self _),
      eval₂_eq_sum_range' (n := p.natDegree + 1) _ (Nat.lt_succ_self _),
      ← Finset.sum_sub_distrib]
    simp only [sub_mul]
  simp only [e]
  rw [show (0 : K) = ∑ k ∈ Finset.range (p.natDegree + 1), (0 : K) by simp]
  refine tendsto_finsetSum _ fun k _ => ?_
  refine Tendsto.zero_mul_isBoundedUnder_le ?_ ?_
  · simpa using (hψ (p.coeff k)).sub_const (ψ₀ (p.coeff k))
  · refine ⟨max 1 B ^ k, Filter.eventually_map.mpr ?_⟩
    filter_upwards [ht] with i hi
    simp only [Function.comp, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hi.trans (le_max_right 1 B)) k

/-- In an ultrametric field, a polynomial with coefficients bounded by `M₀` is bounded by
`M₀ max(1, B) ^ deg` on the ball of radius `B`. -/
theorem norm_eval_le_of_coeff [IsUltrametricDist K] (P : K[X]) {M₀ B : ℝ} (hM₀ : 0 ≤ M₀)
    (hP : ∀ n, ‖P.coeff n‖ ≤ M₀) {t : K} (ht : ‖t‖ ≤ B) :
    ‖P.eval t‖ ≤ M₀ * max 1 B ^ P.natDegree := by
  rw [eval_eq_sum_range]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro n hn
  rw [norm_mul, norm_pow]
  refine mul_le_mul (hP n) ?_ (by positivity) hM₀
  calc ‖t‖ ^ n ≤ max 1 B ^ n := pow_le_pow_left₀ (norm_nonneg _) (ht.trans (le_max_right _ _)) n
    _ ≤ max 1 B ^ P.natDegree :=
        pow_le_pow_right₀ (le_max_left _ _) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

/-- In an ultrametric field, the Taylor coefficients of `Q` at points of the ball of radius
`B` are bounded uniformly. -/
theorem norm_taylor_coeff_le [IsUltrametricDist K] (Q : K[X]) {M₀ B : ℝ} (hM₀ : 0 ≤ M₀)
    (hQ : ∀ n, ‖Q.coeff n‖ ≤ M₀) {t : K} (ht : ‖t‖ ≤ B) (k : ℕ) :
    ‖(taylor t Q).coeff k‖ ≤ M₀ * max 1 B ^ Q.natDegree := by
  rw [taylor_coeff]
  refine (norm_eval_le_of_coeff _ hM₀ (fun n => ?_) ht).trans ?_
  · rw [hasseDeriv_coeff, norm_mul]
    calc ‖(((n + k).choose k : ℕ) : K)‖ * ‖Q.coeff (n + k)‖ ≤ 1 * M₀ :=
          mul_le_mul (IsUltrametricDist.norm_natCast_le_one K _) (hQ _) (norm_nonneg _)
            zero_le_one
      _ = M₀ := one_mul M₀
  · gcongr
    · exact le_max_left _ _
    · exact (natDegree_hasseDeriv_le Q k).trans (Nat.sub_le _ _)

/-- If finitely many elements `f` generate the unit ideal and a family of evaluations keeps
every element bounded, then some `f` stays frequently bounded away from zero. -/
theorem exists_frequently_le_norm {α : Type*} (l : Filter α) [l.NeBot] (ev : α → A →+* K)
    (s : Finset A) (c : A → A) (hc : ∑ f ∈ s, c f * f = 1)
    (hbdd : ∀ b, ∃ C, ∀ᶠ x in l, ‖ev x b‖ ≤ C) :
    ∃ f ∈ s, ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ x in l, δ ≤ ‖ev x f‖ := by
  classical
  choose C hC using hbdd
  set D : ℝ := 1 + ∑ f ∈ s, |C (c f)| with hD
  have hD1 : 1 ≤ D := by
    have : 0 ≤ ∑ f ∈ s, |C (c f)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hDpos : 0 < D := by linarith
  have hcb : ∀ᶠ x in l, ∀ f ∈ s, ‖ev x (c f)‖ ≤ D := by
    rw [eventually_all_finset]
    intro f hf
    filter_upwards [hC (c f)] with x hx
    refine hx.trans ((le_abs_self _).trans ?_)
    have : |C (c f)| ≤ ∑ g ∈ s, |C (c g)| :=
      Finset.single_le_sum (f := fun g => |C (c g)|) (fun _ _ => abs_nonneg _) hf
    linarith
  set δ : ℝ := 1 / (D * (s.card + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  by_contra hne
  push Not at hne
  have hsmall : ∀ᶠ x in l, ∀ f ∈ s, ‖ev x f‖ < δ := by
    rw [eventually_all_finset]
    intro f hf
    simpa [not_le] using (hne f hf δ hδpos)
  obtain ⟨x, hx₁, hx₂⟩ := (hcb.and hsmall).exists
  have h1 : (1 : ℝ) = ‖ev x (∑ f ∈ s, c f * f)‖ := by rw [hc, map_one, norm_one]
  have h2 : ‖ev x (∑ f ∈ s, c f * f)‖ ≤ ∑ f ∈ s, D * δ := by
    rw [map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f hf => ?_)
    rw [map_mul, norm_mul]
    exact mul_le_mul (hx₁ f hf) (hx₂ f hf).le (norm_nonneg _) hDpos.le
  have h3 : ∑ f ∈ s, D * δ < 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hδ]
    rw [show (s.card : ℝ) * (D * (1 / (D * (s.card + 1)))) = s.card / (s.card + 1) by
      field_simp]
    rw [div_lt_one (by positivity)]
    linarith
  linarith

end Analytic

section Cluster

variable {K : Type*} [NontriviallyNormedField K] [Algebra K A]

/-- The evaluation of a `K`-point `φ` of `A` at elements of the localization `A[1/f]`,
defined when `φ f ≠ 0`. -/
def locLift (f : A) (φ : A →ₐ[K] K) (h : φ f ≠ 0) : Localization.Away f →+* K :=
  IsLocalization.Away.lift f (g := φ.toRingHom) (isUnit_iff_ne_zero.mpr h)

theorem locLift_algebraMap (f : A) (φ : A →ₐ[K] K) (h : φ f ≠ 0) (a : A) :
    locLift f φ h (algebraMap A _ a) = φ a :=
  IsLocalization.Away.lift_eq f _ a

theorem locLift_comp_algebraMap_R (f : A) (φ : A →ₐ[K] K) (h : φ f ≠ 0) :
    (locLift f φ h).comp (algebraMap R (Localization.Away f)) =
      φ.toRingHom.comp (algebraMap R A) := by
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply,
    IsScalarTower.algebraMap_apply R A (Localization.Away f), locLift_algebraMap]
  rfl

/-- Every element of `A[1/f]` times a power of `f` comes from `A`, compatibly with every
`K`-point. -/
theorem exists_mul_pow_eq (f : A) (y : Localization.Away f) :
    ∃ (a : A) (k : ℕ), ∀ (φ : A →ₐ[K] K) (h : φ f ≠ 0), locLift f φ h y * φ f ^ k = φ a := by
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers f) y
  refine ⟨a, k, fun φ h => ?_⟩
  have := congrArg (locLift f φ h) hy
  simp only [map_mul, locLift_algebraMap, map_pow] at this
  exact this

/-- `locLift` commutes with polynomial evaluation. -/
theorem locLift_aeval (f : A) (φ : A →ₐ[K] K) (h : φ f ≠ 0) (x : Localization.Away f)
    (p : R[X]) :
    locLift f φ h (aeval x p) = (p.map (φ.toRingHom.comp (algebraMap R A))).eval
      (locLift f φ h x) := by
  rw [aeval_def, hom_eval₂, locLift_comp_algebraMap_R, eval_map]

end Cluster

section Main

open scoped Bivariate

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable [Algebra K R] [Algebra K A] [IsScalarTower K R A]

/-- **Bounded families of points of étale algebras cluster.** Over a henselian ultrametric
field `K`, let `R → A` be étale. A nontrivial filter of `K`-points of `A` along which every
element of `A` stays bounded, and whose restrictions to `R` converge pointwise to a
`K`-point `ψ₀` of `R`, has a finer nontrivial filter converging pointwise to a `K`-point of
`A` restricting to `ψ₀`. -/
theorem exists_tendsto_of_bounded (hK : IsHenselianValuedField K) [Algebra.Etale R A]
    (l : Filter (A →ₐ[K] K)) [l.NeBot] (hbdd : ∀ a : A, ∃ C, ∀ᶠ φ in l, ‖φ a‖ ≤ C)
    (ψ₀ : R →ₐ[K] K)
    (hconv : ∀ r : R, Tendsto (fun φ : A →ₐ[K] K => φ (algebraMap R A r)) l (𝓝 (ψ₀ r))) :
    ∃ φ₀ : A →ₐ[K] K, (∀ r, φ₀ (algebraMap R A r) = ψ₀ r) ∧
      ∃ l' : Filter (A →ₐ[K] K), l' ≤ l ∧ l'.NeBot ∧
        ∀ a, Tendsto (fun φ : A →ₐ[K] K => φ a) l' (𝓝 (φ₀ a)) := by
  classical
  obtain ⟨s, hs, hstd⟩ := exists_finset_isStandardEtale (R := R) (A := A)
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp
    (show (1 : A) ∈ Ideal.span (s : Set A) by rw [hs]; trivial)
  have hc' : ∑ f ∈ s, c f * f = 1 := by simpa [smul_eq_mul] using hc
  obtain ⟨f, hfs, δ, hδ, hfreq⟩ :=
    exists_frequently_le_norm l (fun φ => φ.toRingHom) s c hc' hbdd
  have := hstd f hfs
  obtain ⟨P⟩ : Nonempty (StandardEtalePresentation R (Localization.Away f)) :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation
  let ψ : (A →ₐ[K] K) → R →+* K := fun φ => φ.toRingHom.comp (algebraMap R A)
  let t : (A →ₐ[K] K) → K := fun φ => if h : φ f ≠ 0 then locLift f φ h P.x else 0
  let gv : (A →ₐ[K] K) → K := fun φ => (P.g.map (ψ φ)).eval (t φ)
  set l₁ := l ⊓ 𝓟 {φ : A →ₐ[K] K | δ ≤ ‖φ f‖} with hl₁def
  have hl₁ : l₁.NeBot := Filter.frequently_iff_neBot.mp hfreq
  have hl₁l : l₁ ≤ l := inf_le_left
  have hδ₁ : ∀ᶠ φ in l₁, δ ≤ ‖φ f‖ := Filter.mem_inf_of_right (Filter.mem_principal_self _)
  have hne₁ : ∀ᶠ φ in l₁, φ f ≠ 0 := hδ₁.mono fun φ hφ =>
    norm_pos_iff.mp (hδ.trans_le hφ)
  have hψ₁ : ∀ r, Tendsto (fun φ => ψ φ r) l₁ (𝓝 (ψ₀ r)) := fun r => (hconv r).mono_left hl₁l
  have hbdd₁ : ∀ a : A, ∃ C, 0 ≤ C ∧ ∀ᶠ φ in l₁, ‖φ a‖ ≤ C := fun a => by
    obtain ⟨C, hC⟩ := hbdd a
    exact ⟨max C 0, le_max_right _ _, (hC.filter_mono hl₁l).mono fun φ h => h.trans
      (le_max_left _ _)⟩
  -- the coordinate stays bounded
  obtain ⟨ax, kx, hx⟩ := exists_mul_pow_eq (K := K) f P.x
  obtain ⟨Cx, hCx0, hCx⟩ := hbdd₁ ax
  set B : ℝ := Cx / δ ^ kx with hB
  have ht_eq : ∀ φ (h : φ f ≠ 0), t φ = locLift f φ h P.x := fun φ h => by simp [t, h]
  have htB : ∀ᶠ φ in l₁, ‖t φ‖ ≤ B := by
    filter_upwards [hδ₁, hne₁, hCx] with φ hδφ hφ hCφ
    rw [ht_eq φ hφ, hB, le_div_iff₀ (by positivity)]
    have e := congrArg norm (hx φ hφ)
    rw [norm_mul, norm_pow] at e
    calc ‖locLift f φ hφ P.x‖ * δ ^ kx ≤ ‖locLift f φ hφ P.x‖ * ‖φ f‖ ^ kx := by gcongr
      _ = ‖φ ax‖ := e
      _ ≤ Cx := hCφ
  -- the coordinate is a root of the specialized polynomial
  have hroot : ∀ φ (h : φ f ≠ 0), (P.f.map (ψ φ)).eval (t φ) = 0 := fun φ h => by
    rw [ht_eq φ h, ← locLift_aeval, P.hasMap.1, map_zero]
  have hgv : ∀ φ (h : φ f ≠ 0), gv φ = locLift f φ h (aeval P.x P.g) := fun φ h => by
    simp only [gv]
    rw [ht_eq φ h, ← locLift_aeval]
  -- the value of `g` stays away from zero
  obtain ⟨u, hu⟩ : ∃ u : Localization.Away f, u * aeval P.x P.g = 1 :=
    ⟨↑(P.hasMap.2.unit⁻¹), P.hasMap.2.val_inv_mul⟩
  obtain ⟨bu, ku, hbu⟩ := exists_mul_pow_eq (K := K) f u
  obtain ⟨Cu, hCu0, hCu⟩ := hbdd₁ bu
  set γ : ℝ := δ ^ ku / (Cu + 1) with hγ
  have hγpos : 0 < γ := by positivity
  have hgvγ : ∀ᶠ φ in l₁, γ ≤ ‖gv φ‖ := by
    filter_upwards [hδ₁, hne₁, hCu] with φ hδφ hφ hCφ
    have h1 : locLift f φ hφ u * gv φ = 1 := by
      rw [hgv φ hφ, ← map_mul, hu, map_one]
    have h2 := hbu φ hφ
    have hu0 : locLift f φ hφ u ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have e : gv φ * φ bu = φ f ^ ku := by
      rw [← h2, ← mul_assoc, mul_comm (gv φ), h1, one_mul]
    have e' := congrArg norm e
    rw [norm_mul, norm_pow] at e'
    rw [hγ, div_le_iff₀ (by positivity)]
    calc δ ^ ku ≤ ‖φ f‖ ^ ku := by gcongr
      _ = ‖gv φ‖ * ‖φ bu‖ := e'.symm
      _ ≤ ‖gv φ‖ * (Cu + 1) := by gcongr; linarith
  -- the derivative stays away from zero
  obtain ⟨p₁, p₂, n, hcond⟩ := P.cond
  obtain ⟨M₁, hM₁0, hM₁⟩ : ∃ M₁ : ℝ, 0 < M₁ ∧
      ∀ᶠ φ in l₁, ∀ i, ‖(p₁.map (ψ φ)).coeff i‖ ≤ M₁ := by
    refine ⟨1 + ∑ i ∈ Finset.range (p₁.natDegree + 1), ‖ψ₀ (p₁.coeff i)‖, by positivity, ?_⟩
    have hev : ∀ᶠ φ in l₁, ∀ i ∈ Finset.range (p₁.natDegree + 1),
        ‖ψ φ (p₁.coeff i)‖ ≤ ‖ψ₀ (p₁.coeff i)‖ + 1 := by
      rw [eventually_all_finset]
      intro i _
      exact ((hψ₁ _).norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h => h.le
    filter_upwards [hev] with φ hφ i
    rw [coeff_map]
    by_cases hi : i ∈ Finset.range (p₁.natDegree + 1)
    · refine (hφ i hi).trans ?_
      have := Finset.single_le_sum (f := fun j => ‖ψ₀ (p₁.coeff j)‖)
        (fun _ _ => norm_nonneg _) hi
      linarith
    · rw [coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hi), map_zero,
        norm_zero]
      positivity
  set Bm : ℝ := max 1 B with hBm
  set η : ℝ := γ ^ n / (M₁ * Bm ^ p₁.natDegree) with hη
  have hBm0 : 0 < Bm := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hηpos : 0 < η := by positivity
  have hderη : ∀ᶠ φ in l₁, η ≤ ‖(P.f.map (ψ φ)).derivative.eval (t φ)‖ := by
    filter_upwards [hne₁, htB, hgvγ, hM₁] with φ hφ htφ hgφ hMφ
    have e : (P.f.map (ψ φ)).derivative.eval (t φ) * (p₁.map (ψ φ)).eval (t φ) =
        gv φ ^ n := by
      have := congrArg (fun q => (q.map (ψ φ)).eval (t φ)) hcond
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, eval_add,
        eval_mul, eval_pow, ← derivative_map, hroot φ hφ, zero_mul, add_zero] at this
      exact this
    have hp₁ : ‖(p₁.map (ψ φ)).eval (t φ)‖ ≤ M₁ * Bm ^ p₁.natDegree := by
      refine (norm_eval_le_of_coeff _ hM₁0.le hMφ htφ).trans ?_
      gcongr
      · exact le_max_left _ _
      · exact natDegree_map_le
    have e' := congrArg norm e
    rw [norm_mul, norm_pow] at e'
    rw [hη, div_le_iff₀ (by positivity)]
    calc γ ^ n ≤ ‖gv φ‖ ^ n := pow_le_pow_left₀ hγpos.le hgφ n
      _ = _ := e'.symm
      _ ≤ ‖(P.f.map (ψ φ)).derivative.eval (t φ)‖ * (M₁ * Bm ^ p₁.natDegree) := by gcongr
  -- the limiting polynomial
  set Qlim : K[X] := P.f.map ψ₀.toRingHom with hQlim
  have hQlim0 : Tendsto (fun φ => Qlim.eval (t φ)) l₁ (𝓝 0) := by
    have h := tendsto_eval_map_sub P.f ψ ψ₀.toRingHom hψ₁ htB
    have h' : Tendsto (fun φ => -Qlim.eval (t φ)) l₁ (𝓝 0) :=
      h.congr' (hne₁.mono fun φ hφ => by simp only [hroot φ hφ, zero_sub, Qlim])
    simpa using h'.neg
  have hQlimd : Tendsto (fun φ => (P.f.map (ψ φ)).derivative.eval (t φ) -
      Qlim.derivative.eval (t φ)) l₁ (𝓝 0) := by
    simpa only [derivative_map, Qlim] using
      tendsto_eval_map_sub (derivative P.f) ψ ψ₀.toRingHom hψ₁ htB
  have hderη2 : ∀ᶠ φ in l₁, η / 2 ≤ ‖Qlim.derivative.eval (t φ)‖ := by
    filter_upwards [hderη, (tendsto_zero_iff_norm_tendsto_zero.mp hQlimd).eventually
      (gt_mem_nhds (half_pos hηpos))] with φ h₁ h₂
    have := norm_sub_norm_le ((P.f.map (ψ φ)).derivative.eval (t φ))
      (Qlim.derivative.eval (t φ))
    linarith
  obtain ⟨M₀, hM₀0, hM₀⟩ : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ i, ‖Qlim.coeff i‖ ≤ M₀ :=
    ⟨∑ i ∈ Finset.range (Qlim.natDegree + 1), ‖Qlim.coeff i‖, by positivity, fun i => by
      by_cases hi : i ∈ Finset.range (Qlim.natDegree + 1)
      · exact Finset.single_le_sum (f := fun j => ‖Qlim.coeff j‖) (fun _ _ => norm_nonneg _) hi
      · rw [coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hi), norm_zero]
        positivity⟩
  set MT : ℝ := M₀ * Bm ^ Qlim.natDegree with hMT
  have hMT0 : 0 ≤ MT := by positivity
  set κ : ℝ := min (η / 2) ((η / 2) ^ 2 / (MT + 1)) with hκ
  have hκpos : 0 < κ := lt_min (half_pos hηpos) (by positivity)
  have hsmallQ : ∀ᶠ φ in l₁, ‖Qlim.eval (t φ)‖ < κ :=
    (tendsto_zero_iff_norm_tendsto_zero.mp hQlim0).eventually (gt_mem_nhds hκpos)
  have hnewton : ∀ᶠ φ in l₁, ∃ τ : K, Qlim.eval τ = 0 ∧
      ‖τ - t φ‖ ≤ ‖Qlim.eval (t φ)‖ / (η / 2) := by
    filter_upwards [htB, hderη2, hsmallQ] with φ htφ hdφ hsφ
    have hx0 : 0 ≤ ‖Qlim.eval (t φ)‖ := norm_nonneg _
    obtain ⟨τ, hτ, hτn⟩ := exists_root_of_isHenselianValuedField hK Qlim (t φ) (M := MT)
      (fun k _ => norm_taylor_coeff_le Qlim hM₀0 hM₀ htφ k)
      ((hsφ.le.trans (min_le_left _ _)).trans hdφ)
      (by
        have h1 : ‖Qlim.eval (t φ)‖ < (η / 2) ^ 2 / (MT + 1) := hsφ.trans_le (min_le_right _ _)
        have h2 : (MT + 1) * ‖Qlim.eval (t φ)‖ < (η / 2) ^ 2 := by
          rwa [lt_div_iff₀ (by positivity), mul_comm] at h1
        have h3 : (η / 2) ^ 2 ≤ ‖Qlim.derivative.eval (t φ)‖ ^ 2 :=
          pow_le_pow_left₀ (half_pos hηpos).le hdφ 2
        nlinarith)
    exact ⟨τ, hτ, hτn.trans (div_le_div_of_nonneg_left hx0 (half_pos hηpos) hdφ)⟩
  -- a root of the limit polynomial attracts the coordinates frequently
  have hQlimne : Qlim ≠ 0 := (P.monic_f.map _).ne_zero
  set Z := Qlim.roots.toFinset with hZdef
  set ε : (A →ₐ[K] K) → ℝ := fun φ => ‖Qlim.eval (t φ)‖ / (η / 2) with hεdef
  have hZ : ∀ᶠ φ in l₁, ∃ τ ∈ Z, ‖τ - t φ‖ ≤ ε φ :=
    hnewton.mono fun φ ⟨τ, hτ, hτn⟩ =>
      ⟨τ, Multiset.mem_toFinset.mpr ((mem_roots hQlimne).mpr hτ), hτn⟩
  obtain ⟨τ, hτZ, hτfreq⟩ : ∃ τ ∈ Z, ∃ᶠ φ in l₁, ‖τ - t φ‖ ≤ ε φ := by
    by_contra hcon
    have hcon' : ∀ᶠ φ in l₁, ∀ τ ∈ Z, ¬ ‖τ - t φ‖ ≤ ε φ := by
      rw [eventually_all_finset]
      exact fun τ hτ => Filter.not_frequently.mp fun h => hcon ⟨τ, hτ, h⟩
    obtain ⟨φ, ⟨τ, hτ, hle⟩, hφ⟩ := (hZ.and hcon').exists
    exact hφ τ hτ hle
  set l₂ := l₁ ⊓ 𝓟 {φ : A →ₐ[K] K | ‖τ - t φ‖ ≤ ε φ} with hl₂def
  have hl₂ : l₂.NeBot := Filter.frequently_iff_neBot.mp hτfreq
  have hl₂l₁ : l₂ ≤ l₁ := inf_le_left
  have hτle : ∀ᶠ φ in l₂, ‖τ - t φ‖ ≤ ε φ :=
    Filter.mem_inf_of_right (Filter.mem_principal_self _)
  have hε0 : Tendsto ε l₂ (𝓝 0) := by
    have := ((tendsto_zero_iff_norm_tendsto_zero.mp hQlim0).div_const (η / 2)).mono_left hl₂l₁
    simpa [ε] using this
  have ht_tend : Tendsto t l₂ (𝓝 τ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (hτle.mono fun φ h => ?_) hε0
    rw [norm_sub_rev]
    exact h
  have hψ₂ : ∀ r, Tendsto (fun φ => ψ φ r) l₂ (𝓝 (ψ₀ r)) :=
    fun r => (hψ₁ r).mono_left hl₂l₁
  have hgv_tend : Tendsto gv l₂ (𝓝 ((P.g.map ψ₀.toRingHom).eval τ)) :=
    tendsto_eval_map P.g ψ ψ₀.toRingHom hψ₂ ht_tend
  have hgτ : (P.g.map ψ₀.toRingHom).eval τ ≠ 0 := by
    have := ge_of_tendsto hgv_tend.norm (hgvγ.filter_mono hl₂l₁)
    exact norm_pos_iff.mp (hγpos.trans_le this)
  have hτroot : Qlim.eval τ = 0 := (mem_roots hQlimne).mp (Multiset.mem_toFinset.mp hτZ)
  -- the limit point
  set gτ := (P.g.map ψ₀.toRingHom).eval τ with hgτdef
  let ρ₀ : R[X][X] →+* K := eval₂RingHom (eval₂RingHom ψ₀.toRingHom τ) gτ⁻¹
  have hρ₀C : ∀ r : R, ρ₀ (C (C r)) = ψ₀ r := fun r => by
    simp [ρ₀]
  have hρ₀I : ∀ z ∈ Ideal.span {C P.f, Y * C P.g - 1}, ρ₀ z = 0 := by
    intro z hz
    refine (Ideal.span_le (I := RingHom.ker ρ₀)).mpr ?_ hz
    rw [Set.pair_subset_iff]
    constructor
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      simp only [ρ₀, coe_eval₂RingHom, eval₂_C]
      rw [← eval_map]
      exact hτroot
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      simp only [ρ₀, coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_X, eval₂_C, eval₂_one]
      rw [← eval_map, ← hgτdef, inv_mul_cancel₀ hgτ, sub_self]
  let ρ₀' : P.Ring →+* K := Ideal.Quotient.lift _ ρ₀ hρ₀I
  let φ₀r : A →+* K := ρ₀'.comp
    (P.equivRing.toRingEquiv.toRingHom.comp (algebraMap A (Localization.Away f)))
  have hφ₀R : ∀ r : R, φ₀r (algebraMap R A r) = ψ₀ r := by
    intro r
    change ρ₀' (P.equivRing (algebraMap A (Localization.Away f) (algebraMap R A r))) = _
    rw [← IsScalarTower.algebraMap_apply R A (Localization.Away f), AlgEquiv.commutes]
    change ρ₀ (C (C r)) = ψ₀ r
    exact hρ₀C r
  let φ₀ : A →ₐ[K] K :=
    { φ₀r with
      commutes' := fun c => by
        change φ₀r (algebraMap K A c) = algebraMap K K c
        rw [IsScalarTower.algebraMap_apply K R A c, hφ₀R]
        exact ψ₀.commutes c }
  refine ⟨φ₀, hφ₀R, l₂, hl₂l₁.trans hl₁l, hl₂, fun a => ?_⟩
  obtain ⟨F, hF⟩ :=
    Ideal.Quotient.mk_surjective (P.equivRing (algebraMap A (Localization.Away f) a))
  have hφ₀a : φ₀ a = F.eval₂ (eval₂RingHom ψ₀.toRingHom τ) gτ⁻¹ := by
    change ρ₀' (P.equivRing (algebraMap A (Localization.Away f) a)) = _
    exact (congrArg ρ₀' hF.symm).trans rfl
  let mkP : R[X][X] →+* P.Ring := Ideal.Quotient.mk _
  have hF' : mkP F = P.equivRing (algebraMap A (Localization.Away f) a) := hF
  have hz : mkP (Y * C P.g - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hφa : ∀ φ (h : φ f ≠ 0), φ a = F.eval₂ (eval₂RingHom (ψ φ) (t φ)) (gv φ)⁻¹ := by
    intro φ h
    let θ : R[X][X] →+* K := (locLift f φ h).comp
      (P.equivRing.symm.toRingEquiv.toRingHom.comp mkP)
    have hθC : θ.comp C = eval₂RingHom (ψ φ) (t φ) := by
      refine Polynomial.ringHom_ext' (RingHom.ext fun r => ?_) ?_
      · change locLift f φ h (P.equivRing.symm (mkP (C (C r)))) =
          eval₂ (ψ φ) (t φ) (C r)
        rw [eval₂_C, show mkP (C (C r)) = algebraMap R P.Ring r from rfl, AlgEquiv.commutes]
        exact RingHom.congr_fun (locLift_comp_algebraMap_R f φ h) r
      · change locLift f φ h (P.equivRing.symm P.X) = eval₂ (ψ φ) (t φ) X
        rw [StandardEtalePresentation.equivRing_symm_X, eval₂_X, ht_eq φ h]
    have hθX : θ X = (gv φ)⁻¹ := by
      have hrel : θ (Y * C P.g - 1) = 0 := by
        simp only [θ, RingHom.comp_apply]
        rw [hz, map_zero, map_zero]
      have hg : θ (C P.g) = gv φ := by
        rw [← RingHom.comp_apply θ C, hθC, coe_eval₂RingHom, ← eval_map]
      rw [map_sub, map_mul, map_one, sub_eq_zero, hg] at hrel
      exact eq_inv_of_mul_eq_one_left hrel
    have hθ : θ = eval₂RingHom (eval₂RingHom (ψ φ) (t φ)) (gv φ)⁻¹ :=
      Polynomial.ringHom_ext' (by rw [hθC]; ext <;> simp) (by rw [hθX]; simp)
    calc φ a = locLift f φ h (algebraMap A _ a) := (locLift_algebraMap f φ h a).symm
      _ = θ F := by
          change _ = locLift f φ h (P.equivRing.symm (mkP F))
          rw [hF', AlgEquiv.symm_apply_apply]
      _ = _ := by rw [hθ]; rfl
  rw [hφ₀a]
  refine (tendsto_eval₂_eval₂ F ψ ψ₀.toRingHom hψ₂ ht_tend (hgv_tend.inv₀ hgτ)).congr' ?_
  filter_upwards [hne₁.filter_mono hl₂l₁] with φ hφ
  exact (hφa φ hφ).symm

end Main

end EtaleBoundedCluster

end Langlands.AlgebraicGeometry.PointTopology
