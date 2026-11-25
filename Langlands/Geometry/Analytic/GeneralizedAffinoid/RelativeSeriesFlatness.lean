import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedSubmodules
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesComparison
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Completeness
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.RingHom.Flat

/-! # Flatness of relative series and of one-variable rational quotients -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Every vector of a finitely generated submodule of a finite free module over
a general presented affinoid is a combination of the given generators with
coefficients bounded by a fixed multiple of its norm. The bound is obtained
over a nontrivially valued strict extension field by the open mapping theorem
and brought back by the bounded coefficient retraction. -/
theorem exists_bounded_span_coefficients (A : PresentedAffinoidAlgebra K) {k q : ℕ}
    (n : Fin q → Fin k → A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ Submodule.span A (Set.range n),
      ∃ a : Fin q → A, v = ∑ t, a t • n t ∧ ∀ t, ‖a t‖ ≤ C * ‖v‖ := by
  let τ : Fin A.arity ⊕ Unit → ℝ := Sum.elim A.polyradius (fun _ => 2)
  obtain ⟨R⟩ := FiniteRadiusRealization.nonempty (K := K) τ (by
    intro j
    cases j with
    | inl j => exact A.polyradius.positive j
    | inr j => norm_num [τ])
  let : NontriviallyNormedField R.L :=
    { (inferInstance : NormedField R.L) with
      non_trivial := ⟨R.c (.inr ()), by rw [R.norm_c]; norm_num [τ]⟩ }
  let c : Fin A.arity → R.L := fun j => R.c (.inl j)
  have hc : ∀ j, ‖c j‖ = A.polyradius j := fun j => R.norm_c (.inl j)
  let φ := strictBaseChangeHom A R.ι R.norm_ι hc
  let ρ := strictBaseChangeRetraction A R.ι R.norm_ι hc R.π R.π_ι_mul R.bound_pos.le
    R.norm_π_le
  let F : (Fin k → A) → (Fin k → strictBaseChange A R.ι R.norm_ι hc) :=
    fun v j => φ (v j)
  let N : Submodule (strictBaseChange A R.ι R.norm_ι hc)
      (Fin k → strictBaseChange A R.ι R.norm_ι hc) :=
    Submodule.span _ (Set.range fun t => F (n t))
  have hN : IsClosed (N : Set (Fin k → strictBaseChange A R.ι R.norm_ι hc)) :=
    isClosed_submodule_pi_of_noetherian_banach (K := R.L) N
  have : CompleteSpace N := hN.completeSpace_coe
  let b : Fin q → N := fun t => ⟨F (n t), Submodule.subset_span ⟨t, rfl⟩⟩
  let l : (Fin q → strictBaseChange A R.ι R.norm_ι hc) →ₗ[strictBaseChange A R.ι R.norm_ι hc] N :=
    Fintype.linearCombination _ b
  have hl : Function.Surjective l := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
    refine ⟨a, Subtype.ext ?_⟩
    subst ha
    rw [Fintype.linearCombination_apply]
    simp [b]
  have hlc : Continuous l := by
    change Continuous (fun a : Fin q → strictBaseChange A R.ι R.norm_ι hc => ∑ t, a t • b t)
    exact continuous_finsetSum _ fun t _ => (continuous_apply t).smul continuous_const
  let L' : (Fin q → strictBaseChange A R.ι R.norm_ι hc) →L[R.L] N :=
    { l.restrictScalars R.L with cont := hlc }
  obtain ⟨D, hD, hpre⟩ := L'.exists_preimage_norm_le hl
  refine ⟨R.bound * D, mul_nonneg R.bound_pos.le hD.le, ?_⟩
  intro v hv
  have hFv : F v ∈ N := by
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact Submodule.subset_span ⟨t, rfl⟩
    | zero =>
      have : F 0 = 0 := by funext j; simp [F]
      rw [this]
      exact N.zero_mem
    | add x y _ _ hx hy =>
      have : F (x + y) = F x + F y := by funext j; simp [F]
      rw [this]
      exact N.add_mem hx hy
    | smul a x _ hx =>
      have : F (a • x) = φ a • F x := by funext j; simp [F]
      rw [this]
      exact N.smul_mem _ hx
  obtain ⟨β, hβ, hβn⟩ := hpre ⟨F v, hFv⟩
  have hβ' : ∑ t, β t • F (n t) = F v := by
    have h := congrArg Subtype.val hβ
    change ((Fintype.linearCombination _ b β : N) : Fin k → _) = F v at h
    rw [Fintype.linearCombination_apply] at h
    simpa [b] using h
  have hρφ : ∀ a : A, ρ (φ a) = a := fun a =>
    strictBaseChangeRetraction_strictBaseChangeHom A R.ι R.norm_ι hc R.π R.π_ι_mul
      R.bound_pos.le R.norm_π_le R.π_one a
  have hρmul : ∀ (a : A) (x : strictBaseChange A R.ι R.norm_ι hc), ρ (φ a * x) = a * ρ x :=
    fun a x => strictBaseChangeRetraction_strictBaseChangeHom_mul A R.ι R.norm_ι hc R.π
      R.π_ι_mul R.bound_pos.le R.norm_π_le a x
  refine ⟨fun t => ρ (β t), ?_, ?_⟩
  · funext j
    have hj := congrFun hβ' j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, F] at hj
    calc v j = ρ (φ (v j)) := (hρφ _).symm
      _ = ρ (∑ t, β t * φ (n t j)) := by rw [hj]
      _ = ∑ t, ρ (β t * φ (n t j)) := map_sum ρ _ _
      _ = ∑ t, n t j * ρ (β t) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [mul_comm, hρmul]
      _ = (∑ t, ρ (β t) • n t) j := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  · intro t
    have hFn : ‖(⟨F v, hFv⟩ : N)‖ ≤ ‖v‖ := by
      change ‖F v‖ ≤ ‖v‖
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun j => ?_
      exact (norm_strictBaseChangeHom_le A R.ι R.norm_ι hc (v j)).trans (norm_le_pi_norm v j)
    calc ‖ρ (β t)‖ ≤ R.bound * ‖β t‖ :=
          norm_strictBaseChangeRetraction_le A R.ι R.norm_ι hc R.π R.π_ι_mul
            R.bound_pos.le R.norm_π_le (β t)
      _ ≤ R.bound * ‖β‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm β t) R.bound_pos.le
      _ ≤ R.bound * (D * ‖v‖) := mul_le_mul_of_nonneg_left
          (hβn.trans (mul_le_mul_of_nonneg_left hFn hD.le)) R.bound_pos.le
      _ = R.bound * D * ‖v‖ := (mul_assoc _ _ _).symm


open Filter Topology in
/-- If, degree by degree, the coefficient vectors of finitely many relative
series lie in a finitely generated submodule of `Aᵏ`, then the series are
combinations of the generators with coefficients in the relative series ring. -/
theorem exists_series_span_lift (A : PresentedAffinoidAlgebra K) {σ : Type v}
    (s : PositivePolyradius σ) {k q : ℕ} (n : Fin q → Fin k → A)
    (x : Fin k → GeneralizedTateAlgebra s A)
    (hx : ∀ d, (fun i => MvPowerSeries.coeff d (series s A (x i))) ∈
      Submodule.span A (Set.range n)) :
    ∃ y : Fin q → GeneralizedTateAlgebra s A, ∀ i, x i = ∑ t, n t i • y t := by
  obtain ⟨C, hC, hBL⟩ := exists_bounded_span_coefficients A n
  choose a ha hab using fun d => hBL _ (hx d)
  have hres : ∀ t, MvPowerSeries.IsRestricted s (fun d => a d t : MvPowerSeries σ A) := by
    intro t
    have hsum : Tendsto (fun d : σ →₀ ℕ =>
        C * ∑ i, ‖MvPowerSeries.coeff d (series s A (x i))‖ * s.weight d) cofinite (𝓝 0) := by
      have h := tendsto_finsetSum (Finset.univ : Finset (Fin k))
        (fun i _ => isRestricted_series s A (x i))
      simpa [PositivePolyradius.weight] using h.const_mul C
    refine squeeze_zero (fun d => ?_) (fun d => ?_) hsum
    · exact mul_nonneg (norm_nonneg _) (s.weight_pos d).le
    · change ‖a d t‖ * s.weight d ≤ _
      have hv : ‖(fun i => MvPowerSeries.coeff d (series s A (x i)))‖ ≤
          ∑ i, ‖MvPowerSeries.coeff d (series s A (x i))‖ := by
        refine (pi_norm_le_iff_of_nonneg
          (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr fun i => ?_
        exact Finset.single_le_sum (f := fun i => ‖MvPowerSeries.coeff d (series s A (x i))‖)
          (fun i _ => norm_nonneg _) (Finset.mem_univ i)
      rw [← Finset.sum_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right ((hab d t).trans (mul_le_mul_of_nonneg_left hv hC))
        (s.weight_pos d).le
  refine ⟨fun t => ofSeries s A (fun d => a d t) (hres t), fun i => ?_⟩
  refine ext_coeff s A fun d => ?_
  change _ = coeffLinearMap s A d (∑ t, n t i • ofSeries s A (fun d => a d t) (hres t))
  rw [map_sum]
  simp only [map_smul, coeffLinearMap_apply, smul_eq_mul]
  have h := congrFun (ha d) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm]
  rfl

/-- Every relative series algebra over a presented affinoid is flat as an
algebra over its coefficient ring. -/
theorem flat_generalizedTateAlgebra (A : PresentedAffinoidAlgebra K) {σ : Type v}
    (s : PositivePolyradius σ) : Module.Flat A (GeneralizedTateAlgebra s A) := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l} {f} {x} hfx => ?_
  let N : Submodule A (Fin l → A) := LinearMap.ker (Fintype.linearCombination A f)
  obtain ⟨q, n, hn⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian N)
  have hmem : ∀ v, v ∈ N ↔ ∑ i, f i * v i = 0 := by
    intro v
    simp only [N, LinearMap.mem_ker, Fintype.linearCombination_apply, smul_eq_mul, mul_comm]
  obtain ⟨y, hy⟩ := exists_series_span_lift A s n x fun d => by
    rw [hn, hmem]
    have h := congrArg (coeffLinearMap s A d) hfx
    rw [map_sum, map_zero] at h
    simpa only [map_smul, coeffLinearMap_apply, smul_eq_mul] using h
  refine ⟨q, fun i t => n t i, y, hy, fun t => ?_⟩
  exact (hmem (n t)).mp (hn ▸ Submodule.subset_span ⟨t, rfl⟩)


/-- A sequence obeying the recurrence of the rational equation `g X - f`, with
`g` and `f` generating the unit ideal, vanishes in a Noetherian ring. -/
theorem eq_zero_of_rationalRecurrence {R : Type*} [CommRing R] [IsNoetherianRing R]
    {a b g f : R} (hab : a * g + b * f = 1) (c : ℕ → R) (h0 : f * c 0 = 0)
    (hrec : ∀ k, g * c k = f * c (k + 1)) (k : ℕ) : c k = 0 := by
  let M : Submodule R R := Submodule.span R (Set.range c)
  have hle : M ≤ Ideal.span {f} • M := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hk : c k = f • (a • c (k + 1) + b • c k) := by
      simp only [smul_eq_mul]
      linear_combination (-(c k)) * hab + a * hrec k
    rw [SetLike.mem_coe, hk]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f)
      (M.add_mem (M.smul_mem a (Submodule.subset_span ⟨k + 1, rfl⟩))
        (M.smul_mem b (Submodule.subset_span ⟨k, rfl⟩)))
  obtain ⟨r, hr, hrM⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (Ideal.span {f}) M (IsNoetherian.noetherian M) hle
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hr
  have key : ∀ k, f * c k = 0 → c k = 0 := fun k hk => by
    have h1 : r * c k = 0 := hrM _ (Submodule.subset_span ⟨k, rfl⟩)
    linear_combination h1 + (c k) * ht - t * hk
  induction k with
  | zero => exact key 0 h0
  | succ k ih => exact key (k + 1) (by rw [← hrec k, ih, mul_zero])

/-- Every ideal of a finite-variable relative series algebra over a presented
affinoid is closed, by transport from the enlarged presented affinoid. -/
theorem isClosed_ideal_generalizedTateAlgebra (A : PresentedAffinoidAlgebra K) {m : ℕ}
    (s : PositivePolyradius (Fin m)) (J : Ideal (GeneralizedTateAlgebra s A)) :
    IsClosed (J : Set (GeneralizedTateAlgebra s A)) := by
  let J' : Ideal (Adjoin.algebra K A s ∅) := J.comap (Adjoin.relativeSeriesMap K A s).toAlgHom
  have hJ' : IsClosed (J' : Set (Adjoin.algebra K A s ∅)) := isClosed_ideal _ J'
  have hcont : Continuous (Adjoin.relativeSeriesInverse K A s) :=
    AddMonoidHomClass.continuous_of_bound (Adjoin.relativeSeriesInverse K A s).toAlgHom 1
      fun f => by simpa using Adjoin.norm_relativeSeriesInverse_le K A s f
  have hJ : (J : Set (GeneralizedTateAlgebra s A)) =
      Adjoin.relativeSeriesInverse K A s ⁻¹' (J' : Set (Adjoin.algebra K A s ∅)) := by
    ext f
    change f ∈ J ↔ Adjoin.relativeSeriesMap K A s (Adjoin.relativeSeriesInverse K A s f) ∈ J
    rw [Adjoin.relativeSeriesMap_inverse]
  rw [hJ]
  exact hJ'.preimage hcont


/-- A relative series whose coefficients all lie in a finitely generated ideal
is a combination of the generators with relative series coefficients. -/
theorem exists_series_ideal_lift (A : PresentedAffinoidAlgebra K) {σ : Type v}
    (s : PositivePolyradius σ) {l : ℕ} (f : Fin l → A) (x : GeneralizedTateAlgebra s A)
    (hx : ∀ d, MvPowerSeries.coeff d (series s A x) ∈ Ideal.span (Set.range f)) :
    ∃ z : Fin l → GeneralizedTateAlgebra s A, x = ∑ t, f t • z t := by
  obtain ⟨y, hy⟩ := exists_series_span_lift A s (k := 1) (fun t _ => f t) (fun _ => x)
    fun d => by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp (hx d)
      refine (Submodule.mem_span_range_iff_exists_fun A).mpr ⟨c, ?_⟩
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hc ⊢
      exact hc
  exact ⟨y, hy 0⟩

/-- The one-variable relative series quotient by a single rational equation
`g X - f₀`, with `g` and `f₀` generating the unit ideal, is flat over the
coefficient ring. -/
theorem flat_quotient_rationalEquation (A : PresentedAffinoidAlgebra K)
    (s : PositivePolyradius (Fin 1)) (g f₀ : A) (hgen : Ideal.span {g, f₀} = ⊤) :
    Module.Flat A (GeneralizedTateAlgebra s A ⧸ Ideal.span
      {algebraMap A (GeneralizedTateAlgebra s A) g * X s A 0 -
        algebraMap A (GeneralizedTateAlgebra s A) f₀}) := by
  obtain ⟨h, hh⟩ : ∃ h : GeneralizedTateAlgebra s A,
      h = algebraMap A (GeneralizedTateAlgebra s A) g * X s A 0 -
        algebraMap A (GeneralizedTateAlgebra s A) f₀ := ⟨_, rfl⟩
  rw [← hh]
  have := flat_generalizedTateAlgebra A s
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp
    (hgen ▸ Submodule.mem_top : (1 : A) ∈ Ideal.span {g, f₀})
  refine Module.Flat.of_forall_isTrivialRelation fun {l} {f} {x} hfx => ?_
  choose x' hx' using fun i => Ideal.Quotient.mkₐ_surjective A (Ideal.span {h}) (x i)
  have hmem : ∑ i, f i • x' i ∈ Ideal.span {h} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change Ideal.Quotient.mkₐ A (Ideal.span {h}) (∑ i, f i • x' i) = 0
    rw [map_sum]
    simp only [map_smul, hx']
    exact hfx
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hmem
  let I : Ideal A := Ideal.span (Set.range f)
  have hcoef : ∀ d, MvPowerSeries.coeff d (series s A (q * h)) ∈ I := by
    intro d
    rw [hq]
    have e : MvPowerSeries.coeff d (series s A (∑ i, f i • x' i)) =
        ∑ i, f i * MvPowerSeries.coeff d (series s A (x' i)) := by
      change coeffLinearMap s A d (∑ i, f i • x' i) = _
      rw [map_sum]
      simp only [map_smul, coeffLinearMap_apply, smul_eq_mul]
    rw [e]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hX : series s A (X s A 0) = MvPowerSeries.monomial (Finsupp.single 0 1) 1 := rfl
  have hser : series s A (q * h) = MvPowerSeries.C g *
      (MvPowerSeries.monomial (Finsupp.single 0 1) 1 * series s A q) -
        MvPowerSeries.C f₀ * series s A q := by
    change seriesAlgHom s A (q * h) = _
    have hC : ∀ c : A, series s A (algebraMap A (GeneralizedTateAlgebra s A) c) =
        MvPowerSeries.C c := fun c => by
      change algebraMap A (MvPowerSeries (Fin 1) A) c = _
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [hh, map_mul, map_sub, map_mul]
    simp only [seriesAlgHom_apply, hC, hX]
    ring
  let c : ℕ → A ⧸ I := fun k =>
    Ideal.Quotient.mk I (MvPowerSeries.coeff (Finsupp.single 0 k) (series s A q))
  have h0 : Ideal.Quotient.mk I f₀ * c 0 = 0 := by
    have h1 := hcoef 0
    rw [hser, map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      ← MvPowerSeries.X_def, MvPowerSeries.coeff_zero_X_mul, mul_zero, zero_sub] at h1
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Finsupp.single_zero]
    simpa using I.neg_mem h1
  have hrec : ∀ k, Ideal.Quotient.mk I g * c k = Ideal.Quotient.mk I f₀ * c (k + 1) := by
    intro k
    have h1 := hcoef (Finsupp.single 0 (k + 1))
    have hsplit : Finsupp.single (0 : Fin 1) (k + 1) =
        Finsupp.single 0 1 + Finsupp.single 0 k := by
      rw [← Finsupp.single_add, add_comm]
    rw [hser, map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul] at h1
    conv at h1 => enter [2, 1, 2]; rw [hsplit, MvPowerSeries.coeff_add_monomial_mul, one_mul]
    rw [← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact h1
  have hab' : Ideal.Quotient.mk I a * Ideal.Quotient.mk I g +
      Ideal.Quotient.mk I b * Ideal.Quotient.mk I f₀ = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, hab, map_one]
  have hq' : ∀ d, MvPowerSeries.coeff d (series s A q) ∈ I := by
    intro d
    have hd : d = Finsupp.single 0 (d 0) :=
      Finsupp.ext fun i => by rw [Subsingleton.elim i 0, Finsupp.single_eq_same]
    rw [hd, ← Ideal.Quotient.eq_zero_iff_mem]
    exact eq_zero_of_rationalRecurrence hab' c h0 hrec (d 0)
  obtain ⟨z, hz⟩ := exists_series_ideal_lift A s f q hq'
  have hsum : ∑ i, f i • (x' i - z i * h) = 0 := by
    have e1 : ∑ i, f i • (z i * h) = q * h := by
      rw [hz, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => (smul_mul_assoc _ _ _).symm
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [e1, hq, sub_self]
  obtain ⟨k, a', y, hy, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := A) (M := GeneralizedTateAlgebra s A) hsum
  refine ⟨k, a', fun j => Ideal.Quotient.mkₐ A (Ideal.span {h}) (y j), fun i => ?_, hf⟩
  rw [← hx' i]
  have hzi : Ideal.Quotient.mkₐ A (Ideal.span {h}) (x' i) = Ideal.Quotient.mkₐ A (Ideal.span {h}) (x' i - z i * h) := by
    rw [map_sub, eq_comm, sub_eq_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
  rw [hzi, show x' i - z i * h = ∑ j, a' i j • y j from hy i, map_sum]
  exact Finset.sum_congr rfl fun j _ => map_smul (Ideal.Quotient.mkₐ A (Ideal.span {h})) _ _


/-- The intrinsic relative rational quotient with one fraction coordinate is
flat over its coefficient ring. -/
theorem flat_relativeRationalAlgebra (A : PresentedAffinoidAlgebra K)
    (s : PositivePolyradius (Fin 1)) (g : A) (f : Fin 1 → A)
    (hgen : RelativeRationalPresentation.GeneratesUnitIdeal K A g f) :
    Module.Flat A (RelativeRationalPresentation.Algebra K A s g f) := by
  have hgen' : Ideal.span {g, f 0} = ⊤ := by
    rw [RelativeRationalPresentation.GeneratesUnitIdeal, Set.range_unique] at hgen
    exact hgen
  have hE : RelativeRationalPresentation.equations K A s g f =
      {algebraMap A (GeneralizedTateAlgebra s A) g * X s A 0 -
        algebraMap A (GeneralizedTateAlgebra s A) (f 0)} := by
    rw [RelativeRationalPresentation.equations, Set.range_unique]
    rfl
  have hI : RelativeRelations.ideal K A s (RelativeRationalPresentation.equations K A s g f) =
      Ideal.span {algebraMap A (GeneralizedTateAlgebra s A) g * X s A 0 -
        algebraMap A (GeneralizedTateAlgebra s A) (f 0)} := by
    rw [RelativeRelations.ideal, hE]
    exact Ideal.closure_eq_of_isClosed _ (isClosed_ideal_generalizedTateAlgebra A s _)
  have key : ∀ J : Ideal (GeneralizedTateAlgebra s A),
      J = Ideal.span {algebraMap A (GeneralizedTateAlgebra s A) g * X s A 0 -
                        algebraMap A (GeneralizedTateAlgebra s A) (f 0)} →
        Module.Flat A (GeneralizedTateAlgebra s A ⧸ J) := by
    rintro J rfl
    exact flat_quotient_rationalEquation A s g (f 0) hgen'
  exact key _ hI

/-- The structural map of a scalar rational presentation with one fraction
coordinate is flat, by comparison with the intrinsic relative quotient. -/
theorem flat_rationalPresentation_baseMap (A : PresentedAffinoidAlgebra K)
    (s : PositivePolyradius (Fin 1)) (g : GeneralizedTateAlgebra A.polyradius K)
    (f : Fin 1 → GeneralizedTateAlgebra A.polyradius K)
    (hgen : RationalPresentation.GeneratesUnitIdeal K A g f) :
    (RationalPresentation.baseMap K A s g f).toAlgHom.toRingHom.Flat := by
  let e := RationalPresentation.relativeEquiv K A s g f
  let ρ := RelativeRationalPresentation.baseMap K A s (presentationMap K A g)
    (fun j => presentationMap K A (f j))
  have hrel : ρ.toAlgHom.toRingHom.Flat := by
    have hρ : ρ.toAlgHom.toRingHom = algebraMap A (RelativeRationalPresentation.Algebra K A s
        (presentationMap K A g) (fun j => presentationMap K A (f j))) :=
      RingHom.ext fun a => rfl
    rw [hρ, RingHom.flat_algebraMap_iff]
    exact flat_relativeRationalAlgebra A s _ _ hgen
  have hcomp : (RationalPresentation.baseMap K A s g f).toAlgHom.toRingHom =
      e.symm.toAlgEquiv.toAlgHom.toRingHom.comp ρ.toAlgHom.toRingHom :=
    RingHom.ext fun a => (RationalPresentation.relativeEquiv_symm_baseMap K A s g f a).symm
  rw [hcomp]
  exact hrel.comp (RingHom.Flat.of_bijective e.symm.toAlgEquiv.bijective)

end Langlands.Analytic.PresentedAffinoidAlgebra
