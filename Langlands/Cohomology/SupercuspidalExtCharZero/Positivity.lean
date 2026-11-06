import Langlands.Cohomology.SupercuspidalExtCharZero.CosetSum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.RingTheory.Jacobson.Ring

/-!
# A nonvanishing coset sum over a field of characteristic zero

Let `U` be an open subgroup of a topological group `G` and `F : G → k` a function with
compact support that is invariant under left and right translation by `U` and satisfies
`F 1 ≠ 0`. Then there are `x y : G` with `F x⁻¹ ≠ 0` and
`∑_{pU} F (x⁻¹ p⁻¹) F (y⁻¹ p) ≠ 0`, the sum running over the left cosets of `U`.

Over `ℂ` this is a positivity argument: with `h g = ∑_{xU} F (x⁻¹ g) conj (F x⁻¹)` one has
`h g⁻¹ = conj (h g)`, so `∑_{pU} h p⁻¹ h p = ∑_{pU} |h p|² ≥ |h 1|² > 0`, while expanding
the same sum writes it as a linear combination of the sums in the conclusion. Over an
arbitrary field of characteristic zero, the finitely many values of `F` together with
`(F 1)⁻¹` generate a finitely generated `ℚ`-subalgebra; a quotient by a maximal ideal is a
number field (Zariski's lemma), which embeds into `ℂ`. The complex case applied to the
image of `F` gives the general one.
-/

noncomputable section

namespace Langlands.Cohomology.SupercuspidalExtCharZero

open Function ComplexConjugate
open scoped Pointwise

universe uG uk

variable {G : Type uG} [Group G]

/-- A coset sum over a finite set of cosets containing every contributing coset. -/
theorem cosetSum_eq_sum {M : Type*} [AddCommMonoid M] {U : Subgroup G} {f : G → M}
    {s : Finset (G ⧸ U)} (hs : ∀ q : G ⧸ U, f q.out ≠ 0 → q ∈ s) :
    cosetSum U f = ∑ q ∈ s, f q.out :=
  finsum_eq_sum_of_support_subset _ fun q hq => hs q hq

section Complex

/-- The self-convolution `g ↦ ∑_{xU} f (x⁻¹ g) conj (f x⁻¹)`. -/
def selfConvolution (U : Subgroup G) (f : G → ℂ) (g : G) : ℂ :=
  cosetSum U fun x => f (x⁻¹ * g) * conj (f x⁻¹)

theorem selfConvolution_inv {U : Subgroup G} {f : G → ℂ}
    (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) (g : G) :
    selfConvolution U f g⁻¹ = conj (selfConvolution U f g) := by
  have hinv : RightInvariant U fun x => f (x⁻¹ * g⁻¹) * conj (f x⁻¹) := by
    intro x u hu
    simp only [mul_inv_rev, mul_assoc]
    rw [hl u⁻¹ (U.inv_mem hu), hl u⁻¹ (U.inv_mem hu)]
  unfold selfConvolution
  rw [← cosetSum_mul_left hinv g⁻¹]
  unfold cosetSum
  rw [starRingEnd_apply, ← starAddEquiv_apply, AddEquiv.map_finsum]
  congr 1
  ext q
  simp only [starAddEquiv_apply, star_mul', mul_inv_rev, inv_inv, mul_assoc,
    mul_inv_cancel, mul_one]
  rw [mul_comm, ← starRingEnd_apply, ← starRingEnd_apply, Complex.conj_conj]

theorem selfConvolution_mul {U : Subgroup G} {f : G → ℂ} (hr : RightInvariant U f) :
    RightInvariant U (selfConvolution U f) := by
  intro g u hu
  unfold selfConvolution
  refine cosetSum_congr fun x => ?_
  rw [← mul_assoc, hr _ u hu]

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem selfConvolution_ne_zero_mem {U : Subgroup G} {f : G → ℂ} {g : G}
    (hg : selfConvolution U f g ≠ 0) : g ∈ (tsupport f)⁻¹ * tsupport f := by
  by_contra hmem
  apply hg
  refine cosetSum_eq_zero fun x => ?_
  by_contra hx
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hx
  have hx1 : x⁻¹ ∈ tsupport f := subset_tsupport f fun h => h2 (by simp [h])
  have hx2 : x⁻¹ * g ∈ tsupport f := subset_tsupport f h1
  apply hmem
  have := Set.mul_mem_mul (Set.inv_mem_inv.mpr hx1) hx2
  simpa [mul_assoc] using this

/-- The positivity core over `ℂ`. -/
theorem exists_cosetSum_ne_zero_complex {U : Subgroup G} (hU : IsOpen (U : Set G))
    {f : G → ℂ} (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) (hr : RightInvariant U f)
    (hf : HasCompactSupport f) (h1 : f 1 ≠ 0) :
    ∃ x y : G, f x⁻¹ ≠ 0 ∧ cosetSum U (fun p => f (x⁻¹ * p⁻¹) * f (y⁻¹ * p)) ≠ 0 := by
  classical
  set K1 : Set G := (tsupport f)⁻¹
  set K2 : Set G := K1 * tsupport f
  have hK1 : IsCompact K1 := hf.isCompact.inv
  have hK2 : IsCompact K2 := hK1.mul hf.isCompact
  set X : Finset (G ⧸ U) := (finite_image_mk hU hK1).toFinset
  set P : Finset (G ⧸ U) := (finite_image_mk hU hK2).toFinset
  have hmemK1 : ∀ x : G, f x⁻¹ ≠ 0 → x ∈ K1 := fun x hx =>
    Set.mem_inv.mpr (subset_tsupport f hx)
  have hmemX : ∀ q : G ⧸ U, f q.out⁻¹ ≠ 0 → q ∈ X := fun q hq => by
    simpa [X] using mem_image_mk_of_out_mem (hmemK1 _ hq)
  set h := selfConvolution U f
  have hexp : ∀ g, h g = ∑ x ∈ X, f (x.out⁻¹ * g) * conj (f x.out⁻¹) := fun g =>
    cosetSum_eq_sum fun q hq => hmemX q fun h0 => hq (by simp [h0])
  have hfinv : RightInvariant U fun x => f x⁻¹ := by
    intro x u hu
    show f (x * u)⁻¹ = f x⁻¹
    rw [mul_inv_rev, hl u⁻¹ (U.inv_mem hu)]
  -- `h 1 ≠ 0`
  have hh1 : h 1 ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re (hexp 1)
    rw [h0, Complex.re_sum] at hre
    have hterm : ∀ x ∈ X, (f (x.out⁻¹ * 1) * conj (f x.out⁻¹)).re =
        Complex.normSq (f x.out⁻¹) := fun x _ => by
      rw [mul_one, Complex.mul_conj, Complex.ofReal_re]
    rw [Finset.sum_congr rfl hterm] at hre
    have hq1 : f (QuotientGroup.mk (1 : G) : G ⧸ U).out⁻¹ = f 1 := by
      simpa using hfinv.apply_out 1
    have hmem1 : (QuotientGroup.mk (1 : G) : G ⧸ U) ∈ X := hmemX _ (by rw [hq1]; exact h1)
    have hle := Finset.single_le_sum (f := fun x : G ⧸ U => Complex.normSq (f x.out⁻¹))
      (fun x _ => Complex.normSq_nonneg _) hmem1
    rw [hq1, ← hre, Complex.zero_re] at hle
    exact absurd (Complex.normSq_pos.mpr h1) (not_lt.mpr hle)
  by_contra H
  push Not at H
  -- the sum `Q = ∑_{pU} h p⁻¹ h p`
  have hmemP : ∀ q : G ⧸ U, h q.out ≠ 0 → q ∈ P := fun q hq => by
    simpa [P] using mem_image_mk_of_out_mem (selfConvolution_ne_zero_mem hq)
  have hQzero : ∑ p ∈ P, h p.out⁻¹ * h p.out = 0 := by
    simp_rw [hexp, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hx : f x.out⁻¹ = 0
    · simp [hx]
    by_cases hy : f y.out⁻¹ = 0
    · simp [hy]
    have hsum : ∑ p ∈ P, f (x.out⁻¹ * p.out⁻¹) * f (y.out⁻¹ * p.out) =
        cosetSum U fun p => f (x.out⁻¹ * p⁻¹) * f (y.out⁻¹ * p) := by
      refine (cosetSum_eq_sum (f := fun p => f (x.out⁻¹ * p⁻¹) * f (y.out⁻¹ * p)) (s := P)
        fun q hq => ?_).symm
      have hq2 : f (y.out⁻¹ * q.out) ≠ 0 := right_ne_zero_of_mul hq
      have hmem : q.out ∈ K2 := by
        have := Set.mul_mem_mul (hmemK1 _ hy) (subset_tsupport f hq2)
        simpa [K2, mul_assoc] using this
      simpa [P] using mem_image_mk_of_out_mem hmem
    have hzero := H x.out y.out hx
    rw [← hsum] at hzero
    calc ∑ p ∈ P, f (x.out⁻¹ * p.out⁻¹) * conj (f x.out⁻¹) *
          (f (y.out⁻¹ * p.out) * conj (f y.out⁻¹))
        = conj (f x.out⁻¹) * conj (f y.out⁻¹) *
          ∑ p ∈ P, f (x.out⁻¹ * p.out⁻¹) * f (y.out⁻¹ * p.out) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ = 0 := by rw [hzero, mul_zero]
  -- but `Q` has positive real part
  have hQpos : 0 < (∑ p ∈ P, h p.out⁻¹ * h p.out).re := by
    have hterm : ∀ p ∈ P, (h p.out⁻¹ * h p.out).re = Complex.normSq (h p.out) :=
      fun p _ => by
        rw [show h p.out⁻¹ = conj (h p.out) from selfConvolution_inv hl _,
          ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    rw [Complex.re_sum, Finset.sum_congr rfl hterm]
    have hq1 : h (QuotientGroup.mk (1 : G) : G ⧸ U).out = h 1 :=
      (selfConvolution_mul hr).apply_out 1
    have hmem1 : (QuotientGroup.mk (1 : G) : G ⧸ U) ∈ P := hmemP _ (by rw [hq1]; exact hh1)
    have hle := Finset.single_le_sum (f := fun p : G ⧸ U => Complex.normSq (h p.out))
      (fun p _ => Complex.normSq_nonneg _) hmem1
    rw [hq1] at hle
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr hh1) hle
  rw [hQzero, Complex.zero_re] at hQpos
  exact lt_irrefl _ hQpos

end Complex

section Embedding

/-- A finitely generated `ℚ`-subalgebra of a field of characteristic zero has a ring
homomorphism to `ℂ`. -/
theorem exists_ringHom_complex {k : Type uk} [Field k] [CharZero k] {s : Set k}
    (hs : s.Finite) : Nonempty (Algebra.adjoin ℚ s →+* ℂ) := by
  have : Algebra.FiniteType ℚ (Algebra.adjoin ℚ s) := Algebra.FiniteType.adjoin_of_finite hs
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Algebra.adjoin ℚ s)
  let := Ideal.Quotient.field m
  have : Module.Finite ℚ (Algebra.adjoin ℚ s ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing ℚ _
  exact ⟨(IsAlgClosed.lift (R := ℚ) (S := Algebra.adjoin ℚ s ⧸ m) (M := ℂ)).toRingHom.comp
    (Ideal.Quotient.mk m)⟩

end Embedding

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The nonvanishing coset sum over a field of characteristic zero. -/
theorem exists_cosetSum_ne_zero {k : Type uk} [Field k] [CharZero k] {U : Subgroup G}
    (hU : IsOpen (U : Set G)) {F : G → k} (hl : ∀ u ∈ U, ∀ g, F (u * g) = F g)
    (hr : RightInvariant U F) (hF : HasCompactSupport F) (h1 : F 1 ≠ 0) :
    ∃ x y : G, F x⁻¹ ≠ 0 ∧ cosetSum U (fun p => F (x⁻¹ * p⁻¹) * F (y⁻¹ * p)) ≠ 0 := by
  classical
  -- `F` takes finitely many values
  have hrange : (Set.range F).Finite := by
    refine (((finite_image_mk hU hF.isCompact).image fun q : G ⧸ U => F q.out).insert
      0).subset ?_
    rintro _ ⟨g, rfl⟩
    by_cases hg : F g = 0
    · exact Or.inl hg
    · refine Or.inr ⟨QuotientGroup.mk g, ⟨g, subset_tsupport F hg, rfl⟩, hr.apply_out g⟩
  set s : Set k := insert (F 1)⁻¹ (Set.range F)
  have hs : s.Finite := hrange.insert _
  obtain ⟨τ⟩ := exists_ringHom_complex hs
  set A := Algebra.adjoin ℚ s
  have hmem : ∀ g, F g ∈ A := fun g =>
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨g, rfl⟩)
  have hmem1 : (F 1)⁻¹ ∈ A := Algebra.subset_adjoin (Set.mem_insert _ _)
  set F' : G → A := fun g => ⟨F g, hmem g⟩
  have hF'zero : ∀ g, F g = 0 → F' g = 0 := fun g hg => Subtype.ext hg
  set f : G → ℂ := fun g => τ (F' g)
  have hfzero : ∀ g, F g = 0 → f g = 0 := fun g hg => by simp [f, hF'zero g hg]
  have hl' : ∀ u ∈ U, ∀ g, f (u * g) = f g := fun u hu g => by
    simp only [f, F', hl u hu g]
  have hr' : RightInvariant U f := fun g u hu => by
    simp only [f, F', hr g u hu]
  have hf : HasCompactSupport f := hF.mono fun g hg => fun h0 => hg (hfzero g h0)
  have h1' : f 1 ≠ 0 := by
    intro h0
    have hunit : F' 1 * ⟨(F 1)⁻¹, hmem1⟩ = 1 := Subtype.ext (mul_inv_cancel₀ h1)
    have := congrArg τ hunit
    rw [map_mul, map_one] at this
    simp only [f] at h0
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  obtain ⟨x, y, hx, hxy⟩ := exists_cosetSum_ne_zero_complex hU hl' hr' hf h1'
  refine ⟨x, y, fun h0 => hx (hfzero _ h0), fun h0 => hxy ?_⟩
  -- transport the vanishing sum along `A → k` and `τ`
  set K : Set G := (fun g => y * g) '' tsupport F
  have hK : IsCompact K := hF.isCompact.image (continuous_const.mul continuous_id)
  set S : Finset (G ⧸ U) := (finite_image_mk hU hK).toFinset
  have hS : ∀ q : G ⧸ U, F (y⁻¹ * q.out) ≠ 0 → q ∈ S := by
    intro q hq
    have : q.out ∈ K := ⟨y⁻¹ * q.out, subset_tsupport F hq, by simp⟩
    simpa [S] using mem_image_mk_of_out_mem this
  rw [cosetSum_eq_sum (s := S) fun q hq => hS q fun h0 => hq (by simp [h0])] at h0
  rw [cosetSum_eq_sum (s := S) fun q hq => hS q fun h0 => hq (by simp [hfzero _ h0])]
  have hA : ∑ q ∈ S, F' (x⁻¹ * q.out⁻¹) * F' (y⁻¹ * q.out) = 0 := by
    apply Subtype.ext
    simpa [F'] using h0
  have := congrArg τ hA
  simpa [f, map_sum, map_mul] using this

end Langlands.Cohomology.SupercuspidalExtCharZero
