import Langlands.Geometry.Analytic.GeneralizedAffinoid.LaurentGaussField
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Operator.Basic

/-! # Realizing finitely many positive radii in a complete extension field -/

noncomputable section

universe u

namespace Langlands.Analytic

/-- A complete ultrametric field `L` with an isometric embedding of `K`, elements
`c i` of the prescribed norms `t i`, and a bounded `K`-linear retraction `π` onto `K`. -/
structure RadiusRealization (K : Type u) [NormedField K] {N : ℕ} (t : Fin N → ℝ) where
  /-- The extension field. -/
  L : Type u
  [instNormedField : NormedField L]
  [instUltrametric : IsUltrametricDist L]
  [instComplete : CompleteSpace L]
  /-- The isometric embedding of the coefficient field. -/
  ι : K →+* L
  norm_ι : ∀ a, ‖ι a‖ = ‖a‖
  /-- Elements of the prescribed norms. -/
  c : Fin N → L
  norm_c : ∀ i, ‖c i‖ = t i
  /-- A bounded additive retraction, linear over the coefficient field. -/
  π : L →+ K
  π_ι_mul : ∀ a x, π (ι a * x) = a * π x
  π_one : π 1 = 1
  /-- A bound for the retraction. -/
  bound : ℝ
  bound_pos : 0 < bound
  norm_π_le : ∀ x, ‖π x‖ ≤ bound * ‖x‖

namespace RadiusRealization

attribute [instance] instNormedField instUltrametric instComplete

variable {K : Type u} [NormedField K]

/-- Realize one more radius over a field which realizes the previous radii. -/
def cons {N : ℕ} {t : Fin N → ℝ} {τ : ℝ} (R : RadiusRealization K t)
    (S : RadiusRealization R.L (fun _ : Fin 1 => τ)) :
    RadiusRealization K (Fin.cons τ t : Fin (N + 1) → ℝ) where
  L := S.L
  ι := S.ι.comp R.ι
  norm_ι a := by rw [RingHom.comp_apply, S.norm_ι, R.norm_ι]
  c := (Fin.cons (S.c 0) fun i => S.ι (R.c i) : Fin (N + 1) → S.L)
  norm_c i := by
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using S.norm_c 0
    · simpa [S.norm_ι] using R.norm_c i
  π := R.π.comp S.π
  π_ι_mul a x := by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, RingHom.comp_apply, S.π_ι_mul,
      R.π_ι_mul]
  π_one := by rw [AddMonoidHom.comp_apply, S.π_one, R.π_one]
  bound := R.bound * S.bound
  bound_pos := mul_pos R.bound_pos S.bound_pos
  norm_π_le x := by
    rw [AddMonoidHom.comp_apply, mul_assoc]
    exact (R.norm_π_le _).trans (mul_le_mul_of_nonneg_left (S.norm_π_le x) R.bound_pos.le)

variable [IsUltrametricDist K] [CompleteSpace K]

/-- No radius is realized by the field itself. -/
def empty (t : Fin 0 → ℝ) : RadiusRealization K t where
  L := K
  ι := RingHom.id K
  norm_ι _ := rfl
  c := Fin.elim0
  norm_c i := Fin.elim0 i
  π := AddMonoidHom.id K
  π_ι_mul _ _ := rfl
  π_one := rfl
  bound := 1
  bound_pos := zero_lt_one
  norm_π_le x := by simp

/-- Radius one is realized by `1` in the field itself. -/
def one : RadiusRealization K (fun _ : Fin 1 => (1 : ℝ)) where
  L := K
  ι := RingHom.id K
  norm_ι _ := rfl
  c _ := 1
  norm_c _ := norm_one
  π := AddMonoidHom.id K
  π_ι_mul _ _ := rfl
  π_one := rfl
  bound := 1
  bound_pos := zero_lt_one
  norm_π_le x := by simp

/-- A radius none of whose nonzero integral powers is a norm from `K` is realized
by the completed Gauss-normed Laurent field. -/
def laurent (t : ℝ) [Fact (0 < t)] (H : ∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n) :
    RadiusRealization K (fun _ : Fin 1 => t) :=
  letI : NormedField (CompletedGaussLaurent K t) := CompletedGaussLaurent.normedField H
  { L := CompletedGaussLaurent K t
    instUltrametric := completion_isUltrametricDist
    instComplete := inferInstanceAs (CompleteSpace (UniformSpace.Completion (GaussLaurent K t)))
    ι := CompletedGaussLaurent.ι
    norm_ι := CompletedGaussLaurent.norm_ι
    c := fun _ => CompletedGaussLaurent.X
    norm_c := fun _ => CompletedGaussLaurent.norm_X
    π := CompletedGaussLaurent.retraction
    π_ι_mul := CompletedGaussLaurent.retraction_ι_mul
    π_one := CompletedGaussLaurent.retraction_one
    bound := 1
    bound_pos := zero_lt_one
    norm_π_le := fun x => by
      rw [one_mul]
      exact CompletedGaussLaurent.norm_retraction_le x }

end RadiusRealization

section Root

open Polynomial

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A positive radius whose `n`-th power is the norm of `a` is realized by a root of
`X ^ n - a` in a splitting field with the spectral norm. -/
theorem RadiusRealization.nonempty_root (a : K) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (hat : ‖a‖ = t ^ n) : Nonempty (RadiusRealization K (fun _ : Fin 1 => t)) := by
  let L := SplittingField (X ^ n - C a)
  let _ : NormedField L := spectralNorm.normedField K L
  have _ : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := K) (L := L))
  have _ : CompleteSpace L := spectralNorm.completeSpace K L
  let _ : NormedSpace K L := spectralNorm.normedSpace K L
  have hnorm : ∀ k : K, ‖algebraMap K L k‖ = ‖k‖ := spectralNorm_extends
  obtain ⟨α, hα⟩ : ∃ α : L, eval α ((X ^ n - C a).map (algebraMap K L)) = 0 := by
    apply (SplittingField.splits (X ^ n - C a)).exists_eval_eq_zero
    rw [degree_map, degree_X_pow_sub_C hn]
    exact_mod_cast hn.ne'
  have hαn : α ^ n = algebraMap K L a := by
    simpa [sub_eq_zero] using hα
  have hαt : ‖α‖ = t := by
    have h : ‖α‖ ^ n = t ^ n := by rw [← norm_pow, hαn, hnorm, hat]
    exact (pow_left_inj₀ (norm_nonneg α) ht.le hn.ne').mp h
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
  let g : L →L[K] K := ⟨f, f.continuous_of_finiteDimensional⟩
  refine ⟨{ L := L
            ι := algebraMap K L
            norm_ι := hnorm
            c := fun _ => α
            norm_c := fun _ => hαt
            π := f.toAddMonoidHom
            π_ι_mul := fun k x => ?_
            π_one := hf
            bound := ‖g‖ + 1
            bound_pos := by positivity
            norm_π_le := fun x => ?_ }⟩
  · change f (algebraMap K L k * x) = k * f x
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  · change ‖g x‖ ≤ _
    exact (g.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg x))

end Root

namespace RadiusRealization

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Every positive radius is realized over every complete ultrametric field. -/
theorem nonempty_single (t : ℝ) (ht : 0 < t) :
    Nonempty (RadiusRealization K (fun _ : Fin 1 => t)) := by
  by_cases h1 : t = 1
  · subst h1
    exact ⟨one⟩
  by_cases hval : ∃ (a : K) (n : ℤ), n ≠ 0 ∧ ‖a‖ = t ^ n
  · obtain ⟨a, n, hn, ha⟩ := hval
    obtain ⟨b, m, hm, hb⟩ : ∃ (b : K) (m : ℕ), 0 < m ∧ ‖b‖ = t ^ m := by
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · refine ⟨a⁻¹, n.natAbs, by omega, ?_⟩
        rw [norm_inv, ha, ← zpow_natCast, Int.natCast_natAbs, abs_of_neg hneg, zpow_neg]
      · refine ⟨a, n.natAbs, by omega, ?_⟩
        rw [ha, ← zpow_natCast, Int.natCast_natAbs, abs_of_pos hpos]
    have hb1 : ‖b‖ ≠ 1 := by
      rw [hb]
      exact fun h => h1 ((pow_eq_one_iff_of_nonneg ht.le hm.ne').mp h)
    have hbpos : 0 < ‖b‖ := hb ▸ pow_pos ht m
    obtain ⟨x, hx⟩ : ∃ x : K, 1 < ‖x‖ := by
      rcases lt_or_gt_of_ne hb1 with h | h
      · exact ⟨b⁻¹, by rw [norm_inv]; exact one_lt_inv₀ hbpos |>.mpr h⟩
      · exact ⟨b, h⟩
    let _ : NontriviallyNormedField K :=
      { (inferInstance : NormedField K) with non_trivial := ⟨x, hx⟩ }
    exact nonempty_root b m hm t ht hb
  · push Not at hval
    have _ : Fact (0 < t) := ⟨ht⟩
    exact ⟨laurent t fun a n hn => hval a n hn⟩

/-- Every finite family of positive radii is realized over every complete
ultrametric field. -/
theorem nonempty : ∀ (N : ℕ) (t : Fin N → ℝ), (∀ i, 0 < t i) →
    Nonempty (RadiusRealization K t)
  | 0, t, _ => ⟨empty t⟩
  | N + 1, t, ht => by
    obtain ⟨R⟩ := nonempty N (Fin.tail t) fun i => ht i.succ
    obtain ⟨S⟩ := nonempty_single (K := R.L) (t 0) (ht 0)
    have h := R.cons S
    rw [Fin.cons_self_tail] at h
    exact ⟨h⟩

end RadiusRealization

end Langlands.Analytic
