import Langlands.GroupScheme.CoalgebraUnipotence.MatrixFromConilpotence
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Noetherian.Basic

noncomputable section

open Coalgebra TensorProduct Module
open Langlands.GroupScheme.AffineLinearEmbedding

namespace Langlands.GroupScheme.CoalgebraUnipotence

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Bialgebra k B]

@[simp] theorem rightAct_one (f : Module.Dual k B) :
    rightAct f (1 : B) = f 1 • (1 : B) := by
  simp [rightAct_apply, Algebra.TensorProduct.one_def]

theorem rightAct_mem_reducedLevel (n : ℕ) (g : Module.Dual k B) {b : B}
    (hb : b ∈ reducedLevel k B n) : rightAct g b ∈ reducedLevel k B n := by
  cases n with
  | zero =>
    have hb0 : b = 0 := (mem_reducedLevel_zero b).mp hb
    simp [hb0]
  | succ n =>
    rw [mem_reducedLevel_succ] at hb ⊢
    intro f hf
    rw [rightAct_rightAct]
    apply hb
    simp [hf]

/-- A nonzero finite-dimensional quotient of a right-translation-stable subspace has
a nonzero vector killed by every right translation whose functional vanishes at `1`. -/
theorem exists_fixed_mod_of_isMatrixUnipotent
    (hB : IsMatrixUnipotent k B) (W : Submodule k B)
    (hW : ∀ (f : Module.Dual k B) (w : W), rightAct f (w : B) ∈ W)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (q : W →ₗ[k] V) (hq : Function.Surjective q)
    (hker : ∀ (f : Module.Dual k B) (w : W), q w = 0 →
      q ⟨rightAct f (w : B), hW f w⟩ = 0) :
    ∃ w : W, q w ≠ 0 ∧ ∀ f : Module.Dual k B, f 1 = 0 →
      q ⟨rightAct f (w : B), hW f w⟩ = 0 := by
  classical
  let n := Module.finrank k V
  let e : Basis (Fin n) k V := Module.finBasis k V
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqs : ∀ v, q (s v) = v := fun v => LinearMap.congr_fun hs v
  obtain ⟨P, hP⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  have hPW : ∀ w : W, P (w : B) = w := fun w => LinearMap.congr_fun hP w
  let φ : Fin n → Module.Dual k B := fun i => e.coord i ∘ₗ q ∘ₗ P
  have hφ : ∀ (i : Fin n) (w : W), φ i (w : B) = e.coord i (q w) := by
    intro i w
    simp [φ, hPW]
  let M : Matrix (Fin n) (Fin n) B :=
    fun i j => leftAct (φ i) (s (e j) : B)
  have hM : ∀ i j, M i j = leftAct (φ i) (s (e j) : B) := fun _ _ => rfl
  have hleft_zero : ∀ (i : Fin n) (w : W), q w = 0 →
      leftAct (φ i) (w : B) = 0 := by
    intro i w hw
    apply (Module.forall_dual_apply_eq_zero_iff k _).mp
    intro g
    rw [apply_leftAct]
    change φ i ((⟨rightAct g (w : B), hW g w⟩ : W) : B) = 0
    rw [hφ, hker g w hw, map_zero]
  have hleft_expand : ∀ (i : Fin n) (w : W),
      leftAct (φ i) (w : B) = ∑ l, e.coord l (q w) • M i l := by
    intro i w
    have hk : q (w - s (q w)) = 0 := by simp [hqs]
    have hz := hleft_zero i (w - s (q w)) hk
    have heq : leftAct (φ i) (w : B) = leftAct (φ i) (s (q w) : B) := by
      simpa only [Submodule.coe_sub, map_sub, sub_eq_zero] using hz
    rw [heq, ← e.sum_repr (q w), map_sum]
    simp [hM]
  have hright_coord : ∀ (g : Module.Dual k B) (j i : Fin n),
      e.coord i (q ⟨rightAct g (s (e j) : B), hW g (s (e j))⟩) = g (M i j) := by
    intro g j i
    rw [hM, apply_leftAct, ← hφ]
  have hcoeff : IsCoefficientMatrix (k := k) M := by
    constructor
    · intro i j
      apply tensor_ext
      intro g
      rw [← rightAct_apply, hM, rightAct_leftAct]
      rw [hleft_expand i ⟨rightAct g (s (e j) : B), hW g (s (e j))⟩]
      simp [hright_coord]
    · intro i j
      rw [hM, apply_leftAct, rightAct_counit]
      rw [hφ, hqs]
      simp [Basis.coord_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  obtain ⟨v, hv, hfixed⟩ := hB n (Module.finrank_pos) M hcoeff
  let y : V := ∑ j, v j • e j
  have hy : y ≠ 0 := by
    intro hy
    apply hv
    funext i
    have hi := congrArg (e.coord i) hy
    simpa [y, Basis.coord_apply, Finsupp.single_apply] using hi
  refine ⟨s y, by simpa [hqs] using hy, fun f hf => ?_⟩
  apply e.repr.injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  change e.coord i (q ⟨rightAct f (s y : B), hW f (s y)⟩) = 0
  rw [← hφ, ← apply_leftAct]
  have hleft_y : leftAct (φ i) (s y : B) = ∑ j, v j • M i j := by
    simp [y, hM]
  rw [hleft_y, hfixed i, map_smul, hf, smul_zero]

theorem exists_reducedLevel_containing_finite_stable
    (hB : IsMatrixUnipotent k B) (W : Submodule k B) [FiniteDimensional k W]
    (hW : ∀ (f : Module.Dual k B) (w : W), rightAct f (w : B) ∈ W) :
    ∃ n, W ≤ reducedLevel k B n := by
  classical
  let F : ℕ →o Submodule k W :=
    ⟨fun n => (reducedLevel k B n).comap W.subtype,
      fun _ _ hij => Submodule.comap_mono (reducedLevel_mono hij)⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian k W) F
  have heq : F n = F (n + 1) := hn (n + 1) (Nat.le_succ n)
  have htop : F n = ⊤ := by
    by_contra hne
    let : Nontrivial (W ⧸ F n) := Submodule.Quotient.nontrivial_iff.mpr hne
    have hker : ∀ (f : Module.Dual k B) (w : W), (F n).mkQ w = 0 →
        (F n).mkQ ⟨rightAct f (w : B), hW f w⟩ = 0 := by
      intro f w hw
      have hw' : w ∈ F n := (Submodule.Quotient.mk_eq_zero _).mp hw
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact rightAct_mem_reducedLevel n f hw'
    obtain ⟨w, hw, hfixed⟩ := exists_fixed_mod_of_isMatrixUnipotent
      hB W hW (F n).mkQ (F n).mkQ_surjective hker
    have hw_next : w ∈ F (n + 1) := by
      change (w : B) ∈ reducedLevel k B (n + 1)
      rw [mem_reducedLevel_succ]
      intro f hf
      have hmem : (⟨rightAct f (w : B), hW f w⟩ : W) ∈ F n :=
        (Submodule.Quotient.mk_eq_zero _).mp (hfixed f hf)
      exact hmem
    apply hw
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rwa [heq]
  refine ⟨n, fun b hb => ?_⟩
  have hmem : (⟨b, hb⟩ : W) ∈ F n := by rw [htop]; trivial
  exact hmem

theorem isLocallyConilpotent_of_isMatrixUnipotent
    (hB : IsMatrixUnipotent k B) : IsLocallyConilpotent k B := by
  classical
  intro b
  obtain ⟨n, M, hΔ, hε, hcontains⟩ :=
    exists_matrix_coefficients (K := k) ({b} : Finset B)
  let W : Submodule k B :=
    Submodule.span k (Set.range fun p : Fin n × Fin n => M p.1 p.2)
  let : FiniteDimensional k W :=
    Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range _))
  have hW : ∀ (f : Module.Dual k B) (w : W), rightAct f (w : B) ∈ W := by
    intro f w
    have hle : W ≤ W.comap (rightAct f) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      have hact : rightAct f (M i j) = ∑ l, f (M l j) • M i l := by
        simp [rightAct_apply, hΔ]
      change rightAct f (M i j) ∈ W
      rw [hact]
      exact Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, l), rfl⟩)
    exact hle w.2
  obtain ⟨m, hm⟩ := exists_reducedLevel_containing_finite_stable hB W hW
  exact ⟨m, hm (hcontains (by simp))⟩

end Langlands.GroupScheme.CoalgebraUnipotence
