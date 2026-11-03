import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Vanishing of graded components of an augmented graded algebra -/

noncomputable section

open DirectSum

namespace Langlands.Algebra.GradedAugmented

/-- `IsRigidInDegree 𝒜 ε χ`: every first-order deformation `φ : C →ₐ[k] k[ε]` of the
augmentation `ε` whose derivation part `(φ ·).snd` vanishes on all homogeneous components of
degree different from `χ` is trivial, i.e. its derivation part vanishes identically. -/
def IsRigidInDegree {k : Type*} [Field k] {C : Type*} [CommRing C] [Algebra k C]
    {Λ : Type*} (𝒜 : Λ → Submodule k C) (ε : C →ₐ[k] k) (χ : Λ) : Prop :=
  ∀ φ : C →ₐ[k] DualNumber k, (TrivSqZeroExt.fstHom k k k).comp φ = ε →
    (∀ ψ ≠ χ, ∀ c ∈ 𝒜 ψ, (φ c).snd = 0) → ∀ c, (φ c).snd = 0

section Helpers

variable {k : Type*} [Field k] {C : Type*} [CommRing C] [Algebra k C]
  {Λ : Type*} [AddCommGroup Λ] [DecidableEq Λ]
  {𝒜 : Λ → Submodule k C} [GradedAlgebra 𝒜] {ε : C →ₐ[k] k}

/-- The augmentation of a graded component is the augmentation of the element in degree
zero, and zero in every other degree. -/
theorem augmentation_decompose (hε : ∀ χ ≠ 0, ∀ c ∈ 𝒜 χ, ε c = 0) (x : C) (χ : Λ) :
    ε (decompose 𝒜 x χ) = if χ = 0 then ε x else 0 := by
  classical
  split_ifs with hχ
  · subst hχ
    conv_rhs => rw [← sum_support_decompose 𝒜 x]
    rw [map_sum]
    by_cases h0 : (0 : Λ) ∈ (decompose 𝒜 x).support
    · rw [Finset.sum_eq_single_of_mem 0 h0 fun i _ hi => hε i hi _ (decompose 𝒜 x i).2]
    · rw [Finset.sum_eq_zero fun i hi => hε i (fun h => h0 (h ▸ hi)) _ (decompose 𝒜 x i).2]
      rw [DFinsupp.notMem_support_iff] at h0
      rw [h0, ZeroMemClass.coe_zero, map_zero]
  · exact hε χ hχ _ (decompose 𝒜 x χ).2

/-- The augmentation ideal is homogeneous. -/
theorem isHomogeneous_ker (hε : ∀ χ ≠ 0, ∀ c ∈ 𝒜 χ, ε c = 0) :
    (RingHom.ker ε).IsHomogeneous 𝒜 := fun χ x hx => by
  rw [RingHom.mem_ker] at hx ⊢
  change ε (decompose 𝒜 x χ) = 0
  rw [augmentation_decompose hε, hx, ite_self]

theorem decompose_mem_ker (hε : ∀ χ ≠ 0, ∀ c ∈ 𝒜 χ, ε c = 0) {x : C}
    (hx : x ∈ RingHom.ker ε) (χ : Λ) : (decompose 𝒜 x χ : C) ∈ RingHom.ker ε :=
  isHomogeneous_ker hε χ hx

/-- If every derivation at `ε` supported in degree `χ` vanishes, then every element of degree
`χ` in the augmentation ideal `m` lies in `m ^ 2`. -/
theorem mem_ker_sq (hε : ∀ χ ≠ 0, ∀ c ∈ 𝒜 χ, ε c = 0) {χ : Λ} (hD : IsRigidInDegree 𝒜 ε χ)
    {c : C} (hc : c ∈ 𝒜 χ) (hc0 : ε c = 0) : c ∈ RingHom.ker ε ^ 2 := by
  set m := RingHom.ker ε with hm_def
  by_contra hcm
  let p : Submodule k C := (m ^ 2).restrictScalars k ⊓ 𝒜 χ
  have hcp : c ∉ p := fun h => hcm h.1
  obtain ⟨l, hlc, hlp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hcp inferInstance
  have hl : ∀ z ∈ p, l z = 0 := fun z hz => by
    have : l z ∈ p.map l := Submodule.mem_map_of_mem hz
    rwa [hlp, Submodule.mem_bot] at this
  have hsq : (m ^ 2).IsHomogeneous 𝒜 := by
    rw [pow_two]; exact (isHomogeneous_ker hε).mul (isHomogeneous_ker hε)
  let π := GradedAlgebra.proj 𝒜 χ
  have hπ : ∀ z ∈ m ^ 2, π z ∈ p := fun z hz => ⟨hsq χ hz, (decompose 𝒜 z χ).2⟩
  have hsub : ∀ x, x - algebraMap k C (ε x) ∈ m := fun x => by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  let D : C → k := fun x => l (π (x - algebraMap k C (ε x)))
  have hDmul : ∀ x y, D (x * y) = ε x * D y + D x * ε y := fun x y => by
    have hxy : x * y - algebraMap k C (ε (x * y)) =
        (x - algebraMap k C (ε x)) * (y - algebraMap k C (ε y)) +
          ε x • (y - algebraMap k C (ε y)) + ε y • (x - algebraMap k C (ε x)) := by
      rw [map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
      ring
    simp only [D]
    rw [hxy, map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      hl _ (hπ _ ?_), smul_eq_mul, smul_eq_mul, zero_add, mul_comm (l _) (ε y)]
    rw [pow_two]
    exact Ideal.mul_mem_mul (hsub x) (hsub y)
  let φ : C →ₐ[k] DualNumber k :=
    { toFun := fun x => TrivSqZeroExt.inl (ε x) + TrivSqZeroExt.inr (D x)
      map_one' := by
        refine TrivSqZeroExt.ext ?_ ?_
        · simp
        · simp [D]
      map_mul' := fun x y => by
        refine TrivSqZeroExt.ext ?_ ?_
        · simp
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
            TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
            TrivSqZeroExt.fst_inr, zero_add, add_zero, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
            MulOpposite.unop_op, hDmul]
      map_zero' := by
        refine TrivSqZeroExt.ext ?_ ?_
        · simp
        · simp [D]
      map_add' := fun x y => by
        refine TrivSqZeroExt.ext ?_ ?_
        · simp
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
            zero_add, D, map_add, add_sub_add_comm]
      commutes' := fun r => by
        refine TrivSqZeroExt.ext ?_ ?_
        · simp [TrivSqZeroExt.algebraMap_eq_inl]
        · simp [D, TrivSqZeroExt.algebraMap_eq_inl] }
  have hφ : ∀ x, (φ x).snd = D x := fun x => by
    change (TrivSqZeroExt.inl (ε x) + TrivSqZeroExt.inr (D x) : DualNumber k).snd = D x
    simp
  have hfst : (TrivSqZeroExt.fstHom k k k).comp φ = ε := by
    ext x
    change (TrivSqZeroExt.inl (ε x) + TrivSqZeroExt.inr (D x) : DualNumber k).fst = ε x
    simp
  have hsupp : ∀ ψ ≠ χ, ∀ c' ∈ 𝒜 ψ, (φ c').snd = 0 := fun ψ hψ c' hc' => by
    rw [hφ]
    simp only [D, π, map_sub, GradedAlgebra.proj_apply, decompose_of_mem_ne 𝒜 hc' hψ]
    by_cases hχ : χ = 0
    · subst hχ
      simp [hε ψ hψ c' hc']
    · rw [decompose_of_mem_ne 𝒜 (SetLike.algebraMap_mem_graded 𝒜 _) (Ne.symm hχ), map_zero,
        sub_zero]
  apply hlc
  have := hD φ hfst hsupp c
  rw [hφ] at this
  simpa only [D, π, hc0, map_zero, sub_zero, GradedAlgebra.proj_apply,
    decompose_of_mem_same 𝒜 hc] using this

end Helpers

/-- **Vanishing of graded components.** Let `C` be a Noetherian `k`-algebra graded by an
abelian group `Λ`, with an augmentation `ε` killing all components of nonzero degree and
without nontrivial idempotents. Let `P` be an additive subsemigroup of `Λ` not containing
`0`. If, for every `χ ∉ P`, every first-order deformation of `ε` supported in degree `χ` is
trivial, then for `χ ∉ P` every element of degree `χ` in the augmentation ideal is zero. -/
theorem eq_zero_of_notMem {k : Type*} [Field k] {C : Type*} [CommRing C] [Algebra k C]
    [IsNoetherianRing C] {Λ : Type*} [AddCommGroup Λ] [DecidableEq Λ]
    (𝒜 : Λ → Submodule k C) [GradedAlgebra 𝒜] (ε : C →ₐ[k] k)
    (hε : ∀ χ ≠ 0, ∀ c ∈ 𝒜 χ, ε c = 0)
    (hconn : ∀ e : C, IsIdempotentElem e → e = 0 ∨ e = 1)
    (P : AddSubsemigroup Λ) (h0 : (0 : Λ) ∉ P)
    (hD : ∀ χ ∉ P, IsRigidInDegree 𝒜 ε χ) :
    ∀ χ ∉ P, ∀ c ∈ 𝒜 χ, ε c = 0 → c = 0 := by
  classical
  set m := RingHom.ker ε with hm_def
  -- Step 1: degree-`χ` elements of `m` lie in every power of `m`, for `χ ∉ P`.
  have hpow : ∀ n : ℕ, ∀ χ ∉ P, ∀ c ∈ 𝒜 χ, ε c = 0 → c ∈ m ^ (n + 1) := by
    intro n
    induction n with
    | zero => intro χ _ c _ hc0; rw [zero_add, pow_one]; exact hc0
    | succ n ih =>
      have key : ∀ x ∈ m * m, ∀ χ ∉ P, (decompose 𝒜 x χ : C) ∈ m ^ (n + 1 + 1) := by
        intro x hx
        refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y hx hy => ?_)
        · intro χ hχ
          rw [decompose_mul, coe_mul_apply]
          refine Ideal.sum_mem _ fun ij hij => ?_
          rw [Finset.mem_filter] at hij
          have ha' := decompose_mem_ker hε ha ij.1
          have hb' := decompose_mem_ker hε hb ij.2
          by_cases h1 : ij.1 ∈ P
          · have h2 : ij.2 ∉ P := fun h2 => hχ (hij.2 ▸ P.add_mem h1 h2)
            rw [pow_succ']
            exact Ideal.mul_mem_mul ha' (ih _ h2 _ (decompose 𝒜 b ij.2).2 hb')
          · rw [pow_succ]
            exact Ideal.mul_mem_mul (ih _ h1 _ (decompose 𝒜 a ij.1).2 ha') hb'
        · intro χ hχ
          rw [decompose_add, add_apply, Submodule.coe_add]
          exact add_mem (hx χ hχ) (hy χ hχ)
      intro χ hχ c hc hc0
      have hc2 := mem_ker_sq hε (hD χ hχ) hc hc0
      rw [pow_two] at hc2
      have := key c hc2 χ hχ
      rwa [decompose_of_mem_same 𝒜 hc] at this
  -- Step 2: Krull's intersection theorem gives `r ∈ m` fixing `⋂ mⁿ` pointwise.
  let N : Submodule C C := ⨅ i : ℕ, m ^ i • ⊤
  have hN : ∀ j, (m.stableFiltration ⊤ ⊓ m.trivialFiltration N).N j = N :=
    fun j => inf_eq_right.mpr ((iInf_le _ j).trans <| le_of_eq <| by simp)
  obtain ⟨r, hrm, hr⟩ :=
    Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul m N (IsNoetherian.noetherian N) (by
      obtain ⟨j, hj⟩ := (m.stableFiltration_stable ⊤).inter_right (m.trivialFiltration N)
      have := hj j (le_refl _)
      rw [hN, hN] at this
      exact le_of_eq this.symm)
  have hmemN : ∀ χ ∉ P, ∀ c ∈ 𝒜 χ, ε c = 0 → c ∈ N := by
    intro χ hχ c hc hc0
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    cases i with
    | zero => simp
    | succ n => exact hpow n χ hχ c hc hc0
  -- Step 3: the degree-zero part of `r` is an idempotent in `m`, hence zero.
  set r₀ : C := (decompose 𝒜 r 0 : C) with hr₀_def
  have hr₀m : ε r₀ = 0 := decompose_mem_ker hε hrm 0
  have hr₀ : r₀ * r₀ = r₀ := by
    have h := hr r₀ (hmemN 0 h0 r₀ (decompose 𝒜 r 0).2 hr₀m)
    rw [smul_eq_mul] at h
    have h' := congrArg (fun x => (decompose 𝒜 x 0 : C)) h
    simp only at h'
    have hr₀mem : r₀ ∈ 𝒜 0 := (decompose 𝒜 r 0).2
    rw [coe_decompose_mul_of_right_mem_zero 𝒜 hr₀mem, decompose_of_mem_same 𝒜 hr₀mem] at h'
    exact h'
  have hr₀0 : r₀ = 0 := by
    rcases hconn r₀ hr₀ with h | h
    · exact h
    · rw [h, map_one] at hr₀m
      exact absurd hr₀m one_ne_zero
  intro χ hχ c hc hc0
  have h := hr c (hmemN χ hχ c hc hc0)
  rw [smul_eq_mul] at h
  have h' := congrArg (fun x => (decompose 𝒜 x (0 + χ) : C)) h
  simp only at h'
  rw [coe_decompose_mul_add_of_right_mem 𝒜 hc, zero_add, decompose_of_mem_same 𝒜 hc,
    ← hr₀_def, hr₀0, zero_mul] at h'
  exact h'.symm

end Langlands.Algebra.GradedAugmented
