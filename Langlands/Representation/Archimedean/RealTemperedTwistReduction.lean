import Langlands.Representation.Archimedean.RealTemperedTwist

/-!
# Irreducibility transport under real determinant twists

Determinant twisting preserves the simultaneous compact and complexified Lie
invariant subspaces. Thus the equal-real-exponent irreducibility statement
reduces to lists whose real block exponents are zero.
-/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

namespace RealTemperedTwist

open InductionStages

variable {n : ℕ}

/-- Every complexified Lie operator changes by a scalar under the twist. -/
theorem twistEquiv_lie_shift (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n)
    (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    ∃ c : ℂ, ∀ f : KFin n ds,
      realStandardLie n (ds.map (realBlockTwist s)) Z (twistEquiv s ds hr f) =
        twistEquiv s ds hr (realStandardLie n ds Z f) + c • twistEquiv s ds hr f := by
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
      refine ⟨z * rightDerivative (matrixModel ℝ n) X
        (RealLinkedJacquetStages.detPow n (s : ℂ)) (1 : Langlands.GeneralLinear n ℝ),
        fun f => ?_⟩
      have h (es : List RealBlock) :
          realStandardLie n es (z ⊗ₜ X) = z • realStandardLie n es (1 ⊗ₜ X) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, h, LinearMap.smul_apply, LinearMap.smul_apply, twistEquiv_lie,
        map_smul, smul_add, smul_smul]
  | add Z₁ Z₂ h₁ h₂ =>
      obtain ⟨c₁, hc₁⟩ := h₁
      obtain ⟨c₂, hc₂⟩ := h₂
      refine ⟨c₁ + c₂, fun f => ?_⟩
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hc₁, hc₂,
        map_add, add_smul]
      abel

/-- Simultaneous compact and Lie invariance for the actual standard module. -/
def IsStable (n : ℕ) (ds : List RealBlock) (U : Submodule ℂ (KFin n ds)) : Prop :=
  (∀ (k : Matrix.unitaryGroup (Fin n) ℝ), ∀ f ∈ U, realStandardRep n ds k f ∈ U) ∧
    ∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ f ∈ U, realStandardLie n ds Z f ∈ U

/-- The twist sends invariant subspaces to invariant subspaces. -/
theorem isStable_map (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n)
    (U : Submodule ℂ (KFin n ds)) (hU : IsStable n ds U) :
    IsStable n (ds.map (realBlockTwist s)) (U.map (twistEquiv s ds hr).toLinearMap) := by
  constructor
  · rintro k _ ⟨f, hf, rfl⟩
    exact ⟨realStandardRep n ds k f, hU.1 k f hf, twistEquiv_rep s ds hr k f⟩
  · rintro Z _ ⟨f, hf, rfl⟩
    obtain ⟨c, hc⟩ := twistEquiv_lie_shift s ds hr Z
    change realStandardLie n (ds.map (realBlockTwist s)) Z (twistEquiv s ds hr f) ∈ _
    rw [hc]
    exact Submodule.add_mem _ ⟨realStandardLie n ds Z f, hU.2 Z f hf, rfl⟩
      (Submodule.smul_mem _ c ⟨f, hf, rfl⟩)

/-- The inverse twist also preserves invariant subspaces. -/
theorem isStable_comap (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n)
    (U : Submodule ℂ (KFin n (ds.map (realBlockTwist s))))
    (hU : IsStable n (ds.map (realBlockTwist s)) U) :
    IsStable n ds (U.comap (twistEquiv s ds hr).toLinearMap) := by
  constructor
  · intro k f hf
    change twistEquiv s ds hr (realStandardRep n ds k f) ∈ U
    rw [twistEquiv_rep]
    exact hU.1 k _ hf
  · intro Z f hf
    change twistEquiv s ds hr (realStandardLie n ds Z f) ∈ U
    obtain ⟨c, hc⟩ := twistEquiv_lie_shift s ds hr Z
    have heq : twistEquiv s ds hr (realStandardLie n ds Z f) =
        realStandardLie n (ds.map (realBlockTwist s)) Z (twistEquiv s ds hr f) -
          c • twistEquiv s ds hr f := by
      rw [hc, add_sub_cancel_right]
    rw [heq]
    exact U.sub_mem (hU.2 Z _ hf) (U.smul_mem c hf)

/-- A real determinant twist preserves irreducibility. -/
theorem isIrreducible_twist_iff (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n) :
    IsIrreducibleGKModule
        (realStandardRep n (ds.map (realBlockTwist s)))
        (realStandardLie n (ds.map (realBlockTwist s))) ↔
      IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) := by
  let e := twistEquiv s ds hr
  constructor
  · intro h
    let := h.1
    refine ⟨e.toEquiv.nontrivial, fun U hUK hUL => ?_⟩
    have hstable := isStable_map s ds hr U ⟨hUK, hUL⟩
    have hU := h.2 (U.map e.toLinearMap) hstable.1 hstable.2
    simpa only [Submodule.map_eq_bot_iff, Submodule.map_eq_top_iff] using hU
  · intro h
    let := h.1
    refine ⟨e.symm.toEquiv.nontrivial, fun U hUK hUL => ?_⟩
    have hstable := isStable_comap s ds hr U ⟨hUK, hUL⟩
    rcases h.2 (U.comap e.toLinearMap) hstable.1 hstable.2 with h0 | htop
    · left
      apply Submodule.comap_injective_of_surjective e.surjective
      simpa only [Submodule.comap_bot, LinearEquiv.ker] using h0
    · right
      apply Submodule.comap_injective_of_surjective e.surjective
      simpa only [Submodule.comap_top] using htop

end RealTemperedTwist

/-- The remaining irreducibility problem after removing the common real
determinant exponent. This proposition is not proved here. -/
def RealZeroExponentStandardIrreducibleStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    (∀ x ∈ ds, realBlockExponent x = 0) →
      IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds)

/-- Lists with equal real block exponents reduce to the zero-exponent case,
including the empty list. -/
theorem realTemperedStandardIrreducible_of_zeroExponent
    (hzero : RealZeroExponentStandardIrreducibleStatement) :
    RealTemperedStandardIrreducibleStatement := by
  intro n ds hr he
  cases ds with
  | nil => exact hzero n [] hr (by simp)
  | cons x xs =>
      let s := -realBlockExponent x
      apply (RealTemperedTwist.isIrreducible_twist_iff s (x :: xs) hr).mp
      apply hzero n ((x :: xs).map (realBlockTwist s))
      · rw [realRank_map_realBlockTwist, hr]
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        rw [realBlockExponent_twist, he z hz x (by simp)]
        simp [s]

/-- Normalization is an equivalence of the two irreducibility statements. -/
theorem realTemperedStandardIrreducible_iff_zeroExponent :
    RealTemperedStandardIrreducibleStatement ↔
      RealZeroExponentStandardIrreducibleStatement := by
  refine ⟨?_, realTemperedStandardIrreducible_of_zeroExponent⟩
  intro h n ds hr hz
  exact h n ds hr (fun x hx y hy => (hz x hx).trans (hz y hy).symm)

end Langlands.Archimedean
