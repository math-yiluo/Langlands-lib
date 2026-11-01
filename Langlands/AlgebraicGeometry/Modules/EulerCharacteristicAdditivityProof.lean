import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicAdditivityStatement
import Langlands.Cohomology.RightDerivedSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

/-! # Proof of additivity of actual cohomological Euler characteristics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

private theorem finite_exact_dimension {K : Type u} [Field K]
    {A B C : ModuleCat.{u} K} [Module.Finite K B]
    {a : A ⟶ B} {b : B ⟶ C} {h : a ≫ b = 0}
    (he : (ShortComplex.mk a b h).Exact) :
    Module.finrank K (LinearMap.range a.hom) +
      Module.finrank K (LinearMap.range b.hom) = Module.finrank K B := by
  have hn := LinearMap.finrank_range_add_finrank_ker b.hom
  rw [← he.moduleCat_range_eq_ker] at hn
  change Module.finrank K (LinearMap.range b.hom) +
    Module.finrank K (LinearMap.range a.hom) = Module.finrank K B at hn
  omega

private theorem alternating_telescope (a b c r : ℕ → ℤ)
    (hzero : r 0 = a 0)
    (hstep : ∀ n, b n + a (n + 1) = r n + c n + r (n + 1))
    (N : ℕ) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (b n - a n - c n)) =
      (-1 : ℤ) ^ N * (a N - r N) := by
  induction N with
  | zero => simp [hzero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      linear_combination (-1 : ℤ) ^ N * hstep N

/-- Additivity for an actual short exact sequence of coefficient sheaves. -/
theorem eulerCharacteristicAdditivity : EulerCharacteristicAdditivityStatement.{u} := by
  intro K _ X f S hS h₁ h₂ h₃
  classical
  let F := relativeGlobalSections f
  let : F.Additive :=
    (inferInstance : ∀ {R : CommRingCat.{u}} (g : X ⟶ Spec R),
      (relativeGlobalSections g).Additive) f
  let (n : ℕ) : Module.Finite K ((F.rightDerived n).obj S.X₁) := h₁.1 n
  let (n : ℕ) : Module.Finite K ((F.rightDerived n).obj S.X₂) := h₂.1 n
  let (n : ℕ) : Module.Finite K ((F.rightDerived n).obj S.X₃) := h₃.1 n
  let a (n : ℕ) : ℤ := Module.finrank K ((F.rightDerived n).obj S.X₁)
  let b (n : ℕ) : ℤ := Module.finrank K ((F.rightDerived n).obj S.X₂)
  let c (n : ℕ) : ℤ := Module.finrank K ((F.rightDerived n).obj S.X₃)
  let r (n : ℕ) : ℤ :=
    Module.finrank K (LinearMap.range ((F.rightDerived n).map S.f).hom)
  have hzero : r 0 = a 0 := by
    have hm := Langlands.Cohomology.DerivedPlus.mono_rightDerived_zero_map F hS
    exact congrArg (fun n : ℕ => (n : ℤ))
      (LinearMap.finrank_range_of_inj (f := ((F.rightDerived 0).map S.f).hom)
        ((ModuleCat.mono_iff_injective _).mp hm))
  have hstep (n : ℕ) : b n + a (n + 1) = r n + c n + r (n + 1) := by
    have hB := finite_exact_dimension
      (Langlands.Cohomology.DerivedPlus.rightDerived_exact₂ F hS n)
    have hC := finite_exact_dimension
      (Langlands.Cohomology.DerivedPlus.rightDerived_exact₃ F hS n (n + 1) rfl)
    have hA := finite_exact_dimension
      (Langlands.Cohomology.DerivedPlus.rightDerived_exact₁ F hS n (n + 1) rfl)
    have hB' := congrArg (fun n : ℕ => (n : ℤ)) hB
    have hC' := congrArg (fun n : ℕ => (n : ℤ)) hC
    have hA' := congrArg (fun n : ℕ => (n : ℤ)) hA
    push_cast at hB' hC' hA'
    dsimp [a, b, c, r]
    linear_combination -hB' - hA' + hC'
  obtain ⟨N₁, hN₁⟩ := h₁.2
  obtain ⟨N₂, hN₂⟩ := h₂.2
  obtain ⟨N₃, hN₃⟩ := h₃.2
  let N := max N₁ (max N₂ N₃)
  have ha : a N = 0 := by
    let : Subsingleton ((F.rightDerived N).obj S.X₁) :=
      ModuleCat.subsingleton_of_isZero (hN₁ N (by omega))
    simp [a, Module.finrank_zero_of_subsingleton]
  have hr : r N = 0 := by
    let : Subsingleton ((F.rightDerived N).obj S.X₁) :=
      ModuleCat.subsingleton_of_isZero (hN₁ N (by omega))
    have hz : ((F.rightDerived N).map S.f).hom = 0 :=
      Subsingleton.elim _ _
    simp [r, hz]
  have hsum := alternating_telescope a b c r hzero hstep N
  rw [ha, hr, sub_self, mul_zero] at hsum
  have hcut (M : X.Modules) (hM : HasFiniteCohomology f M)
      (hN : ∀ n : ℕ, N ≤ n → IsZero ((relativeCohomology f n).obj M)) :
      eulerCharacteristic f M hM = ∑ n ∈ Finset.range N,
        (-1 : ℤ) ^ n * (Module.finrank K ((relativeCohomology f n).obj M) : ℤ) := by
    apply finsum_eq_sum_of_support_subset
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hlt
    let : Subsingleton ((relativeCohomology f n).obj M) :=
      ModuleCat.subsingleton_of_isZero (hN n (by omega))
    exact hn (by simp [Module.finrank_zero_of_subsingleton])
  rw [hcut S.X₁ h₁ (fun n hn => hN₁ n (by omega)),
    hcut S.X₂ h₂ (fun n hn => hN₂ n (by omega)),
    hcut S.X₃ h₃ (fun n hn => hN₃ n (by omega))]
  dsimp [a, b, c, F] at hsum
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hsum)).trans (add_comm _ _)

end Langlands.AlgebraicGeometry.Modules.DerivedSections
