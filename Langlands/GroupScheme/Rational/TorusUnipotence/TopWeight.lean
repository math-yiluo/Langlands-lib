import Langlands.GroupScheme.AffineLinearEmbedding.Comodule
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Fixed vectors of matrix corepresentations of a graded coalgebra -/

noncomputable section

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.TorusUnipotence

open Langlands.GroupScheme.AffineLinearEmbedding

variable {K : Type*} [Field K] {B : Type*} [AddCommGroup B] [Module K B]

section Projection

variable {Γ : Type*} [DecidableEq Γ] (𝒜 : Γ → Submodule K B) [DirectSum.Decomposition 𝒜]

/-- The projection of `B` onto the graded piece `𝒜 χ`. -/
def gradedProj (χ : Γ) : B →ₗ[K] B :=
  (𝒜 χ).subtype ∘ₗ DirectSum.component K Γ (fun χ => 𝒜 χ) χ ∘ₗ
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

variable {𝒜}

theorem gradedProj_apply (χ : Γ) (b : B) :
    gradedProj 𝒜 χ b = (DirectSum.decompose 𝒜 b χ : B) := rfl

theorem gradedProj_mem (χ : Γ) (b : B) : gradedProj 𝒜 χ b ∈ 𝒜 χ :=
  (DirectSum.decompose 𝒜 b χ).2

theorem gradedProj_of_mem {χ : Γ} {b : B} (hb : b ∈ 𝒜 χ) : gradedProj 𝒜 χ b = b :=
  DirectSum.decompose_of_mem_same 𝒜 hb

theorem gradedProj_of_mem_ne {χ ψ : Γ} {b : B} (hb : b ∈ 𝒜 χ) (h : χ ≠ ψ) :
    gradedProj 𝒜 ψ b = 0 :=
  DirectSum.decompose_of_mem_ne 𝒜 hb h

theorem gradedProj_gradedProj (χ ψ : Γ) (b : B) :
    gradedProj 𝒜 ψ (gradedProj 𝒜 χ b) = if χ = ψ then gradedProj 𝒜 χ b else 0 := by
  split_ifs with h
  · subst h; exact gradedProj_of_mem (gradedProj_mem χ b)
  · exact gradedProj_of_mem_ne (gradedProj_mem χ b) h

theorem exists_gradedProj_eq_zero (b : B) : ∃ s : Finset Γ, ∀ χ ∉ s, gradedProj 𝒜 χ b = 0 := by
  classical
  refine ⟨(DirectSum.decompose 𝒜 b).support, fun χ hχ => ?_⟩
  rw [DFinsupp.notMem_support_iff] at hχ
  rw [gradedProj_apply, hχ, ZeroMemClass.coe_zero]

theorem sum_gradedProj {b : B} {s : Finset Γ} (hs : ∀ χ ∉ s, gradedProj 𝒜 χ b = 0) :
    ∑ χ ∈ s, gradedProj 𝒜 χ b = b := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 b]
  symm
  refine Finset.sum_subset (fun χ hχ => ?_) (fun χ _ hχ => ?_)
  · by_contra h
    rw [DFinsupp.mem_support_iff] at hχ
    exact hχ (Subtype.ext (hs χ h))
  · rw [DFinsupp.notMem_support_iff] at hχ
    rw [hχ, ZeroMemClass.coe_zero]

variable {n : Type*}

variable (𝒜 n) in
/-- The projection of `n → B` onto the coordinatewise graded piece of degree `χ`. -/
def gradedProjPi (χ : Γ) : (n → B) →ₗ[K] (n → B) := (gradedProj 𝒜 χ).compLeft n

@[simp] theorem gradedProjPi_apply (χ : Γ) (x : n → B) (i : n) :
    gradedProjPi 𝒜 n χ x i = gradedProj 𝒜 χ (x i) := rfl

variable (𝒜) in
/-- A subspace of `n → B` is graded if it is closed under all the graded projections. -/
def IsGradedPi (W : Submodule K (n → B)) : Prop :=
  ∀ χ : Γ, W ≤ W.comap (gradedProjPi 𝒜 n χ)

theorem gradedProjPi_of_mem {N : Γ} {x : n → B} (hx : ∀ i, x i ∈ 𝒜 N) :
    gradedProjPi 𝒜 n N x = x := by
  ext i
  exact gradedProj_of_mem (hx i)

theorem gradedProjPi_of_mem_ne {N χ : Γ} {x : n → B} (hx : ∀ i, x i ∈ 𝒜 N) (h : N ≠ χ) :
    gradedProjPi 𝒜 n χ x = 0 := by
  ext i
  exact gradedProj_of_mem_ne (hx i) h

theorem gradedProjPi_mem (χ : Γ) (x : n → B) (i : n) : gradedProjPi 𝒜 n χ x i ∈ 𝒜 χ :=
  gradedProj_mem χ (x i)

theorem gradedProjPi_gradedProjPi (χ : Γ) (x : n → B) :
    gradedProjPi 𝒜 n χ (gradedProjPi 𝒜 n χ x) = gradedProjPi 𝒜 n χ x :=
  gradedProjPi_of_mem (gradedProjPi_mem χ x)

theorem exists_gradedProjPi_eq_zero [Finite n] (x : n → B) :
    ∃ s : Finset Γ, ∀ χ ∉ s, gradedProjPi 𝒜 n χ x = 0 := by
  classical
  have := Fintype.ofFinite n
  choose s hs using fun i => exists_gradedProj_eq_zero (𝒜 := 𝒜) (x i)
  refine ⟨Finset.univ.biUnion s, fun χ hχ => ?_⟩
  ext i
  exact hs i χ fun h => hχ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)

theorem sum_gradedProjPi {x : n → B} {s : Finset Γ}
    (hs : ∀ χ ∉ s, gradedProjPi 𝒜 n χ x = 0) : ∑ χ ∈ s, gradedProjPi 𝒜 n χ x = x := by
  ext i
  rw [Finset.sum_apply]
  exact sum_gradedProj fun χ hχ => congrFun (hs χ hχ) i

theorem exists_support_of_finiteDimensional [Finite n] (W : Submodule K (n → B))
    [FiniteDimensional K W] : ∃ s : Finset Γ, ∀ x ∈ W, ∀ χ ∉ s, gradedProjPi 𝒜 n χ x = 0 := by
  classical
  obtain ⟨T, hT⟩ := (Submodule.fg_iff_finiteDimensional W).mpr inferInstance
  choose s hs using exists_gradedProjPi_eq_zero (𝒜 := 𝒜) (n := n)
  refine ⟨T.biUnion s, fun x hx χ hχ => ?_⟩
  rw [← hT] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs y χ fun h => hχ (Finset.mem_biUnion.mpr ⟨y, hy, h⟩)
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

end Projection

section Coalgebra

variable [Coalgebra K B] {Γ : Type*} [DecidableEq Γ] [AddCommGroup Γ] {𝒜 : Γ → Submodule K B}
  [DirectSum.Decomposition 𝒜]

omit [DecidableEq Γ] [DirectSum.Decomposition 𝒜] in
/-- Linear maps on `B ⊗ B` that agree on `𝒜 α ⊗ 𝒜 (χ - α)` for every `α` agree on the
comultiplication of every element of `𝒜 χ`, when the comultiplication is graded. -/
theorem map_comul_eq_of_mem
    (hΔ : ∀ χ, ∀ a ∈ 𝒜 χ, comul (R := K) a ∈
      ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α)))
    {χ : Γ} {a : B} (ha : a ∈ 𝒜 χ) {P : Type*} [AddCommGroup P] [Module K P]
    (f g : B ⊗[K] B →ₗ[K] P)
    (h : ∀ α, ∀ x ∈ 𝒜 α, ∀ y ∈ 𝒜 (χ - α), f (x ⊗ₜ y) = g (x ⊗ₜ y)) :
    f (comul a) = g (comul a) := by
  have hle : (⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α))) ≤
      LinearMap.eqLocus f g :=
    iSup_le fun α => Submodule.map₂_le.mpr fun x hx y hy => h α x hx y hy
  exact hle (hΔ χ a ha)

/-- The degree `χ` part of a right translate of a homogeneous element of degree `N`. -/
theorem gradedProj_rightAct
    (hΔ : ∀ χ, ∀ a ∈ 𝒜 χ, comul (R := K) a ∈
      ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α)))
    {N : Γ} {a : B} (ha : a ∈ 𝒜 N) (χ : Γ) (m : Module.Dual K B) :
    gradedProj 𝒜 χ (rightAct m a) = rightAct (m ∘ₗ gradedProj 𝒜 (N - χ)) a := by
  rw [rightAct_apply, rightAct_apply]
  refine map_comul_eq_of_mem hΔ ha
    (gradedProj 𝒜 χ ∘ₗ (TensorProduct.rid K B).toLinearMap ∘ₗ m.lTensor B)
    ((TensorProduct.rid K B).toLinearMap ∘ₗ (m ∘ₗ gradedProj 𝒜 (N - χ)).lTensor B)
    fun α x hx y hy => ?_
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul, map_smul]
  by_cases h : α = χ
  · subst h
    rw [gradedProj_of_mem hx, gradedProj_of_mem hy]
  · rw [gradedProj_of_mem_ne hx h, gradedProj_of_mem_ne hy fun h' => h (sub_right_inj.mp h'),
      map_zero, zero_smul, smul_zero]

/-- A left translate of a homogeneous element of degree `N` by a functional supported in
degree `N` has degree `0`. -/
theorem leftAct_mem_zero
    (hΔ : ∀ χ, ∀ a ∈ 𝒜 χ, comul (R := K) a ∈
      ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α)))
    {N : Γ} {a : B} (ha : a ∈ 𝒜 N) (φ : Module.Dual K B)
    (hφ : ∀ χ, χ ≠ N → ∀ b ∈ 𝒜 χ, φ b = 0) : leftAct φ a ∈ 𝒜 0 := by
  have key : gradedProj 𝒜 0 (leftAct φ a) = leftAct φ a := by
    rw [leftAct_apply]
    refine map_comul_eq_of_mem hΔ ha
      (gradedProj 𝒜 0 ∘ₗ (TensorProduct.lid K B).toLinearMap ∘ₗ φ.rTensor B)
      ((TensorProduct.lid K B).toLinearMap ∘ₗ φ.rTensor B) fun α x hx y hy => ?_
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul, map_smul]
    by_cases h : α = N
    · subst h
      rw [sub_self] at hy
      rw [gradedProj_of_mem hy]
    · rw [hφ α h x hx, zero_smul, zero_smul]
  rw [← key]
  exact gradedProj_mem 0 _

theorem rightAct_of_comul_eq {e : B} (he : comul (R := K) e = e ⊗ₜ e) (m : Module.Dual K B) :
    rightAct m e = m e • e := by
  rw [rightAct_apply, he, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

end Coalgebra

section Pi

variable [Coalgebra K B] {n : Type*}

variable (n) in
/-- Right translation by a functional, applied to every coordinate of `n → B`. -/
def rightActPi (m : Module.Dual K B) : (n → B) →ₗ[K] (n → B) := (rightAct m).compLeft n

@[simp] theorem rightActPi_apply (m : Module.Dual K B) (x : n → B) (i : n) :
    rightActPi n m x i = rightAct m (x i) := rfl

theorem rightActPi_rightActPi (g f : Module.Dual K B) (x : n → B) :
    rightActPi n g (rightActPi n f x) = rightActPi n (g ∘ₗ rightAct f) x := by
  ext i
  simp [rightAct_rightAct]

@[simp] theorem rightActPi_counit (x : n → B) : rightActPi n (counit (R := K)) x = x := by
  ext i
  simp

/-- A subspace of `n → B` is stable if it is closed under all right translations. -/
def IsStablePi (W : Submodule K (n → B)) : Prop :=
  ∀ m : Module.Dual K B, W ≤ W.comap (rightActPi n m)

variable {Γ : Type*} [DecidableEq Γ] [AddCommGroup Γ] {𝒜 : Γ → Submodule K B}
  [DirectSum.Decomposition 𝒜]

theorem gradedProjPi_rightActPi
    (hΔ : ∀ χ, ∀ a ∈ 𝒜 χ, comul (R := K) a ∈
      ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α)))
    {N : Γ} {x : n → B} (hx : ∀ i, x i ∈ 𝒜 N) (χ : Γ) (m : Module.Dual K B) :
    gradedProjPi 𝒜 n χ (rightActPi n m x) = rightActPi n (m ∘ₗ gradedProj 𝒜 (N - χ)) x := by
  ext i
  exact gradedProj_rightAct hΔ (hx i) χ m

/-- The degree `χ` part of `rightAct l x - l e • x` for `x` homogeneous of degree `N` and `e`
of degree `0` has the same form, with `l` replaced by `l ∘ gradedProj (N - χ)`. -/
theorem gradedProjPi_rightActPi_sub
    (hΔ : ∀ χ, ∀ a ∈ 𝒜 χ, comul (R := K) a ∈
      ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α)))
    {e : B} (he0 : e ∈ 𝒜 0) {N : Γ} {x : n → B} (hx : ∀ i, x i ∈ 𝒜 N) (χ : Γ)
    (l : Module.Dual K B) :
    gradedProjPi 𝒜 n χ (rightActPi n l x - l e • x) =
      rightActPi n (l ∘ₗ gradedProj 𝒜 (N - χ)) x - (l ∘ₗ gradedProj 𝒜 (N - χ)) e • x := by
  rw [map_sub, map_smul, gradedProjPi_rightActPi hΔ hx, LinearMap.comp_apply]
  by_cases h : N = χ
  · subst h
    rw [gradedProjPi_of_mem hx, sub_self, gradedProj_of_mem he0]
  · rw [gradedProjPi_of_mem_ne hx h, gradedProj_of_mem_ne he0 fun h' => h (sub_eq_zero.mp h'.symm),
      map_zero, zero_smul, smul_zero]

theorem rightActPi_rightActPi_sub {e : B} (he : comul (R := K) e = e ⊗ₜ e)
    (m l : Module.Dual K B) (x : n → B) :
    rightActPi n m (rightActPi n l x - l e • x) =
      (rightActPi n (m ∘ₗ rightAct l) x - (m ∘ₗ rightAct l) e • x) -
        l e • (rightActPi n m x - m e • x) := by
  rw [map_sub, map_smul, rightActPi_rightActPi, LinearMap.comp_apply, rightAct_of_comul_eq he,
    map_smul, smul_sub, smul_smul, smul_eq_mul]
  abel

end Pi

section TopWeight

variable [Coalgebra K B] {n : Type*} [Fintype n] {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] {𝒜 : Γ → Submodule K B} [DirectSum.Decomposition 𝒜]

/-- The core top-weight lemma. Let `W' ⊆ W` be stable subspaces of `n → B` with `W'` graded,
such that every component of `W` of degree `> N` lies in `W'`. For `x ∈ W` homogeneous of degree
`N`, the degree `N` part of `rightAct l x - l e • x` lies in `W'`. -/
theorem gradedProjPi_mem_of_top
    (hΔ : ∀ χ, ∀ a ∈ 𝒜 χ, comul (R := K) a ∈
      ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α)))
    {e : B} (hεe : counit (R := K) e = 1)
    (hrigid : ∀ a ∈ 𝒜 0, (∀ m : Module.Dual K B, (∀ χ, 0 ≤ χ → ∀ b ∈ 𝒜 χ, m b = 0) →
      rightAct m a = 0) → ∃ c : K, a = c • e)
    {W W' : Submodule K (n → B)} (hWst : IsStablePi W) (hW'gr : IsGradedPi 𝒜 W')
    (hW'st : IsStablePi W') {N : Γ} (htop : ∀ χ, N < χ → ∀ y ∈ W, gradedProjPi 𝒜 n χ y ∈ W')
    {x : n → B} (hxW : x ∈ W) (hx : ∀ i, x i ∈ 𝒜 N) (l : Module.Dual K B) :
    gradedProjPi 𝒜 n N (rightActPi n l x - l e • x) ∈ W' := by
  classical
  set z := gradedProjPi 𝒜 n N (rightActPi n l x - l e • x) with hz_def
  by_contra hz
  let U : Submodule K (n → B) := W'.comap (gradedProjPi 𝒜 n N)
  have hzU : z ∉ U := by
    change gradedProjPi 𝒜 n N z ∉ W'
    rwa [hz_def, gradedProjPi_gradedProjPi]
  obtain ⟨φ, hφz, hφU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzU inferInstance
  have hφ : ∀ y ∈ U, φ y = 0 := fun y hy => by
    have : φ y ∈ U.map φ := Submodule.mem_map_of_mem hy
    rwa [hφU, Submodule.mem_bot] at this
  have hW'U : ∀ y ∈ W', y ∈ U := fun y hy => hW'gr N hy
  have hzeroU : ∀ y, gradedProjPi 𝒜 n N y = 0 → y ∈ U := fun y hy => by
    change gradedProjPi 𝒜 n N y ∈ W'
    rw [hy]
    exact W'.zero_mem
  let φi : n → Module.Dual K B := fun i => φ ∘ₗ LinearMap.single K (fun _ => B) i
  have hφsum : ∀ y : n → B, φ y = ∑ i, φi i (y i) := fun y => by
    conv_lhs => rw [← Finset.univ_sum_single y]
    simp [φi]
  have hφi : ∀ i χ, χ ≠ N → ∀ b ∈ 𝒜 χ, φi i b = 0 := fun i χ hχ b hb => by
    refine hφ _ (hzeroU _ ?_)
    ext j
    rw [gradedProjPi_apply]
    by_cases hij : j = i
    · subst hij
      simp [gradedProj_of_mem_ne hb hχ]
    · simp [hij]
  let a : B := ∑ i, leftAct (φi i) (x i)
  have ha0 : a ∈ 𝒜 0 := Submodule.sum_mem _ fun i _ => leftAct_mem_zero hΔ (hx i) _ (hφi i)
  have hga : ∀ g : Module.Dual K B, g a = φ (rightActPi n g x) := fun g => by
    simp only [a, map_sum, apply_leftAct, hφsum, rightActPi_apply]
  have hrig : ∀ m : Module.Dual K B, (∀ χ, 0 ≤ χ → ∀ b ∈ 𝒜 χ, m b = 0) →
      rightAct m a = 0 := by
    intro m hm
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro g
    have hy : rightActPi n m x ∈ W' := by
      have hyW := hWst m hxW
      obtain ⟨s, hs⟩ := exists_gradedProjPi_eq_zero (𝒜 := 𝒜) (rightActPi n m x)
      rw [← sum_gradedProjPi hs]
      refine Submodule.sum_mem _ fun χ _ => ?_
      rcases le_or_gt χ N with h | h
      · rw [gradedProjPi_rightActPi hΔ hx]
        convert W'.zero_mem
        ext i
        have : m ∘ₗ gradedProj 𝒜 (N - χ) = 0 := by
          ext b
          exact hm _ (sub_nonneg.mpr h) _ (gradedProj_mem _ _)
        simp [this, rightAct_apply]
      · exact htop χ h _ hyW
    rw [← LinearMap.comp_apply, hga, ← rightActPi_rightActPi]
    exact hφ _ (hW'U _ (hW'st g hy))
  obtain ⟨c, hc⟩ := hrigid a ha0 hrig
  have hφx : φ x = c := by
    have := hga counit
    rw [rightActPi_counit, hc, map_smul, hεe, smul_eq_mul, mul_one] at this
    exact this.symm
  apply hφz
  have hzφ : φ z = φ (rightActPi n l x - l e • x) := by
    rw [← sub_eq_zero, ← map_sub]
    apply hφ
    apply hzeroU
    rw [map_sub, hz_def, gradedProjPi_gradedProjPi, sub_self]
  rw [hzφ, map_sub, map_smul, ← hga, hc, hφx, map_smul, smul_eq_mul, smul_eq_mul, mul_comm,
    sub_self]

/-- Relative top-weight lemma: if `W' < W` are graded stable subspaces of `n → B` with `W`
finite-dimensional (of dimension `d`), then some homogeneous `x ∈ W \ W'` has every
`rightAct l x - l e • x` in `W'`. -/
theorem exists_relative_coinvariant
    (hΔ : ∀ χ, ∀ a ∈ 𝒜 χ, comul (R := K) a ∈
      ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α)))
    {e : B} (he : comul (R := K) e = e ⊗ₜ e) (hεe : counit (R := K) e = 1) (he0 : e ∈ 𝒜 0)
    (hrigid : ∀ a ∈ 𝒜 0, (∀ m : Module.Dual K B, (∀ χ, 0 ≤ χ → ∀ b ∈ 𝒜 χ, m b = 0) →
      rightAct m a = 0) → ∃ c : K, a = c • e)
    (d : ℕ) : ∀ (W W' : Submodule K (n → B)) [FiniteDimensional K W], finrank K W = d →
      IsGradedPi 𝒜 W → IsStablePi W → IsGradedPi 𝒜 W' → IsStablePi W' → W' < W →
      ∃ x ∈ W, x ∉ W' ∧ (∃ N : Γ, ∀ i, x i ∈ 𝒜 N) ∧
        ∀ l : Module.Dual K B, rightActPi n l x - l e • x ∈ W' := by
  classical
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W W' _ hd hWgr hWst hW'gr hW'st hlt
  obtain ⟨s₀, hs₀⟩ := exists_support_of_finiteDimensional (𝒜 := 𝒜) W
  set T := s₀.filter (fun χ => ∃ y ∈ W, gradedProjPi 𝒜 n χ y ∉ W') with hT_def
  have hT : T.Nonempty := by
    obtain ⟨y, hyW, hyW'⟩ := SetLike.exists_of_lt hlt
    by_contra hT'
    apply hyW'
    rw [← sum_gradedProjPi (hs₀ y hyW)]
    refine Submodule.sum_mem _ fun χ hχ => ?_
    by_contra h
    exact hT' ⟨χ, Finset.mem_filter.mpr ⟨hχ, y, hyW, h⟩⟩
  obtain ⟨N, hNT, hNmax⟩ := T.exists_max_image id hT
  obtain ⟨-, y₀, hy₀W, hy₀⟩ := Finset.mem_filter.mp hNT
  have htop : ∀ χ, N < χ → ∀ y ∈ W, gradedProjPi 𝒜 n χ y ∈ W' := by
    intro χ hχ y hy
    by_contra h
    by_cases hχs : χ ∈ s₀
    · exact absurd (hNmax χ (Finset.mem_filter.mpr ⟨hχs, y, hy, h⟩)) (not_le.mpr hχ)
    · exact h (by rw [hs₀ y hy χ hχs]; exact W'.zero_mem)
  let S : Set ((n → B) × Module.Dual K B) := {p | p.1 ∈ W ∧ ∀ i, p.1 i ∈ 𝒜 N}
  let gen : (n → B) × Module.Dual K B → (n → B) := fun p => rightActPi n p.2 p.1 - p.2 e • p.1
  let G : Submodule K (n → B) := Submodule.span K (gen '' S)
  have hgenG : ∀ x ∈ W, (∀ i, x i ∈ 𝒜 N) → ∀ l : Module.Dual K B,
      rightActPi n l x - l e • x ∈ G :=
    fun x hxW hx l => Submodule.subset_span ⟨(x, l), ⟨hxW, hx⟩, rfl⟩
  have hGW : G ≤ W := Submodule.span_le.mpr (by
    rintro _ ⟨⟨x, l⟩, ⟨hxW, -⟩, rfl⟩
    exact W.sub_mem (hWst l hxW) (W.smul_mem _ hxW))
  have hGgr : IsGradedPi 𝒜 G := fun χ => Submodule.span_le.mpr (by
    rintro _ ⟨⟨x, l⟩, ⟨hxW, hx⟩, rfl⟩
    change gradedProjPi 𝒜 n χ (rightActPi n l x - l e • x) ∈ G
    rw [gradedProjPi_rightActPi_sub hΔ he0 hx]
    exact hgenG x hxW hx _)
  have hGst : IsStablePi G := fun m => Submodule.span_le.mpr (by
    rintro _ ⟨⟨x, l⟩, ⟨hxW, hx⟩, rfl⟩
    change rightActPi n m (rightActPi n l x - l e • x) ∈ G
    rw [rightActPi_rightActPi_sub he]
    exact G.sub_mem (hgenG x hxW hx _) (G.smul_mem _ (hgenG x hxW hx _)))
  have hGN : G ≤ W'.comap (gradedProjPi 𝒜 n N) := Submodule.span_le.mpr (by
    rintro _ ⟨⟨x, l⟩, ⟨hxW, hx⟩, rfl⟩
    exact gradedProjPi_mem_of_top hΔ hεe hrigid hWst hW'gr hW'st htop hxW hx l)
  set x₀ := gradedProjPi 𝒜 n N y₀ with hx₀_def
  have hx₀W : x₀ ∈ W := hWgr N hy₀W
  have hx₀ : ∀ i, x₀ i ∈ 𝒜 N := gradedProjPi_mem N y₀
  by_cases hGW' : G ≤ W'
  · exact ⟨x₀, hx₀W, hy₀, ⟨N, hx₀⟩, fun l => hGW' (hgenG x₀ hx₀W hx₀ l)⟩
  · let C := W' ⊔ G
    have hCW : C ≤ W := sup_le hlt.le hGW
    have hx₀C : x₀ ∉ C := by
      intro h
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h
      apply hy₀
      have : gradedProjPi 𝒜 n N (y + z) = x₀ := by rw [hyz, hx₀_def, gradedProjPi_gradedProjPi]
      rw [← this, map_add]
      exact W'.add_mem (hW'gr N hy) (hGN hz)
    have hCltW : C < W := lt_of_le_of_ne hCW fun h => hx₀C (h.ge hx₀W)
    have hW'C : W' < C := lt_of_le_of_ne le_sup_left fun h => hGW' (le_sup_right.trans h.ge)
    have : FiniteDimensional K C := Submodule.finiteDimensional_of_le hCW
    have hCgr : IsGradedPi 𝒜 C := fun χ =>
      sup_le ((hW'gr χ).trans (Submodule.comap_mono le_sup_left))
        ((hGgr χ).trans (Submodule.comap_mono le_sup_right))
    have hCst : IsStablePi C := fun m =>
      sup_le ((hW'st m).trans (Submodule.comap_mono le_sup_left))
        ((hGst m).trans (Submodule.comap_mono le_sup_right))
    obtain ⟨x, hxC, hxW', hxN, hgen⟩ :=
      ih (finrank K C) (hd ▸ Submodule.finrank_lt_finrank_of_lt hCltW) C W' rfl hCgr hCst
        hW'gr hW'st hW'C
    exact ⟨x, hCW hxC, hxW', hxN, hgen⟩

/-- Every nonzero stable subspace `V` of a finite-dimensional graded stable subspace `W₀` of
`n → B` contains a nonzero vector `v` with `rightAct l v = l e • v` for every functional `l`. -/
theorem exists_coinvariant
    (hΔ : ∀ χ, ∀ a ∈ 𝒜 χ, comul (R := K) a ∈
      ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α)))
    {e : B} (he : comul (R := K) e = e ⊗ₜ e) (hεe : counit (R := K) e = 1) (he0 : e ∈ 𝒜 0)
    (hrigid : ∀ a ∈ 𝒜 0, (∀ m : Module.Dual K B, (∀ χ, 0 ≤ χ → ∀ b ∈ 𝒜 χ, m b = 0) →
      rightAct m a = 0) → ∃ c : K, a = c • e)
    {W₀ V : Submodule K (n → B)} [FiniteDimensional K W₀] (hW₀gr : IsGradedPi 𝒜 W₀)
    (hW₀st : IsStablePi W₀) (hVst : IsStablePi V) (hVW₀ : V ≤ W₀) (hV : V ≠ ⊥) :
    ∃ v ∈ V, v ≠ 0 ∧ ∀ l : Module.Dual K B, rightActPi n l v = l e • v := by
  classical
  let P : ℕ → Prop := fun d => ∃ W' : Submodule K (n → B), W' ≤ W₀ ∧ IsGradedPi 𝒜 W' ∧
    IsStablePi W' ∧ V ⊓ W' = ⊥ ∧ finrank K W' = d
  have hP0 : P 0 :=
    ⟨⊥, bot_le, fun _ => bot_le, fun _ => bot_le, inf_bot_eq _, finrank_bot K _⟩
  obtain ⟨W', hW'W₀, hW'gr, hW'st, hVW', hd⟩ :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le (finrank K W₀)) hP0
  have hlt : W' < W₀ := lt_of_le_of_ne hW'W₀ fun h => hV (by
    rw [h, inf_eq_left.mpr hVW₀] at hVW'
    exact hVW')
  obtain ⟨x, hxW₀, hxW', ⟨N, hxN⟩, hgen⟩ :=
    exists_relative_coinvariant hΔ he hεe he0 hrigid _ W₀ W' rfl hW₀gr hW₀st hW'gr hW'st hlt
  let W'' := W' ⊔ K ∙ x
  have hxW'' : x ∈ W'' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hW''W₀ : W'' ≤ W₀ :=
    sup_le hW'W₀ ((Submodule.span_singleton_le_iff_mem _ _).mpr hxW₀)
  have hW''gr : IsGradedPi 𝒜 W'' := fun χ =>
    sup_le ((hW'gr χ).trans (Submodule.comap_mono le_sup_left)) (by
      rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap]
      by_cases h : N = χ
      · subst h
        rw [gradedProjPi_of_mem hxN]
        exact hxW''
      · rw [gradedProjPi_of_mem_ne hxN h]
        exact W''.zero_mem)
  have hW''st : IsStablePi W'' := fun l =>
    sup_le ((hW'st l).trans (Submodule.comap_mono le_sup_left)) (by
      rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap,
        ← sub_add_cancel (rightActPi n l x) (l e • x)]
      exact W''.add_mem (Submodule.mem_sup_left (hgen l)) (W''.smul_mem _ hxW''))
  have : FiniteDimensional K W'' := Submodule.finiteDimensional_of_le hW''W₀
  have hlt' : W' < W'' := lt_of_le_of_ne le_sup_left fun h => hxW' (h.ge hxW'')
  have hne : V ⊓ W'' ≠ ⊥ := fun h => by
    refine Nat.findGreatest_is_greatest (P := P) ?_ (Submodule.finrank_mono hW''W₀)
      ⟨W'', hW''W₀, hW''gr, hW''st, h, rfl⟩
    rw [← hd]
    exact Submodule.finrank_lt_finrank_of_lt hlt'
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hv
  refine ⟨v, hv.1, hv0, fun l => ?_⟩
  have hmem : rightActPi n l v - l e • v ∈ V ⊓ W' := by
    refine Submodule.mem_inf.mpr ⟨V.sub_mem (hVst l hv.1) (V.smul_mem _ hv.1), ?_⟩
    obtain ⟨w, hw, y, hy, hwy⟩ := Submodule.mem_sup.mp hv.2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have : rightActPi n l v - l e • v =
        (rightActPi n l w - l e • w) + c • (rightActPi n l x - l e • x) := by
      rw [← hwy, map_add, map_smul, smul_add, smul_sub, smul_comm c (l e) x]
      abel
    rw [this]
    exact W'.add_mem (W'.sub_mem (hW'st l hw) (W'.smul_mem _ hw)) (W'.smul_mem _ (hgen l))
  rw [hVW', Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

end TopWeight

section FixedVector

variable [Coalgebra K B]

/-- The right translate of a matrix coefficient, expanded along the comultiplication. -/
theorem rightAct_matrix_coeff {n : Type*} [Fintype n] {M : Matrix n n B}
    (hM : ∀ i j, comul (R := K) (M i j) = ∑ l, M i l ⊗ₜ[K] M l j) (m : Module.Dual K B)
    (i j : n) : rightAct m (M i j) = ∑ l, m (M l j) • M i l := by
  rw [rightAct_apply, hM, map_sum, map_sum]
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

/-- An element `b` with `rightAct l b = l e • b` for every functional `l` is a scalar multiple
of `e`, namely `counit b • e`. -/
theorem eq_counit_smul_of_rightAct {e b : B} (h : ∀ l : Module.Dual K B, rightAct l b = l e • b) :
    b = counit (R := K) b • e := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro g
  have hg := congrArg (counit (R := K)) (h g)
  rw [← apply_leftAct, leftAct_counit, map_smul, smul_eq_mul] at hg
  rw [map_sub, map_smul, hg, smul_eq_mul, mul_comm, sub_self]

/-- Let `B` be a coalgebra over a field `K`, graded by a linearly ordered abelian group `Γ` with
graded comultiplication, and let `e ∈ B` be a grouplike element of degree `0` satisfying the
top-weight rigidity hypothesis `hrigid`. Then every matrix corepresentation `M` of `B`, indexed by
a nonempty finite type, has a nonzero fixed vector `v`: `∑ j, v j • M i j = v i • e` for all `i`. -/
theorem exists_fixed_vector_of_graded {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (𝒜 : Γ → Submodule K B) (h𝒜 : DirectSum.IsInternal 𝒜)
    (hΔ : ∀ χ, ∀ a ∈ 𝒜 χ, comul (R := K) a ∈
      ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α)))
    {e : B} (he : comul (R := K) e = e ⊗ₜ e) (hεe : counit (R := K) e = 1) (he0 : e ∈ 𝒜 0)
    (hrigid : ∀ a ∈ 𝒜 0, (∀ m : Module.Dual K B, (∀ χ, 0 ≤ χ → ∀ b ∈ 𝒜 χ, m b = 0) →
      rightAct m a = 0) → ∃ c : K, a = c • e)
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (M : Matrix n n B)
    (hM : ∀ i j, comul (R := K) (M i j) = ∑ l, M i l ⊗ₜ[K] M l j)
    (hMε : ∀ i j, counit (R := K) (M i j) = (1 : Matrix n n K) i j) :
    ∃ v : n → K, v ≠ 0 ∧ ∀ i, ∑ j, v j • M i j = v i • e := by
  classical
  let _ : DirectSum.Decomposition 𝒜 := h𝒜.chooseDecomposition
  -- A finite set of degrees supporting every matrix coefficient.
  obtain ⟨s, hs⟩ := exists_gradedProjPi_eq_zero (𝒜 := 𝒜) (fun p : n × n => M p.1 p.2)
  have hs' : ∀ i j, ∀ χ ∉ s, gradedProj 𝒜 χ (M i j) = 0 := fun i j χ hχ =>
    congrFun (hs χ hχ) (i, j)
  -- The graded right-translation-stable subspace `𝒰` of `B` generated by the coefficients.
  let f : (n × n) × Γ × Module.Dual K B → B := fun q =>
    rightAct q.2.2 (gradedProj 𝒜 q.2.1 (M q.1.1 q.1.2))
  let 𝒰 : Submodule K B := Submodule.span K (Set.range f)
  have h𝒰gr : ∀ χ, ∀ b ∈ 𝒰, gradedProj 𝒜 χ b ∈ 𝒰 := by
    intro χ b hb
    refine (Submodule.span_le.mpr ?_ : 𝒰 ≤ 𝒰.comap (gradedProj 𝒜 χ)) hb
    rintro _ ⟨⟨⟨i, j⟩, ψ, g⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    simp only [f]
    rw [gradedProj_rightAct hΔ (gradedProj_mem ψ (M i j)) χ g]
    exact Submodule.subset_span ⟨((i, j), ψ, g ∘ₗ gradedProj 𝒜 (ψ - χ)), rfl⟩
  have h𝒰st : ∀ m : Module.Dual K B, ∀ b ∈ 𝒰, rightAct m b ∈ 𝒰 := by
    intro m b hb
    refine (Submodule.span_le.mpr ?_ : 𝒰 ≤ 𝒰.comap (rightAct m)) hb
    rintro _ ⟨⟨⟨i, j⟩, ψ, g⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    simp only [f]
    rw [rightAct_rightAct]
    exact Submodule.subset_span ⟨((i, j), ψ, m ∘ₗ rightAct g), rfl⟩
  have hM𝒰 : ∀ i j, M i j ∈ 𝒰 := by
    intro i j
    rw [← sum_gradedProj (hs' i j)]
    refine Submodule.sum_mem _ fun χ _ => ?_
    rw [← rightAct_counit (K := K) (gradedProj 𝒜 χ (M i j))]
    exact Submodule.subset_span ⟨((i, j), χ, counit), rfl⟩
  have : FiniteDimensional K 𝒰 := by
    choose U hUfg hU using exists_fg_rightAct (K := K) (B := B)
    let X : Submodule K B := ⨆ q : (n × n) × s, U (gradedProj 𝒜 q.2 (M q.1.1 q.1.2))
    have h𝒰X : 𝒰 ≤ X := Submodule.span_le.mpr (by
      rintro _ ⟨⟨⟨i, j⟩, ψ, g⟩, rfl⟩
      by_cases hψ : ψ ∈ s
      · exact Submodule.mem_iSup_of_mem (((i, j), ⟨ψ, hψ⟩) : (n × n) × s) (hU _ g)
      · simp only [f, SetLike.mem_coe]
        rw [hs' i j ψ hψ, map_zero]
        exact X.zero_mem)
    have : FiniteDimensional K X :=
      (Submodule.fg_iff_finiteDimensional X).mp (Submodule.fg_iSup _ fun q => hUfg _)
    exact Submodule.finiteDimensional_of_le h𝒰X
  -- The coordinatewise subspace `𝒰ⁿ` of `n → B`.
  let W₀ : Submodule K (n → B) := LinearMap.range (𝒰.subtype.compLeft n)
  have hW₀ : ∀ y : n → B, y ∈ W₀ ↔ ∀ i, y i ∈ 𝒰 := fun y => by
    refine ⟨fun hy i => ?_, fun hy => LinearMap.mem_range.mpr ⟨fun i => ⟨y i, hy i⟩, rfl⟩⟩
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hy
    exact (u i).2
  have hW₀gr : IsGradedPi 𝒜 W₀ := fun χ y hy =>
    (hW₀ _).mpr fun i => h𝒰gr χ _ ((hW₀ y).mp hy i)
  have hW₀st : IsStablePi W₀ := fun m y hy =>
    (hW₀ _).mpr fun i => h𝒰st m _ ((hW₀ y).mp hy i)
  -- The span `V` of the columns of `M`.
  let col : n → n → B := fun j i => M i j
  let V : Submodule K (n → B) := Submodule.span K (Set.range col)
  have hVst : IsStablePi V := fun m => Submodule.span_le.mpr (by
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have : rightActPi n m (col j) = ∑ l, m (M l j) • col l := by
      ext i
      simp [col, rightAct_matrix_coeff hM, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun l _ => V.smul_mem _ (Submodule.subset_span ⟨l, rfl⟩))
  have hVW₀ : V ≤ W₀ := Submodule.span_le.mpr (by
    rintro _ ⟨j, rfl⟩
    exact (hW₀ _).mpr fun i => hM𝒰 i j)
  have hV : V ≠ ⊥ := by
    obtain ⟨i₀⟩ := ‹Nonempty n›
    intro h
    have h0 : col i₀ = 0 := by
      rw [← Submodule.mem_bot K, ← h]
      exact Submodule.subset_span ⟨i₀, rfl⟩
    have h1 := hMε i₀ i₀
    rw [show M i₀ i₀ = 0 from congrFun h0 i₀, map_zero, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  obtain ⟨v, hvV, hv0, hv⟩ :=
    exists_coinvariant hΔ he hεe he0 hrigid hW₀gr hW₀st hVst hVW₀ hV
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hvV
  refine ⟨c, fun hc => hv0 (by simp [hc]), fun i => ?_⟩
  have hvi : (∑ j, c j • col j) i = ∑ j, c j • M i j := by simp [col, Finset.sum_apply]
  have key := eq_counit_smul_of_rightAct (e := e) (b := (∑ j, c j • col j) i)
    fun l => congrFun (hv l) i
  rw [hvi] at key
  rw [key]
  congr 1
  simp [map_sum, hMε, Matrix.one_apply]

/-- `exists_fixed_vector_of_graded` with the comultiplication `Δ` and counit `ε` given explicitly
as linear maps satisfying the coalgebra axioms, rather than through a `Coalgebra` instance. Right
translation by `m` is written out as `b ↦ TensorProduct.rid K B (m.lTensor B (Δ b))`. -/
theorem exists_fixed_vector_of_graded' {B : Type*} [AddCommGroup B] [Module K B]
    (Δ : B →ₗ[K] B ⊗[K] B) (ε : B →ₗ[K] K)
    (hcoassoc : TensorProduct.assoc K B B B ∘ₗ Δ.rTensor B ∘ₗ Δ = Δ.lTensor B ∘ₗ Δ)
    (hrε : ε.rTensor B ∘ₗ Δ = TensorProduct.mk K K B 1)
    (hlε : ε.lTensor B ∘ₗ Δ = (TensorProduct.mk K B K).flip 1)
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (𝒜 : Γ → Submodule K B) (h𝒜 : DirectSum.IsInternal 𝒜)
    (hΔ : ∀ χ, ∀ a ∈ 𝒜 χ, Δ a ∈ ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α)))
    {e : B} (he : Δ e = e ⊗ₜ e) (hεe : ε e = 1) (he0 : e ∈ 𝒜 0)
    (hrigid : ∀ a ∈ 𝒜 0, (∀ m : Module.Dual K B, (∀ χ, 0 ≤ χ → ∀ b ∈ 𝒜 χ, m b = 0) →
      TensorProduct.rid K B (m.lTensor B (Δ a)) = 0) → ∃ c : K, a = c • e)
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (M : Matrix n n B)
    (hM : ∀ i j, Δ (M i j) = ∑ l, M i l ⊗ₜ[K] M l j)
    (hMε : ∀ i j, ε (M i j) = (1 : Matrix n n K) i j) :
    ∃ v : n → K, v ≠ 0 ∧ ∀ i, ∑ j, v j • M i j = v i • e := by
  let _ : Coalgebra K B :=
    { comul := Δ
      counit := ε
      coassoc := hcoassoc
      rTensor_counit_comp_comul := hrε
      lTensor_counit_comp_comul := hlε }
  exact exists_fixed_vector_of_graded 𝒜 h𝒜 hΔ he hεe he0 hrigid M hM hMε

end FixedVector

end Langlands.GroupScheme.TorusUnipotence
