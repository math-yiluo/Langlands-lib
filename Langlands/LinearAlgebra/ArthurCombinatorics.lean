import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.Basic.Real.Basic

/-! # Arthur's combinatorics of standard parabolic subgroups

Arthur 1978, §1 and §6; Arthur 2005, §§5–8. The data are a root system `P` over `ℝ` with a base
`b`: the weight space `M` is `(𝔞_0^G)^*`, the coweight space `N` is `𝔞_0^G`, the simple roots
`α_i`, `i ∈ b.support`, are `Δ_0`, and a standard parabolic subgroup is recorded by the set
`Θ ⊆ b.support` of simple roots of its Levi component. For such `Θ`:

* `corootSpan P Θ` is `𝔞_0^P`, spanned by the coroots `α_i^∨`, `i ∈ Θ`;
* `rootAnnihilator P Θ` is `𝔞_P^G`, the common kernel of the roots `α_i`, `i ∈ Θ`;
* `levelProjection P Θ` is the projection `H ↦ H_P` of `𝔞_0^G = 𝔞_0^P ⊕ 𝔞_P^G` onto `𝔞_P^G`
  (`isCompl_corootSpan_rootAnnihilator`).

Arthur's characteristic functions `τ_{P_1}^{P_2}`, `τ̂_{P_1}^{P_2}`, his function `σ_{P_1}^{P_2}`,
and Langlands' functions `φ_Q^P(Λ, ·)` with the signs `ε_Q^P(Λ)` are integer valued functions on
`𝔞_0^G`. -/

noncomputable section

open Module Submodule

set_option autoImplicit false

namespace Langlands.ArthurCombinatorics

variable {ι M N : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
  [Module ℝ N] (P : RootPairing ι ℝ M N)

/-- `𝔞_0^P`: the span of the coroots `α_i^∨`, `i ∈ Θ`. -/
def corootSpan (Θ : Finset ι) : Submodule ℝ N :=
  span ℝ (P.coroot '' (Θ : Set ι))

/-- `𝔞_P^G`: the vectors on which every root `α_i`, `i ∈ Θ`, vanishes. -/
def rootAnnihilator (Θ : Finset ι) : Submodule ℝ N :=
  ⨅ i ∈ Θ, LinearMap.ker (P.root' i)

/-- The block `(α_k(α_j^∨))_{k, j ∈ Θ}` of the Cartan matrix. -/
def cartanBlock (Θ : Finset ι) : Matrix Θ Θ ℝ :=
  Matrix.of fun k j => P.root' k (P.coroot j)

omit [DecidableEq ι] in
@[simp] theorem cartanBlock_apply (Θ : Finset ι) (k j : Θ) :
    cartanBlock P Θ k j = P.root' k (P.coroot j) :=
  rfl

/-- `ϖ_i`: for `i ∈ Θ`, the linear form `∑_k (A_Θ⁻¹)_{ik} α_k`, `A_Θ = cartanBlock P Θ`. For `Θ` in a
base it is the coefficient of `α_i^∨` in the `𝔞_0^P`-component of a vector
(`weightCoordinate_coroot`, `weightCoordinate_eq_zero_of_mem_rootAnnihilator`), that is, the
element of `Δ̂_{P_1}^{P}` attached to `α_i` for every `P_1 ⊆ P` with `α_i ∉ Δ_0^{P_1}`. It is `0`
for `i ∉ Θ`. -/
def weightCoordinate (Θ : Finset ι) (i : ι) : N →ₗ[ℝ] ℝ :=
  if h : i ∈ Θ then ∑ k : Θ, (cartanBlock P Θ)⁻¹ ⟨i, h⟩ k • P.root' k else 0

/-- The projection `H ↦ H_P = H - ∑_{j ∈ Θ} ϖ_j(H) α_j^∨` of `𝔞_0^G = 𝔞_0^P ⊕ 𝔞_P^G` onto
`𝔞_P^G` (`levelProjection_mem_rootAnnihilator`, `sub_levelProjection_mem_corootSpan`). -/
def levelProjection (Θ : Finset ι) : N →ₗ[ℝ] N :=
  LinearMap.id - ∑ j : Θ, (weightCoordinate P Θ j).smulRight (P.coroot j)

/-- `τ_{P_1}^{P_2}(H)`: `1` if `α_i(H_{P_1}) > 0` for every `i ∈ Θ₂ \ Θ₁` (the roots of
`Δ_{P_1}^{P_2}`, restricted to `𝔞_{P_1}`), and `0` otherwise. -/
def tau (Θ₁ Θ₂ : Finset ι) (H : N) : ℤ :=
  if ∀ i ∈ Θ₂ \ Θ₁, 0 < P.root' i (levelProjection P Θ₁ H) then 1 else 0

/-- `τ̂_{P_1}^{P_2}(H)`: `1` if `ϖ_i(H) > 0` for every `i ∈ Θ₂ \ Θ₁` (the weights of
`Δ̂_{P_1}^{P_2}`, `ϖ_i = weightCoordinate P Θ₂ i`), and `0` otherwise. -/
def tauHat (Θ₁ Θ₂ : Finset ι) (H : N) : ℤ :=
  if ∀ i ∈ Θ₂ \ Θ₁, 0 < weightCoordinate P Θ₂ i H then 1 else 0

/-- Arthur's `σ_{P_1}^{P_2}(H) = ∑_{P_3 ⊇ P_2} (−1)^{dim(A_2/A_3)} τ_{P_1}^{P_3}(H) τ̂_{P_3}(H)`
(Arthur 1978, §6), for `G` given by `S`: the sum runs over `Θ₂ ⊆ Θ₃ ⊆ S`, with
`dim(A_2/A_3) = |Θ₃ \ Θ₂|` and `τ̂_{P_3} = τ̂_{P_3}^G`. -/
def sigma (S Θ₁ Θ₂ : Finset ι) (H : N) : ℤ :=
  ∑ Θ₃ ∈ S.powerset.filter (Θ₂ ⊆ ·),
    (-1) ^ (Θ₃ \ Θ₂).card * tau P Θ₁ Θ₃ H * tauHat P Θ₃ S H

/-- `Λ(α^∨)` for the root `α ∈ Δ_Q^P` attached to `i ∈ Θ_P \ Θ_Q`: the coroot `α^∨` is the
projection of `α_i^∨` onto `𝔞_Q^P`, which is its `𝔞_Q`-component `levelProjection P Θ_Q α_i^∨`. -/
def corootValue (Θ : Finset ι) (Λ : M) (i : ι) : ℝ :=
  P.toLinearMap Λ (levelProjection P Θ (P.coroot i))

/-- Langlands' sign `ε_Q^P(Λ) = (−1)^{#{α ∈ Δ_Q^P : Λ(α^∨) ≤ 0}}` (Arthur 1978, §6). -/
def epsilon (ΘQ ΘP : Finset ι) (Λ : M) : ℤ :=
  (-1) ^ ((ΘP \ ΘQ).filter fun i => corootValue P ΘQ Λ i ≤ 0).card

/-- Langlands' function `φ_Q^P(Λ, H)` (Arthur 1978, §6): `1` if for every `α ∈ Δ_Q^P`,
`ϖ_α(H) > 0` when `Λ(α^∨) ≤ 0` and `ϖ_α(H) ≤ 0` when `Λ(α^∨) > 0`, and `0` otherwise. -/
def phi (ΘQ ΘP : Finset ι) (Λ : M) (H : N) : ℤ :=
  if ∀ i ∈ ΘP \ ΘQ, (corootValue P ΘQ Λ i ≤ 0 → 0 < weightCoordinate P ΘP i H) ∧
      (0 < corootValue P ΘQ Λ i → weightCoordinate P ΘP i H ≤ 0) then 1 else 0

section Base

variable {P} (b : P.Base) [Finite ι] [P.IsRootSystem]

omit [DecidableEq ι] in
/-- For a subset `Θ` of a base, `𝔞_0^G = 𝔞_0^P ⊕ 𝔞_P^G`. -/
theorem isCompl_corootSpan_rootAnnihilator {Θ : Finset ι} (hΘ : Θ ⊆ b.support) :
    IsCompl (corootSpan P Θ) (rootAnnihilator P Θ) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional ℝ N := Module.Finite.of_basis b.toCoweightBasis
  -- a vector on which every root vanishes is zero
  have hzero : ∀ Y : N, (∀ k, P.root' k Y = 0) → Y = 0 := by
    intro Y hY
    have hall : ∀ m : M, P.toLinearMap m Y = 0 := by
      intro m
      have hm : m ∈ span ℝ (Set.range P.root) := by simp
      refine span_induction (p := fun m _ => P.toLinearMap m Y = 0) ?_ ?_ ?_ ?_ hm
      · rintro _ ⟨k, rfl⟩; exact hY k
      · simp
      · intro x y _ _ hx hy; simp [hx, hy]
      · intro a x _ hx; simp [hx]
    have h0 : P.flip.toPerfPair Y = 0 := by
      ext m; exact hall m
    exact (LinearEquiv.map_eq_zero_iff _).mp h0
  -- the invariant form detects vanishing of a root on a vector
  have hform : ∀ (i : ι) (Y : N), P.root' i Y = 0 → P.CorootForm (P.coroot i) Y = 0 := by
    intro i Y hY
    have hY' : P.toLinearMap (P.root i) Y = 0 := hY
    have h1 : P.toLinearMap (2 • P.CoPolarization (P.coroot i)) Y = 0 := by
      rw [← P.corootForm_self_smul_root i, map_smul, LinearMap.smul_apply, hY', smul_zero]
    rw [map_nsmul, LinearMap.smul_apply, P.toLinearMap_apply_CoPolarization] at h1
    rcases (smul_eq_zero.mp h1) with h2 | h2
    · exact absurd h2 two_ne_zero
    · exact h2
  have hdisj : Disjoint (corootSpan P Θ) (rootAnnihilator P Θ) := by
    rw [Submodule.disjoint_def]
    intro Y hYc hYa
    have hroot : ∀ i ∈ Θ, P.root' i Y = 0 := by
      intro i hi
      have := (Submodule.mem_iInf _).mp hYa i
      exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp this hi)
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp hYc
    have hlin : ∀ Z : N, P.CorootForm (Finsupp.linearCombination ℝ P.coroot l) Z =
        ∑ j ∈ l.support, l j * P.CorootForm (P.coroot j) Z := by
      intro Z
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
        LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have hself : P.CorootForm (Finsupp.linearCombination ℝ P.coroot l)
        (Finsupp.linearCombination ℝ P.coroot l) = 0 := by
      rw [hlin]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [hform j _ (hroot j (hl hj)), mul_zero]
    apply hzero
    intro k
    rw [P.corootForm_apply_apply] at hself
    have hsq := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      mul_self_nonneg (P.root' k (Finsupp.linearCombination ℝ P.coroot l)))).mp
      hself k (Finset.mem_univ k)
    exact mul_self_eq_zero.mp hsq
  refine ⟨hdisj, ?_⟩
  rw [codisjoint_iff]
  -- dimension count
  have hli : LinearIndependent ℝ (fun x : Θ => P.coroot x) :=
    b.linearIndepOn_coroot.mono (Finset.coe_subset.mpr hΘ)
  have hA : finrank ℝ (corootSpan P Θ) = Θ.card := by
    have h := finrank_span_eq_card hli
    have hspan : corootSpan P Θ = span ℝ (Set.range fun x : Θ => P.coroot x) := by
      rw [corootSpan, Set.image_eq_range]; rfl
    rw [hspan, h]
    simp
  let f : N →ₗ[ℝ] (Θ → ℝ) := LinearMap.pi fun x : Θ => P.root' x
  have hker : LinearMap.ker f = rootAnnihilator P Θ := by
    ext Y
    simp [f, rootAnnihilator, LinearMap.ker_pi, Submodule.mem_iInf]
  have hB : finrank ℝ N ≤ finrank ℝ (rootAnnihilator P Θ) + Θ.card := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : finrank ℝ (LinearMap.range f) ≤ Θ.card := by
      calc finrank ℝ (LinearMap.range f) ≤ finrank ℝ (Θ → ℝ) := Submodule.finrank_le _
        _ = Θ.card := by simp
    rw [hker] at h1
    omega
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (corootSpan P Θ) (rootAnnihilator P Θ)
  rw [disjoint_iff.mp hdisj, finrank_bot] at hsum
  apply Submodule.eq_top_of_finrank_eq
  have hle := Submodule.finrank_le (corootSpan P Θ ⊔ rootAnnihilator P Θ)
  omega

/-- The Cartan block of a subset of a base is invertible. -/
theorem isUnit_det_cartanBlock {Θ : Finset ι} (hΘ : Θ ⊆ b.support) :
    IsUnit (cartanBlock P Θ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hYc : (∑ j : Θ, v j • P.coroot (j : ι)) ∈ corootSpan P Θ :=
    Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, j.2, rfl⟩)
  have hYa : (∑ j : Θ, v j • P.coroot (j : ι)) ∈ rootAnnihilator P Θ := by
    simp only [rootAnnihilator, Submodule.mem_iInf, LinearMap.mem_ker]
    intro k hk
    have := congrFun hAv ⟨k, hk⟩
    simpa [Matrix.mulVec, dotProduct, map_sum, map_smul, mul_comm] using this
  have hY0 := (Submodule.disjoint_def.mp (isCompl_corootSpan_rootAnnihilator b hΘ).disjoint) _
    hYc hYa
  have hli : LinearIndependent ℝ (fun x : Θ => P.coroot x) :=
    b.linearIndepOn_coroot.mono (Finset.coe_subset.mpr hΘ)
  exact hv (funext fun j => Fintype.linearIndependent_iff.mp hli v hY0 j)

theorem weightCoordinate_coroot {Θ : Finset ι} (hΘ : Θ ⊆ b.support) {i j : ι} (hi : i ∈ Θ)
    (hj : j ∈ Θ) : weightCoordinate P Θ i (P.coroot j) = if i = j then 1 else 0 := by
  classical
  have hinv := Matrix.nonsing_inv_mul (cartanBlock P Θ) (isUnit_det_cartanBlock b hΘ)
  have h := congrFun (congrFun hinv ⟨i, hi⟩) ⟨j, hj⟩
  simp only [Matrix.mul_apply, cartanBlock_apply, Matrix.one_apply,
    Subtype.mk.injEq] at h
  simp only [weightCoordinate, hi, ↓reduceDIte, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  exact h

omit [Finite ι] [P.IsRootSystem] in
theorem weightCoordinate_eq_zero_of_mem_rootAnnihilator {Θ : Finset ι} (i : ι) {Z : N}
    (hZ : Z ∈ rootAnnihilator P Θ) : weightCoordinate P Θ i Z = 0 := by
  classical
  have hk : ∀ k ∈ Θ, P.root' k Z = 0 := by
    intro k hk
    have := (Submodule.mem_iInf _).mp hZ k
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp this hk)
  unfold weightCoordinate
  split_ifs with hi
  · simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun k _ => by rw [hk k k.2, mul_zero]
  · rfl

omit [Finite ι] [P.IsRootSystem] in
theorem sub_levelProjection_mem_corootSpan (Θ : Finset ι) (H : N) :
    H - levelProjection P Θ H ∈ corootSpan P Θ := by
  simp only [levelProjection, LinearMap.sub_apply, LinearMap.id_apply, sub_sub_cancel,
    LinearMap.sum_apply, LinearMap.smulRight_apply]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, j.2, rfl⟩)

theorem levelProjection_mem_rootAnnihilator {Θ : Finset ι} (hΘ : Θ ⊆ b.support) (H : N) :
    levelProjection P Θ H ∈ rootAnnihilator P Θ := by
  classical
  simp only [rootAnnihilator, Submodule.mem_iInf, LinearMap.mem_ker]
  intro k hk
  have hinv := Matrix.mul_nonsing_inv (cartanBlock P Θ) (isUnit_det_cartanBlock b hΘ)
  simp only [levelProjection, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, map_sub, map_sum, map_smul, smul_eq_mul]
  rw [sub_eq_zero]
  have hw : ∀ j : Θ, weightCoordinate P Θ j H =
      ∑ l : Θ, (cartanBlock P Θ)⁻¹ j l * P.root' l H := by
    intro j
    simp [weightCoordinate, j.2]
  simp_rw [hw, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ l : Θ, ∑ j : Θ, (cartanBlock P Θ)⁻¹ j l * P.root' l H * P.root' k (P.coroot j) =
      (if (⟨k, hk⟩ : Θ) = l then 1 else 0) * P.root' l H := by
    intro l
    have h := congrFun (congrFun hinv ⟨k, hk⟩) l
    simp only [Matrix.mul_apply, cartanBlock_apply, Matrix.one_apply] at h
    rw [← h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  simp

end Base

end Langlands.ArthurCombinatorics
