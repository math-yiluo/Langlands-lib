import Langlands.LinearAlgebra.RootDatumReversedPath
import Mathlib.Algebra.Group.Submonoid.Finsupp

/-! # Weights along a path component of type `A` -/

noncomputable section

open Set Function

set_option autoImplicit false

namespace Langlands.LinearAlgebra.RootDatumPathWeights

open Langlands.LinearAlgebra.RootDatumReversedPath

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootDatum ι M N} {b : P.Base}

/-- `β` lists, in path order, the vertices of a connected component of type `A_L` of the
Dynkin diagram of the base `b`: the pairings along `β` form the Cartan matrix of type `A_L`,
and every simple root off the path is orthogonal to all of it. -/
structure IsPathComponent {L : ℕ} (β : Fin L → b.support) : Prop where
  pos : 0 < L
  pairing_eq : ∀ i j, P.pairing (β i : ι) (β j : ι) =
    if (i : ℕ) = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0
  isOrthogonal : ∀ z, z ∉ Set.range β → ∀ i, P.IsOrthogonal (z : ι) (β i : ι)

/-- A reversed path is a path component. -/
theorem _root_.Langlands.LinearAlgebra.RootDatumReversedPath.IsReversedPath.isPathComponent
    {σ : Equiv.Perm b.support} {m : ℕ} {β : Fin (2 * m) → b.support}
    (h : IsReversedPath σ β) : IsPathComponent β :=
  ⟨by have := h.pos; omega, h.pairing_eq, h.isOrthogonal⟩

variable {L : ℕ}

theorem IsPathComponent.injective {β : Fin L → b.support} (hβ : IsPathComponent β) :
    Function.Injective β := by
  intro i j hij
  have := hβ.pairing_eq i j
  rw [hij, P.pairing_same] at this
  apply Fin.ext
  split_ifs at this with h1 h2 <;> omega

theorem IsPathComponent.pairing_mk {β : Fin L → b.support} (hβ : IsPathComponent β)
    {i j : ℕ} (hi : i < L) (hj : j < L) :
    P.pairing (β ⟨i, hi⟩ : ι) (β ⟨j, hj⟩ : ι) =
      if i = j then 2 else if i + 1 = j ∨ j + 1 = i then -1 else 0 :=
  hβ.pairing_eq _ _

theorem IsPathComponent.pairing_mk_left {β : Fin L → b.support} (hβ : IsPathComponent β)
    {j : ℕ} (hj : j < L) (i : Fin L) :
    P.pairing (β ⟨j, hj⟩ : ι) (β i : ι) =
      if j = (i : ℕ) then 2 else if j + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = j then -1 else 0 :=
  hβ.pairing_eq _ _

theorem IsPathComponent.pairing_succ_left {β : Fin L → b.support} (hβ : IsPathComponent β)
    {i : ℕ} (hi : i + 1 < L) :
    P.pairing (β ⟨i + 1, hi⟩ : ι) (β ⟨i, by omega⟩ : ι) = -1 := by
  rw [hβ.pairing_eq]
  simp

theorem IsPathComponent.pairing_succ_right {β : Fin L → b.support} (hβ : IsPathComponent β)
    {i : ℕ} (hi : i + 1 < L) :
    P.pairing (β ⟨i, by omega⟩ : ι) (β ⟨i + 1, hi⟩ : ι) = -1 := by
  rw [hβ.pairing_eq]
  simp

variable (β : Fin L → b.support)

/-- The `i`-th simple root along the path, and `0` past its end. -/
def pathRoot (i : ℕ) : M := if h : i < L then P.root (β ⟨i, h⟩ : ι) else 0

/-- The weight `ω - (α_0 + ⋯ + α_{j-1})` obtained from `ω` by subtracting the first `j`
simple roots of the path. -/
def pathWeight (ω : M) (j : ℕ) : M := ω - ∑ i ∈ Finset.range j, pathRoot β i

theorem pathRoot_of_lt {i : ℕ} (hi : i < L) : pathRoot β i = P.root (β ⟨i, hi⟩ : ι) :=
  dite_eq_left hi

@[simp] theorem pathWeight_zero (ω : M) : pathWeight β ω 0 = ω := by
  simp [pathWeight]

theorem pathWeight_succ (ω : M) (j : ℕ) :
    pathWeight β ω (j + 1) = pathWeight β ω j - pathRoot β j := by
  simp only [pathWeight, Finset.sum_range_succ]
  abel

/-- `ω` is the fundamental weight at the first vertex `β 0` of the path: it pairs to `1` with
the coroot of `β 0` and to `0` with every other simple coroot. -/
structure IsPathFundamental (ω : M) : Prop where
  pairing_path : ∀ i : Fin L, P.toLinearMap ω (P.coroot (β i : ι)) = if (i : ℕ) = 0 then 1 else 0
  pairing_off : ∀ z : b.support, z ∉ Set.range β → P.toLinearMap ω (P.coroot (z : ι)) = 0

variable {β}

/-- The pairing of a path weight with the coroot of a path vertex. -/
theorem pairing_pathWeight (hβ : IsPathComponent β) {ω : M} (hω : IsPathFundamental β ω)
    {j : ℕ} (hj : j ≤ L) (i : Fin L) :
    P.toLinearMap (pathWeight β ω j) (P.coroot (β i : ι)) =
      if j = (i : ℕ) then 1 else if j = (i : ℕ) + 1 then -1 else 0 := by
  induction j with
  | zero =>
    rw [pathWeight_zero, hω.pairing_path i]
    split_ifs <;> omega
  | succ j ih =>
    rw [pathWeight_succ, map_sub, LinearMap.sub_apply, ih (by omega),
      pathRoot_of_lt β (by omega : j < L), RootPairing.root_coroot_eq_pairing,
      hβ.pairing_mk_left (by omega : j < L) i]
    split_ifs <;> omega

/-- `pairing_pathWeight` with the path vertex given by a natural number. -/
theorem pairing_pathWeight_mk (hβ : IsPathComponent β) {ω : M} (hω : IsPathFundamental β ω)
    {j : ℕ} (hj : j ≤ L) {i : ℕ} (hi : i < L) :
    P.toLinearMap (pathWeight β ω j) (P.coroot (β ⟨i, hi⟩ : ι)) =
      if j = i then 1 else if j = i + 1 then -1 else 0 :=
  pairing_pathWeight hβ hω hj ⟨i, hi⟩

/-- Path weights are orthogonal to the coroots of simple roots off the path. -/
theorem pairing_pathWeight_of_not_mem (hβ : IsPathComponent β) {ω : M} (hω : IsPathFundamental β ω)
    {z : b.support} (hz : z ∉ Set.range β) (j : ℕ) :
    P.toLinearMap (pathWeight β ω j) (P.coroot (z : ι)) = 0 := by
  induction j with
  | zero => rw [pathWeight_zero, hω.pairing_off z hz]
  | succ j ih =>
    rw [pathWeight_succ, map_sub, LinearMap.sub_apply, ih]
    unfold pathRoot
    split_ifs with h
    · rw [RootPairing.root_coroot_eq_pairing, (hβ.isOrthogonal z hz ⟨j, h⟩).2, sub_zero]
    · simp

theorem reflection_apply_eq (γ : ι) (x : M) :
    P.reflection γ x = x - P.toLinearMap x (P.coroot γ) • P.root γ :=
  RootPairing.reflection_apply _ _ _

/-- The reflection in the `j`-th path root moves the `j`-th path weight to the next one. -/
theorem reflection_pathWeight_self (hβ : IsPathComponent β) {ω : M} (hω : IsPathFundamental β ω)
    {j : ℕ} (hj : j < L) :
    P.reflection (β ⟨j, hj⟩ : ι) (pathWeight β ω j) = pathWeight β ω (j + 1) := by
  rw [reflection_apply_eq, pairing_pathWeight hβ hω hj.le, ite_eq_left rfl, one_smul,
    pathWeight_succ, pathRoot_of_lt β hj]

/-- Every simple reflection maps a path weight to a path weight. -/
theorem reflection_pathWeight (hβ : IsPathComponent β) {ω : M} (hω : IsPathFundamental β ω)
    (γ : b.support) {j : ℕ} (hj : j ≤ L) :
    ∃ j' ≤ L, P.reflection (γ : ι) (pathWeight β ω j) = pathWeight β ω j' := by
  by_cases hγ : γ ∈ Set.range β
  · obtain ⟨i, rfl⟩ := hγ
    have hi := i.2
    rw [reflection_apply_eq, pairing_pathWeight hβ hω hj]
    by_cases h1 : j = (i : ℕ)
    · subst h1
      refine ⟨(i : ℕ) + 1, by omega, ?_⟩
      rw [ite_eq_left rfl, one_smul, pathWeight_succ, pathRoot_of_lt β hi]
    · by_cases h2 : j = (i : ℕ) + 1
      · subst h2
        refine ⟨i, by omega, ?_⟩
        rw [ite_eq_right h1, ite_eq_left rfl, pathWeight_succ, pathRoot_of_lt β hi]
        simp
      · refine ⟨j, hj, ?_⟩
        rw [ite_eq_right h1, ite_eq_right h2, zero_smul, sub_zero]
  · refine ⟨j, hj, ?_⟩
    rw [reflection_apply_eq, pairing_pathWeight_of_not_mem hβ hω hγ, zero_smul, sub_zero]

private theorem pathWeight_ne_of_lt (hβ : IsPathComponent β) {ω : M} (hω : IsPathFundamental β ω)
    {j j' : ℕ} (hlt : j < j') (hj' : j' ≤ L) : pathWeight β ω j ≠ pathWeight β ω j' := by
  intro h
  have e := congrArg (fun x => P.toLinearMap x (P.coroot (β ⟨j, by omega⟩ : ι))) h
  rw [pairing_pathWeight_mk hβ hω (by omega), pairing_pathWeight_mk hβ hω hj'] at e
  split_ifs at e <;> omega

/-- Distinct indices give distinct path weights. -/
theorem pathWeight_injOn (hβ : IsPathComponent β) {ω : M} (hω : IsPathFundamental β ω)
    {j j' : ℕ} (hj : j ≤ L) (hj' : j' ≤ L) (h : pathWeight β ω j = pathWeight β ω j') :
    j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hlt
  · exact absurd h (pathWeight_ne_of_lt hβ hω hlt hj')
  · exact heq
  · exact absurd h.symm (pathWeight_ne_of_lt hβ hω hlt hj)

/-! ### Reflection-stable sets below the first fundamental weight -/

section Form

variable [Fintype ι]

private theorem rootForm_comm (x y : M) : P.RootForm x y = P.RootForm y x := by
  simp only [RootPairing.rootForm_apply_apply, mul_comm]

private theorem rootForm_self_nonneg (x : M) : 0 ≤ P.RootForm x x := by
  rw [RootPairing.rootForm_apply_apply]
  exact Finset.sum_nonneg fun k _ => mul_self_nonneg _

private theorem rootForm_pos {x : M} (hx : x ∈ P.rootSpan ℤ) (hx0 : x ≠ 0) :
    0 < P.RootForm x x := by
  rcases (rootForm_self_nonneg (P := P) x).lt_or_eq with h | h
  · exact h
  · exfalso
    rw [RootPairing.rootForm_apply_apply] at h
    have hnonneg : ∀ k ∈ Finset.univ, 0 ≤ P.coroot' k x * P.coroot' k x :=
      fun k _ => mul_self_nonneg _
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h.symm
    have hker : x ∈ LinearMap.ker P.RootForm := by
      rw [LinearMap.mem_ker]
      ext y
      rw [RootPairing.rootForm_apply_apply, LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun k hk => ?_
      have := hzero k hk
      rw [mul_self_eq_zero] at this
      rw [this, zero_mul]
    exact hx0 ((Submodule.disjoint_def.mp P.disjoint_rootSpan_ker_rootForm) x hx hker)

/-- `2 B(α_i, x) = ⟨x, α_i^∨⟩ B(α_i, α_i)` for every `x`. -/
private theorem two_mul_rootForm_root_left (i : ι) (x : M) :
    2 * P.RootForm (P.root i) x =
      P.toLinearMap x (P.coroot i) * P.RootForm (P.root i) (P.root i) := by
  have h := congrArg (P.toLinearMap x) (P.rootForm_self_smul_coroot i)
  simp only [map_smul, map_nsmul, RootPairing.toLinearMap_apply_apply_Polarization,
    smul_eq_mul, nsmul_eq_mul] at h
  push_cast at h
  linarith

private theorem rootForm_root_root_eq_zero {i j : ι} (h : P.pairing j i = 0) :
    P.RootForm (P.root i) (P.root j) = 0 := by
  have h2 := two_mul_rootForm_root_left (P := P) i (P.root j)
  rw [RootPairing.root_coroot_eq_pairing, h, zero_mul] at h2
  linarith

private theorem rootForm_add_smul (S a : M) (x : ℤ) :
    P.RootForm (S + x • a) (S + x • a) =
      P.RootForm S S + 2 * x * P.RootForm S a + x * x * P.RootForm a a := by
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  linear_combination x * rootForm_comm (P := P) a S

private theorem rootForm_add_add (X Y : M) :
    P.RootForm (X + Y) (X + Y) = P.RootForm X X + 2 * P.RootForm X Y + P.RootForm Y Y := by
  simp only [map_add, LinearMap.add_apply]
  linear_combination rootForm_comm (P := P) Y X

/-- All path roots have the norm of the first one. -/
private theorem rootForm_pathRoot (hβ : IsPathComponent β) {i : ℕ} (hi : i < L) :
    P.RootForm (pathRoot β i) (pathRoot β i) =
      P.RootForm (P.root (β ⟨0, hβ.pos⟩ : ι)) (P.root (β ⟨0, hβ.pos⟩ : ι)) := by
  induction i with
  | zero => rw [pathRoot_of_lt β hi]
  | succ i ih =>
    rw [← ih (by omega), pathRoot_of_lt β hi, pathRoot_of_lt β (by omega : i < L)]
    have h1 := two_mul_rootForm_root_left (P := P) (β ⟨i, by omega⟩ : ι)
      (P.root (β ⟨i + 1, hi⟩ : ι))
    have h2 := two_mul_rootForm_root_left (P := P) (β ⟨i + 1, hi⟩ : ι)
      (P.root (β ⟨i, by omega⟩ : ι))
    rw [RootPairing.root_coroot_eq_pairing, hβ.pairing_succ_left hi] at h1
    rw [RootPairing.root_coroot_eq_pairing, hβ.pairing_succ_right hi] at h2
    have c := rootForm_comm (P := P) (P.root (β ⟨i, by omega⟩ : ι))
      (P.root (β ⟨i + 1, hi⟩ : ι))
    linarith

/-- The coefficient sequence along the path of a function on simple roots. -/
private def pathCoeff (f : Fin L → b.support) (c : b.support → ℤ) (i : ℕ) : ℤ :=
  if h : i < L then c (f ⟨i, h⟩) else 0

/-- The coefficient preceding position `i` (zero at the start). -/
private def prevCoeff (x : ℕ → ℤ) (i : ℕ) : ℤ := if i = 0 then 0 else x (i - 1)

/-- The quadratic form of the Cartan matrix of type `A_l` on the first `l` coefficients,
with the cross terms indexed by the later vertex. -/
private def cartanQuad (x : ℕ → ℤ) (l : ℕ) : ℤ :=
  2 * ∑ i ∈ Finset.range l, x i * x i - 2 * ∑ i ∈ Finset.range l, prevCoeff x i * x i

private theorem cartanQuad_succ (x : ℕ → ℤ) (l : ℕ) :
    cartanQuad x (l + 1) = cartanQuad x l + 2 * x l * x l - 2 * prevCoeff x l * x l := by
  simp only [cartanQuad, Finset.sum_range_succ]
  ring

private theorem int_abs_le_mul_self (y : ℤ) : |y| ≤ y * y := by
  rcases (abs_nonneg y).eq_or_lt with h | h
  · rw [← h]
    exact mul_self_nonneg y
  · have h1 : 1 ≤ |y| := by omega
    have : y * y = |y| * |y| := (abs_mul_abs_self y).symm
    nlinarith

private theorem cartanQuad_ge_aux (x : ℕ → ℤ) (l : ℕ) :
    x 0 * x 0 + |x 0| - |x l| ≤ cartanQuad x (l + 1) - x l * x l := by
  induction l with
  | zero =>
    simp [cartanQuad, prevCoeff]
    nlinarith
  | succ l ih =>
    have hp : prevCoeff x (l + 1) = x l := by simp [prevCoeff]
    rw [cartanQuad_succ, hp]
    have h1 := int_abs_le_mul_self (x l - x (l + 1))
    have h2 : |x l| ≤ |x l - x (l + 1)| + |x (l + 1)| := by
      have := abs_add_le (x l - x (l + 1)) (x (l + 1))
      rwa [sub_add_cancel] at this
    nlinarith

/-- The Cartan form of type `A_L` dominates `x₀² + x₀` for nonnegative coefficients. -/
private theorem cartanQuad_ge (x : ℕ → ℤ) {l : ℕ} (hl : 0 < l) (h0 : 0 ≤ x 0) :
    x 0 * x 0 + x 0 ≤ cartanQuad x l := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have := cartanQuad_ge_aux x l
  have h1 := int_abs_le_mul_self (x l)
  rw [abs_of_nonneg h0] at this
  linarith

/-- The norm of a partial path sum is given by the Cartan form of type `A`. -/
private theorem two_mul_rootForm_partialSum (hβ : IsPathComponent β) (x : ℕ → ℤ) {l : ℕ}
    (hl : l ≤ L) :
    2 * P.RootForm (∑ i ∈ Finset.range l, x i • pathRoot β i)
        (∑ i ∈ Finset.range l, x i • pathRoot β i) =
      P.RootForm (P.root (β ⟨0, hβ.pos⟩ : ι)) (P.root (β ⟨0, hβ.pos⟩ : ι)) * cartanQuad x l := by
  induction l with
  | zero => simp [cartanQuad]
  | succ l ih =>
    have hlL : l < L := by omega
    rw [Finset.sum_range_succ, rootForm_add_smul, cartanQuad_succ, rootForm_pathRoot hβ hlL]
    -- the cross term with the new root
    have hcross : 2 * P.RootForm (∑ i ∈ Finset.range l, x i • pathRoot β i) (pathRoot β l) =
        - (P.RootForm (P.root (β ⟨0, hβ.pos⟩ : ι)) (P.root (β ⟨0, hβ.pos⟩ : ι)) *
          prevCoeff x l) := by
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      have hterm : ∀ i ∈ Finset.range l, 2 * (x i * P.RootForm (pathRoot β i) (pathRoot β l)) =
          if i + 1 = l then
            - (P.RootForm (P.root (β ⟨0, hβ.pos⟩ : ι)) (P.root (β ⟨0, hβ.pos⟩ : ι)) * x i)
          else 0 := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have h2 := two_mul_rootForm_root_left (P := P) (β ⟨i, by omega⟩ : ι)
          (P.root (β ⟨l, hlL⟩ : ι))
        rw [RootPairing.root_coroot_eq_pairing, hβ.pairing_mk hlL (by omega : i < L)] at h2
        have hn := rootForm_pathRoot hβ (by omega : i < L)
        rw [pathRoot_of_lt β (by omega : i < L)] at hn
        rw [pathRoot_of_lt β (by omega : i < L), pathRoot_of_lt β hlL]
        rw [hn] at h2
        split_ifs at h2 ⊢ <;> first | omega | linear_combination x i * h2
      rw [Finset.sum_congr rfl hterm]
      by_cases hl0 : l = 0
      · subst hl0
        simp [prevCoeff]
      · rw [Finset.sum_eq_single (l - 1)]
        · rw [ite_eq_left (by omega), prevCoeff, ite_eq_right hl0]
        · intro i _ hi
          rw [ite_eq_right (by omega)]
        · intro h
          exact absurd (Finset.mem_range.mpr (by omega)) h
    linear_combination (ih (by omega)) + 2 * x l * hcross

/-- The quadratic bound on a nonnegative combination of simple roots. -/
private theorem two_mul_rootForm_ge (hβ : IsPathComponent β) (c : b.support → ℕ) :
    P.RootForm (P.root (β ⟨0, hβ.pos⟩ : ι)) (P.root (β ⟨0, hβ.pos⟩ : ι)) *
        ((c (β ⟨0, hβ.pos⟩) : ℤ) * c (β ⟨0, hβ.pos⟩) + c (β ⟨0, hβ.pos⟩)) ≤
      2 * P.RootForm (∑ γ, c γ • P.root (γ : ι)) (∑ γ, c γ • P.root (γ : ι)) := by
  classical
  let x : ℕ → ℤ := pathCoeff β (fun γ => (c γ : ℤ))
  have hx0 : x 0 = c (β ⟨0, hβ.pos⟩) := dite_eq_left hβ.pos
  obtain ⟨DA, hDA⟩ : ∃ DA : M, DA = ∑ i : Fin L, c (β i) • P.root (β i : ι) := ⟨_, rfl⟩
  obtain ⟨DR, hDR⟩ : ∃ DR : M,
      DR = ∑ γ ∈ (Finset.univ.image β)ᶜ, c γ • P.root (γ : ι) := ⟨_, rfl⟩
  have hsplit : ∑ γ, c γ • P.root (γ : ι) = DA + DR := by
    rw [hDA, hDR, ← Finset.sum_add_sum_compl (Finset.univ.image β),
      Finset.sum_image (by intro i _ j _ h; exact hβ.injective h)]
  have hDA' : DA = ∑ i ∈ Finset.range L, x i • pathRoot β i := by
    rw [hDA, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [x, pathCoeff, pathRoot, i.2, natCast_zsmul]
  have h1 : ∀ i : Fin L, P.RootForm (P.root (β i : ι)) DR = 0 := by
    intro i
    rw [hDR, map_sum]
    refine Finset.sum_eq_zero fun γ hγ => ?_
    have hγ' : γ ∉ Set.range β := by
      rintro ⟨j, rfl⟩
      exact Finset.mem_compl.mp hγ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    rw [map_nsmul, rootForm_root_root_eq_zero (hβ.isOrthogonal γ hγ' i).1, smul_zero]
  have hcross : P.RootForm DA DR = 0 := by
    rw [hDA, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_nsmul, LinearMap.smul_apply, h1 i, smul_zero]
  have hDRnn := rootForm_self_nonneg (P := P) DR
  have hAA := two_mul_rootForm_partialSum hβ x (le_refl L)
  rw [← hDA'] at hAA
  have hq := cartanQuad_ge x hβ.pos (by rw [hx0]; positivity)
  have hn0 : 0 < P.RootForm (P.root (β ⟨0, hβ.pos⟩ : ι)) (P.root (β ⟨0, hβ.pos⟩ : ι)) :=
    rootForm_pos (Submodule.subset_span (Set.mem_range_self _)) (P.ne_zero _)
  rw [hsplit, rootForm_add_add, hcross]
  rw [hx0] at hq
  nlinarith

/-- A dominant weight below `ω` is `ω` itself. -/
private theorem eq_of_dominant (hβ : IsPathComponent β) {ω : M} (hω : IsPathFundamental β ω)
    {ν : M} (hdom : ∀ γ : b.support, 0 ≤ P.toLinearMap ν (P.coroot (γ : ι)))
    {c : b.support → ℕ} (hc : ω - ν = ∑ γ, c γ • P.root (γ : ι)) : ν = ω := by
  classical
  have hn0 : 0 < P.RootForm (P.root (β ⟨0, hβ.pos⟩ : ι)) (P.root (β ⟨0, hβ.pos⟩ : ι)) :=
    rootForm_pos (Submodule.subset_span (Set.mem_range_self _)) (P.ne_zero _)
  have hlin : ∀ y : M, 2 * P.RootForm (∑ γ, c γ • P.root (γ : ι)) y =
      ∑ γ, (c γ : ℤ) * (P.toLinearMap y (P.coroot (γ : ι)) *
        P.RootForm (P.root (γ : ι)) (P.root (γ : ι))) := by
    intro y
    simp only [map_sum, map_nsmul, LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← two_mul_rootForm_root_left]
    ring
  have hν : 0 ≤ 2 * P.RootForm (∑ γ, c γ • P.root (γ : ι)) ν := by
    rw [hlin]
    exact Finset.sum_nonneg fun γ _ => mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (hdom γ) (rootForm_self_nonneg _))
  have hωeq : 2 * P.RootForm (∑ γ, c γ • P.root (γ : ι)) ω =
      c (β ⟨0, hβ.pos⟩) *
        P.RootForm (P.root (β ⟨0, hβ.pos⟩ : ι)) (P.root (β ⟨0, hβ.pos⟩ : ι)) := by
    rw [hlin, Finset.sum_eq_single (β ⟨0, hβ.pos⟩)]
    · rw [hω.pairing_path, ite_eq_left rfl, one_mul]
    · intro γ _ hγ
      by_cases hr : γ ∈ Set.range β
      · obtain ⟨i, rfl⟩ := hr
        have hi : (i : ℕ) ≠ 0 := fun h => hγ (congrArg β (Fin.ext h))
        rw [hω.pairing_path, ite_eq_right hi, zero_mul, mul_zero]
      · rw [hω.pairing_off γ hr, zero_mul, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hDD : P.RootForm (∑ γ, c γ • P.root (γ : ι)) (∑ γ, c γ • P.root (γ : ι)) =
      P.RootForm (∑ γ, c γ • P.root (γ : ι)) ω - P.RootForm (∑ γ, c γ • P.root (γ : ι)) ν := by
    rw [← map_sub, hc]
  have hge := two_mul_rootForm_ge hβ c
  have h0 : (0 : ℤ) ≤ c (β ⟨0, hβ.pos⟩) := Nat.cast_nonneg _
  have h1 : P.RootForm (P.root (β ⟨0, hβ.pos⟩ : ι)) (P.root (β ⟨0, hβ.pos⟩ : ι)) *
      ((c (β ⟨0, hβ.pos⟩) : ℤ) * c (β ⟨0, hβ.pos⟩)) ≤ 0 := by
    nlinarith
  have h2 : (c (β ⟨0, hβ.pos⟩) : ℤ) * c (β ⟨0, hβ.pos⟩) ≤ 0 := by
    by_contra h
    push Not at h
    have := mul_pos hn0 h
    linarith
  have hc0 : (c (β ⟨0, hβ.pos⟩) : ℤ) = 0 := by
    have := mul_self_nonneg (c (β ⟨0, hβ.pos⟩) : ℤ)
    exact mul_self_eq_zero.mp (le_antisymm h2 this)
  have hD : ∑ γ, c γ • P.root (γ : ι) = 0 := by
    by_contra hne
    have hmem : ∑ γ, c γ • P.root (γ : ι) ∈ P.rootSpan ℤ :=
      Submodule.sum_mem _ fun γ _ => nsmul_mem (Submodule.subset_span (Set.mem_range_self _)) _
    have := rootForm_pos hmem hne
    rw [hc0, zero_mul] at hωeq
    linarith
  rw [hD] at hc
  exact (sub_eq_zero.mp hc).symm

end Form

/-- **Minuscule orbit.** Let `β` be a path component of type `A_L` and `ω` the fundamental
weight at its first vertex `β 0`. A set of weights that is stable under all simple reflections
and lies below `ω` (that is, `ω - ν` is a nonnegative integral combination of simple roots)
consists of path weights `ω - (α_0 + ⋯ + α_{j-1})`, `j ≤ L`. -/
theorem exists_eq_pathWeight [Finite ι] (hβ : IsPathComponent β)
    {ω : M} (hω : IsPathFundamental β ω)
    {S : Set M} (hrefl : ∀ ν ∈ S, ∀ γ : b.support, P.reflection (γ : ι) ν ∈ S)
    (hle : ∀ ν ∈ S,
      ω - ν ∈ AddSubmonoid.closure (Set.range fun γ : b.support => P.root (γ : ι)))
    {ν : M} (hν : ν ∈ S) : ∃ j ≤ L, ν = pathWeight β ω j := by
  classical
  let := Fintype.ofFinite ι
  have hcoef : ∀ ν ∈ S, ∃ c : b.support → ℕ, ω - ν = ∑ γ, c γ • P.root (γ : ι) :=
    fun ν hν => AddSubmonoid.mem_closure_range_iff_of_fintype.mp (hle ν hν)
  have hli := linearIndependent_iff'.mp b.linearIndepOn_root.linearIndependent
  suffices H : ∀ n : ℕ, ∀ ν ∈ S, ∀ c : b.support → ℕ,
      ω - ν = ∑ γ, c γ • P.root (γ : ι) → ∑ γ, c γ ≤ n → ∃ j ≤ L, ν = pathWeight β ω j by
    obtain ⟨c, hc⟩ := hcoef ν hν
    exact H _ ν hν c hc le_rfl
  intro n
  induction n with
  | zero =>
    intro ν hν c hc hn
    have hc0 : ∀ γ, c γ = 0 := fun γ =>
      (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hn)) γ (Finset.mem_univ γ)
    simp only [hc0, zero_smul, Finset.sum_const_zero] at hc
    exact ⟨0, Nat.zero_le _, by rw [pathWeight_zero]; exact (sub_eq_zero.mp hc).symm⟩
  | succ n ih =>
    intro ν hν c hc hn
    by_cases hdom : ∀ γ : b.support, 0 ≤ P.toLinearMap ν (P.coroot (γ : ι))
    · exact ⟨0, Nat.zero_le _, by rw [pathWeight_zero]; exact eq_of_dominant hβ hω hdom hc⟩
    push Not at hdom
    obtain ⟨γ, hγ⟩ := hdom
    have hν' : P.reflection (γ : ι) ν ∈ S := hrefl ν hν γ
    obtain ⟨c', hc'⟩ := hcoef _ hν'
    -- compare the coefficients of `ν` and of its reflection
    have hrel : ∀ δ : b.support, (c' δ : ℤ) =
        c δ + if δ = γ then P.toLinearMap ν (P.coroot (γ : ι)) else 0 := by
      have heq : ∑ δ, ((c' δ : ℤ) - (c δ + if δ = γ then P.toLinearMap ν (P.coroot (γ : ι))
          else 0)) • P.root (δ : ι) = 0 := by
        simp only [sub_smul, add_smul, ite_smul, zero_smul, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, natCast_zsmul]
        rw [← hc', ← hc, reflection_apply_eq]
        abel
      intro δ
      have := hli Finset.univ _ heq δ (Finset.mem_univ δ)
      linarith
    have hsum : (∑ δ, c' δ : ℤ) = ∑ δ, (c δ : ℤ) + P.toLinearMap ν (P.coroot (γ : ι)) := by
      simp only [hrel, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hle' : ∑ δ, c' δ ≤ n := by
      have : (∑ δ, c' δ : ℤ) < ∑ δ, (c δ : ℤ) := by linarith
      have h2 : (∑ δ, (c δ : ℤ)) ≤ n + 1 := by exact_mod_cast hn
      have h3 : ((∑ δ, c' δ : ℕ) : ℤ) = ∑ δ, (c' δ : ℤ) := by push_cast; rfl
      omega
    obtain ⟨j', hj', hνj⟩ := ih _ hν' c' hc' hle'
    obtain ⟨j'', hj'', h''⟩ := reflection_pathWeight hβ hω γ hj'
    refine ⟨j'', hj'', ?_⟩
    rw [← h'', ← hνj, RootPairing.reflection_same]

end Langlands.LinearAlgebra.RootDatumPathWeights
