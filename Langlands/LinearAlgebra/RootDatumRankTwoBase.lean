import Langlands.GroupScheme.Reductive.LocalSplitRootPairCommutator

/-! # Bases containing a rank-two parabolic subsystem through two roots -/

universe u

open Module Matrix

namespace Langlands.LinearAlgebra

section Perp

variable {I : Type*} [Fintype I]

/-- **A perpendicular integer vector.** If `x` is not in the rational span of two linearly
independent integer vectors `β`, `ε`, some integer vector `w` is orthogonal to `β` and `ε` but
not to `x`. -/
theorem exists_dotProduct_perp {β ε x : I → ℤ} (hli : LinearIndependent ℤ ![β, ε])
    (hx : ∀ n p q : ℤ, n • x = p • β + q • ε → n = 0) :
    ∃ w : I → ℤ, w ⬝ᵥ β = 0 ∧ w ⬝ᵥ ε = 0 ∧ w ⬝ᵥ x ≠ 0 := by
  set A := β ⬝ᵥ β
  set B := β ⬝ᵥ ε
  set C := ε ⬝ᵥ ε
  have hε0 : ε ≠ 0 := by
    have := hli.ne_zero 1
    simpa using this
  have hC : C ≠ 0 := fun h => hε0 (dotProduct_self_eq_zero.mp h)
  have hΔ : A * C - B * B ≠ 0 := by
    intro h
    have hv : (C • β - B • ε) ⬝ᵥ (C • β - B • ε) = C * (A * C - B * B) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        A, B, C, dotProduct_comm ε β]
      ring
    rw [h, mul_zero] at hv
    have h0 := dotProduct_self_eq_zero.mp hv
    have := LinearIndependent.pair_iff.mp hli C (-B) (by rw [neg_smul, ← sub_eq_add_neg]; exact h0)
    exact hC this.1
  set L := C * (x ⬝ᵥ β) - B * (x ⬝ᵥ ε)
  set N := A * (x ⬝ᵥ ε) - B * (x ⬝ᵥ β)
  set w := (A * C - B * B) • x - L • β - N • ε with hw
  have hwβ : w ⬝ᵥ β = 0 := by
    simp only [hw, sub_dotProduct, smul_dotProduct, smul_eq_mul, L, N, A, B, C,
      dotProduct_comm ε β]
    ring
  have hwε : w ⬝ᵥ ε = 0 := by
    simp only [hw, sub_dotProduct, smul_dotProduct, smul_eq_mul, L, N, A, B, C]
    ring
  refine ⟨w, hwβ, hwε, fun h => ?_⟩
  have hww : w ⬝ᵥ w = 0 := by
    conv_lhs => rw [hw]
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [h, hwβ, hwε]
    ring
  have h0 := dotProduct_self_eq_zero.mp hww
  have := hx (A * C - B * B) L N (by
    rw [hw, sub_sub, sub_eq_zero] at h0
    exact h0)
  exact hΔ this

end Perp

section Base

open Langlands.GroupScheme.SplitExistence

variable {I J : Type u} [Fintype I] [Finite J] [DecidableEq J] (P : RootDatum J (I → ℤ) (I → ℤ))

omit [Fintype I] [Finite J] in
/-- Three distinct simple roots of a base cannot all lie in the rational span of two roots. -/
theorem not_three_mem_plane (b : P.Base) {β ε t₁ t₂ t₃ : J} (h₁ : t₁ ∈ b.support)
    (h₂ : t₂ ∈ b.support) (h₃ : t₃ ∈ b.support) (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃)
    (h₂₃ : t₂ ≠ t₃)
    (hp : ∀ t ∈ ({t₁, t₂, t₃} : Finset J), ∃ k p q : ℤ, k ≠ 0 ∧
      k • P.root t = p • P.root β + q • P.root ε) : False := by
  classical
  obtain ⟨k₁, p₁, q₁, hk₁, e₁⟩ := hp t₁ (by simp)
  obtain ⟨k₂, p₂, q₂, hk₂, e₂⟩ := hp t₂ (by simp)
  obtain ⟨k₃, p₃, q₃, hk₃, e₃⟩ := hp t₃ (by simp)
  -- three vectors of `ℤ²` are dependent
  have hdep : (p₂ * q₃ - p₃ * q₂) • (k₁ • P.root t₁) + (p₃ * q₁ - p₁ * q₃) • (k₂ • P.root t₂) +
      (p₁ * q₂ - p₂ * q₁) • (k₃ • P.root t₃) = 0 := by
    rw [e₁, e₂, e₃]
    simp only [smul_add, smul_smul]
    rw [← sub_eq_zero]
    have : ∀ (x y : I → ℤ) (a₁ a₂ a₃ b₁ b₂ b₃ : ℤ), a₁ • x + b₁ • y + (a₂ • x + b₂ • y) +
        (a₃ • x + b₃ • y) - 0 = (a₁ + a₂ + a₃) • x + (b₁ + b₂ + b₃) • y := by
      intros; module
    rw [this]
    have e1 : (p₂ * q₃ - p₃ * q₂) * p₁ + (p₃ * q₁ - p₁ * q₃) * p₂ + (p₁ * q₂ - p₂ * q₁) * p₃ = 0 := by
      ring
    have e2 : (p₂ * q₃ - p₃ * q₂) * q₁ + (p₃ * q₁ - p₁ * q₃) * q₂ + (p₁ * q₂ - p₂ * q₁) * q₃ = 0 := by
      ring
    rw [e1, e2, zero_smul, zero_smul, add_zero]
  have hli3 := linearIndepOn_iff'.mp (b.linearIndepOn_root.restrict_scalars' ℤ)
    ({t₁, t₂, t₃} : Finset J)
    (fun t => if t = t₁ then (p₂ * q₃ - p₃ * q₂) * k₁ else if t = t₂ then
      (p₃ * q₁ - p₁ * q₃) * k₂ else (p₁ * q₂ - p₂ * q₁) * k₃)
  have hsum := hli3 (by simp [Set.insert_subset_iff, h₁, h₂, h₃]) (by
    rw [Finset.sum_insert (by simp [h₁₂, h₁₃]), Finset.sum_insert (by simp [h₂₃]),
      Finset.sum_singleton]
    simp only [h₁₂.symm, h₁₃.symm, h₂₃.symm, ↓reduceIte, mul_smul]
    rw [← hdep]
    abel)
  have c₃ := hsum t₃ (by simp)
  simp only [h₁₃.symm, h₂₃.symm, ↓reduceIte] at c₃
  have m₃ : p₁ * q₂ - p₂ * q₁ = 0 := (mul_eq_zero.mp c₃).resolve_right hk₃
  -- the first two simple roots are then dependent
  have hpair := b.linearIndependent_pair_of_ne (i := ⟨t₁, h₁⟩) (j := ⟨t₂, h₂⟩)
    (fun h => h₁₂ (congrArg Subtype.val h))
  have r1 : (p₂ * k₁) • P.root t₁ + (-(p₁ * k₂)) • P.root t₂ = 0 := by
    have : (p₂ * k₁) • P.root t₁ + (-(p₁ * k₂)) • P.root t₂ =
        p₂ • (k₁ • P.root t₁) - p₁ • (k₂ • P.root t₂) := by
      simp only [mul_smul, neg_smul]; abel
    rw [this, e₁, e₂]
    rw [show p₂ • (p₁ • P.root β + q₁ • P.root ε) - p₁ • (p₂ • P.root β + q₂ • P.root ε) =
      (p₂ * q₁ - p₁ * q₂) • P.root ε by module]
    rw [show p₂ * q₁ - p₁ * q₂ = -(p₁ * q₂ - p₂ * q₁) by ring, m₃, neg_zero, zero_smul]
  have r2 : (q₂ * k₁) • P.root t₁ + (-(q₁ * k₂)) • P.root t₂ = 0 := by
    have : (q₂ * k₁) • P.root t₁ + (-(q₁ * k₂)) • P.root t₂ =
        q₂ • (k₁ • P.root t₁) - q₁ • (k₂ • P.root t₂) := by
      simp only [mul_smul, neg_smul]; abel
    rw [this, e₁, e₂]
    rw [show q₂ • (p₁ • P.root β + q₁ • P.root ε) - q₁ • (p₂ • P.root β + q₂ • P.root ε) =
      (q₂ * p₁ - q₁ * p₂) • P.root β by module]
    rw [show q₂ * p₁ - q₁ * p₂ = p₁ * q₂ - p₂ * q₁ by ring, m₃, zero_smul]
  have s1 := LinearIndependent.pair_iff.mp hpair _ _ r1
  have s2 := LinearIndependent.pair_iff.mp hpair _ _ r2
  have hp₁ : p₁ = 0 := by
    have := s1.2
    rw [neg_eq_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hk₂
  have hq₁ : q₁ = 0 := by
    have := s2.2
    rw [neg_eq_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hk₂
  rw [hp₁, hq₁, zero_smul, zero_smul, add_zero] at e₁
  have : P.root t₁ = 0 := by
    rcases smul_eq_zero.mp e₁ with h | h
    · exact absurd h hk₁
    · exact h
  exact P.ne_zero t₁ this

omit [DecidableEq J] in
/-- **A base through a rank-two subsystem** (compare SGA 3, Exp. XXI, 3.5.4). For two linearly
independent roots `β`, `ε` of a finite reduced root datum on `ℤ^I`, some base has two distinct
simple roots `a`, `c` with `β` and `ε` in `ℕ a + ℕ c`. -/
theorem exists_base_rankTwo [P.IsReduced] {β ε : J}
    (hli : LinearIndependent ℤ ![P.root β, P.root ε]) :
    ∃ (b : P.Base) (c : J), β ∈ b.support ∧ c ∈ b.support ∧ β ≠ c ∧
      ∃ p q : ℕ, P.root ε = p • P.root β + q • P.root c := by
  classical
  have := Fintype.ofFinite J
  let plane : J → Prop := fun j => ∃ k p q : ℤ, k ≠ 0 ∧
    k • P.root j = p • P.root β + q • P.root ε
  -- a functional vanishing exactly on the plane
  let S : Submodule ℤ (I → ℤ) := Submodule.span ℤ {P.root β, P.root ε}
  have hdet : ∀ j ∈ (Finset.univ.filter fun j => ¬ plane j),
      ∃ φ : Dual ℤ ((I → ℤ) ⧸ S), φ (S.mkQ (P.root j)) ≠ 0 := by
    intro j hj
    have hj' : ¬ plane j := (Finset.mem_filter.mp hj).2
    obtain ⟨w, hwβ, hwε, hwx⟩ := exists_dotProduct_perp hli (x := P.root j)
      (fun n p q h => by
        by_contra hn
        exact hj' ⟨n, p, q, hn, h⟩)
    let φ : Dual ℤ (I → ℤ) :=
      { toFun := fun v => w ⬝ᵥ v
        map_add' := fun v v' => dotProduct_add w v v'
        map_smul' := fun r v => by rw [dotProduct_smul]; rfl }
    have hle : S ≤ LinearMap.ker φ := by
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hwβ, hwε⟩
    exact ⟨S.liftQ φ hle, by simpa [φ] using hwx⟩
  obtain ⟨φ, hφ⟩ := exists_dual_forall_ne_zero _ _ hdet
  let h' : Dual ℤ (I → ℤ) := φ ∘ₗ S.mkQ
  have h'β : h' (P.root β) = 0 := by
    have : S.mkQ (P.root β) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr (Submodule.subset_span (by simp))
    simp [h', this]
  have h'ε : h' (P.root ε) = 0 := by
    have : S.mkQ (P.root ε) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr (Submodule.subset_span (by simp))
    simp [h', this]
  have h'plane : ∀ j, plane j → h' (P.root j) = 0 := by
    rintro j ⟨k, p, q, hk, h⟩
    have := congrArg h' h
    rw [map_smul, map_add, map_smul, map_smul, h'β, h'ε, smul_zero, smul_zero, add_zero,
      smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left hk
  have h'ne : ∀ j, ¬ plane j → h' (P.root j) ≠ 0 :=
    fun j hj => hφ j (by simp [hj])
  -- a functional on the plane, minimal at `β`
  have hdot_nonneg : ∀ v : I → ℤ, 0 ≤ v ⬝ᵥ v := fun v =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  set A := P.root β ⬝ᵥ P.root β with hA
  set B := P.root β ⬝ᵥ P.root ε with hB
  set C := P.root ε ⬝ᵥ P.root ε with hC
  have hCpos : 0 < C := lt_of_le_of_ne (hdot_nonneg _)
    (Ne.symm fun h => P.ne_zero ε (dotProduct_self_eq_zero.mp h))
  set Δ := A * C - B * B with hΔdef
  have hΔ : 0 < Δ := by
    have hv : (C • P.root β - B • P.root ε) ⬝ᵥ (C • P.root β - B • P.root ε) = C * Δ := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        hΔdef, hA, hB, hC, dotProduct_comm (P.root ε) (P.root β)]
      ring
    have hne : Δ ≠ 0 := by
      intro h
      rw [h, mul_zero] at hv
      have h0 := dotProduct_self_eq_zero.mp hv
      have := LinearIndependent.pair_iff.mp hli C (-B)
        (by rw [neg_smul, ← sub_eq_add_neg]; exact h0)
      exact hCpos.ne' this.1
    have := hdot_nonneg (C • P.root β - B • P.root ε)
    rw [hv] at this
    exact lt_of_le_of_ne (by nlinarith) (Ne.symm hne)
  let bnd : J → ℤ := fun j => if h : plane j then |h.choose| + |h.choose_spec.choose| else 0
  have hbnd0 : ∀ j, 0 ≤ bnd j := by
    intro j
    simp only [bnd]
    split_ifs <;> positivity
  let N : ℤ := 1 + ∑ j, bnd j
  have hrep : ∀ j, plane j → ∃ k p q : ℤ, k ≠ 0 ∧
      k • P.root j = p • P.root β + q • P.root ε ∧ |k| + |p| < N := by
    intro j h
    obtain ⟨hk, he⟩ := h.choose_spec.choose_spec.choose_spec
    refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose, hk, he, ?_⟩
    have hb : bnd j = |h.choose| + |h.choose_spec.choose| := by simp only [bnd, h, ↓reduceDIte]
    have hle := Finset.single_le_sum (f := bnd) (fun j _ => hbnd0 j) (Finset.mem_univ j)
    simp only [N]
    linarith
  set wβ := C • P.root β - B • P.root ε
  set wε := A • P.root ε - B • P.root β
  let f₀ : Dual ℤ (I → ℤ) :=
    { toFun := fun v => v ⬝ᵥ (wβ + N • wε)
      map_add' := fun v v' => add_dotProduct v v' _
      map_smul' := fun r v => by rw [smul_dotProduct]; rfl }
  have hf₀val : ∀ v : I → ℤ, f₀ v = v ⬝ᵥ (wβ + N • wε) := fun v => rfl
  have hf₀β' : f₀ (P.root β) = Δ := by
    rw [hf₀val]
    simp only [wβ, wε, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, hΔdef,
      hA, hB, hC]
    ring
  have hf₀ε' : f₀ (P.root ε) = N * Δ := by
    rw [hf₀val]
    simp only [wβ, wε, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, hΔdef,
      hA, hB, hC, dotProduct_comm (P.root ε) (P.root β)]
    ring
  have hN : 0 < N := by
    have := Finset.sum_nonneg (s := Finset.univ) fun j (_ : j ∈ Finset.univ) => hbnd0 j
    simp only [N]
    linarith
  have hf₀β : 0 < f₀ (P.root β) := by rw [hf₀β']; exact hΔ
  have hf₀ε : 0 < f₀ (P.root ε) := by rw [hf₀ε']; exact mul_pos hN hΔ
  -- planar roots other than `±β` take values larger than `Δ` in absolute value
  have hbig : ∀ j, plane j → j ≠ β → P.root j ≠ -P.root β → Δ < |f₀ (P.root j)| := by
    intro j hj hjβ hjnβ
    obtain ⟨k, p, q, hk, he, hkp⟩ := hrep j hj
    have hval : k * f₀ (P.root j) = Δ * (p + q * N) := by
      have := congrArg f₀ he
      rw [map_smul, map_add, map_smul, map_smul, hf₀β', hf₀ε', smul_eq_mul, smul_eq_mul,
        smul_eq_mul] at this
      rw [this]
      ring
    have hq : q ≠ 0 := by
      rintro rfl
      have hlin := RootPairing.IsReduced.linearIndependent P hjβ hjnβ
      have := LinearIndependent.pair_iff.mp hlin k (-p) (by
        rw [neg_smul, ← sub_eq_add_neg, he, zero_smul, add_zero, sub_self])
      exact hk this.1
    have hq1 : 1 ≤ |q| := Int.one_le_abs hq
    have htri : |q * N| ≤ |p + q * N| + |p| := by
      have := abs_sub (p + q * N) p
      rwa [add_sub_cancel_left] at this
    rw [abs_mul, abs_of_pos hN] at htri
    have hlarge : |k| < |p + q * N| := by nlinarith [abs_nonneg p, abs_nonneg k]
    have habs : |k| * |f₀ (P.root j)| = Δ * |p + q * N| := by
      rw [← abs_mul, hval, abs_mul, abs_of_pos hΔ]
    have hkpos : 0 < |k| := abs_pos.mpr hk
    nlinarith
  have hf₀ne : ∀ j, plane j → f₀ (P.root j) ≠ 0 := by
    intro j hj h0
    by_cases hjβ : j = β
    · rw [hjβ] at h0; exact hΔ.ne' (hf₀β'.symm.trans h0)
    by_cases hjnβ : P.root j = -P.root β
    · rw [hjnβ, map_neg, hf₀β'] at h0
      exact hΔ.ne' (neg_eq_zero.mp h0)
    have := hbig j hj hjβ hjnβ
    rw [h0, abs_zero] at this
    exact absurd this (not_lt.mpr hΔ.le)
  -- the combined functional
  let M : ℤ := 1 + ∑ j, |f₀ (P.root j)|
  have hM : ∀ j, |f₀ (P.root j)| < M := by
    intro j
    have := Finset.single_le_sum (f := fun j => |f₀ (P.root j)|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
    simp only [M]
    linarith
  have hM0 : 0 < M := lt_of_le_of_lt (abs_nonneg _) (hM β)
  let f : Dual ℤ (I → ℤ) := M • h' + f₀
  have hfval : ∀ j, f (P.root j) = M * h' (P.root j) + f₀ (P.root j) := by
    intro j
    simp [f]
  have hfplane : ∀ j, plane j → f (P.root j) = f₀ (P.root j) := by
    intro j hj
    rw [hfval, h'plane j hj, mul_zero, zero_add]
  have hfsign : ∀ j, ¬ plane j → (0 < f (P.root j) ↔ 0 < h' (P.root j)) ∧ f (P.root j) ≠ 0 := by
    intro j hj
    have hne := h'ne j hj
    obtain ⟨hlo, hhi⟩ := abs_lt.mp (hM j)
    rw [hfval]
    rcases lt_or_gt_of_ne hne with hl | hl
    · have h1 : h' (P.root j) ≤ -1 := by omega
      have := mul_le_mul_of_nonneg_left h1 hM0.le
      refine ⟨⟨fun h => by nlinarith, fun h => by omega⟩, by nlinarith⟩
    · have h1 : 1 ≤ h' (P.root j) := by omega
      have := mul_le_mul_of_nonneg_left h1 hM0.le
      refine ⟨⟨fun _ => hl, fun _ => by nlinarith⟩, by nlinarith⟩
  have hf : ∀ j, f (P.root j) ≠ 0 := by
    intro j
    by_cases hj : plane j
    · rw [hfplane j hj]
      exact hf₀ne j hj
    · exact (hfsign j hj).2
  -- the base of `f`
  let g : Dual ℤ (I → ℤ) := f ∘ₗ P.flip.Polarization
  have hg : ∀ j, g (P.coroot j) ≠ 0 := fun j => dual_polarization_root_ne_zero P.flip hf j
  have hgf : ∀ j, 0 < g (P.coroot j) ↔ 0 < f (P.root j) :=
    fun j => dual_polarization_root_pos_iff P.flip f j
  obtain ⟨b, hb⟩ := exists_base_isPos_iff P g hg
  have hbf : ∀ j, b.IsPos j ↔ 0 < f (P.root j) := fun j => (hb j).trans (hgf j)
  have hsimple : ∀ s ∈ b.support, 0 < f (P.root s) :=
    fun s hs => (hbf s).mp (RootPairing.Base.isPos_of_mem_support hs)
  have hh'simple : ∀ s ∈ b.support, 0 ≤ h' (P.root s) ∧ (h' (P.root s) = 0 → plane s) := by
    intro s hs
    by_cases hp : plane s
    · exact ⟨(h'plane s hp).ge, fun _ => hp⟩
    · have := (hfsign s hp).1.mp (hsimple s hs)
      exact ⟨this.le, fun h0 => absurd h0 this.ne'⟩
  -- decomposition of the roots of the plane
  have hdecomp : ∀ γ, h' (P.root γ) = 0 → 0 < f (P.root γ) → ∃ n : J → ℕ,
      P.root γ = ∑ j ∈ b.support, n j • P.root j ∧ ∀ j ∈ b.support, n j ≠ 0 → plane j := by
    intro γ hγ hfγ
    obtain ⟨n, -, h | h⟩ := b.exists_root_eq_sum_nat_or_neg γ
    · refine ⟨n, h, ?_⟩
      have hsum : ∑ j ∈ b.support, (n j : ℤ) * h' (P.root j) = 0 := by
        rw [← hγ, h, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_nsmul, nsmul_eq_mul]
      have hnonneg : ∀ j ∈ b.support, 0 ≤ (n j : ℤ) * h' (P.root j) :=
        fun j hj => mul_nonneg (by positivity) (hh'simple j hj).1
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
      intro j hj hnj
      rcases mul_eq_zero.mp (hz j hj) with h1 | h1
      · exact absurd (by exact_mod_cast h1) hnj
      · exact (hh'simple j hj).2 h1
    · exfalso
      have hle : f (P.root γ) ≤ 0 := by
        rw [h, map_neg, map_sum]
        have : 0 ≤ ∑ j ∈ b.support, f (n j • P.root j) := Finset.sum_nonneg fun j hj => by
          rw [map_nsmul]
          exact nsmul_nonneg (hsimple j hj).le _
        linarith
      linarith
  have hβplane : plane β := ⟨1, 1, 0, one_ne_zero, by simp⟩
  have hεplane : plane ε := ⟨1, 0, 1, one_ne_zero, by simp⟩
  obtain ⟨n, hn, hnp⟩ := hdecomp β h'β (by rw [hfplane β hβplane]; exact hf₀β)
  obtain ⟨m, hm, hmp⟩ := hdecomp ε h'ε (by rw [hfplane ε hεplane]; exact hf₀ε)
  -- `β` is simple
  have hβmem : β ∈ b.support := by
    by_contra hβs
    obtain ⟨s, hs, hns⟩ : ∃ s ∈ b.support, n s ≠ 0 := by
      by_contra! h0
      apply P.ne_zero β
      rw [hn]
      exact Finset.sum_eq_zero fun j hj => by rw [h0 j hj, zero_smul]
    have hsplane := hnp s hs hns
    have hsβ : s ≠ β := fun h => hβs (h ▸ hs)
    have hfs : 0 < f (P.root s) := hsimple s hs
    have hsnβ : P.root s ≠ -P.root β := by
      intro h
      rw [hfplane s hsplane, h, map_neg, hf₀β'] at hfs
      linarith
    have hgt : Δ < f (P.root s) := by
      have := hbig s hsplane hsβ hsnβ
      rw [← hfplane s hsplane, abs_of_pos hfs] at this
      exact this
    have hsum : f (P.root β) = ∑ j ∈ b.support, (n j : ℤ) * f (P.root j) := by
      rw [hn, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_nsmul, nsmul_eq_mul]
    have hge : (n s : ℤ) * f (P.root s) ≤ ∑ j ∈ b.support, (n j : ℤ) * f (P.root j) :=
      Finset.single_le_sum (f := fun j => (n j : ℤ) * f (P.root j))
        (fun j hj => mul_nonneg (by positivity) (hsimple j hj).le) hs
    have hn1 : (1 : ℤ) ≤ n s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hns
    rw [hfplane β hβplane, hf₀β'] at hsum
    nlinarith
  -- a second simple root occurring in `ε`
  obtain ⟨c, hc, hcβ, hmc⟩ : ∃ c ∈ b.support, c ≠ β ∧ m c ≠ 0 := by
    by_contra! h0
    have hεβ : P.root ε = m β • P.root β := by
      rw [hm, Finset.sum_eq_single_of_mem β hβmem fun j hj hjβ => by rw [h0 j hj hjβ, zero_smul]]
    have hdep : ((m β : ℕ) : ℤ) • P.root β + (-1 : ℤ) • P.root ε = 0 := by
      rw [hεβ, natCast_zsmul]
      simp
    have := (LinearIndependent.pair_iff.mp hli _ _ hdep).2
    norm_num at this
  have hplane_c : plane c := hmp c hc hmc
  have hthird : ∀ j ∈ b.support, j ≠ β → j ≠ c → m j = 0 := by
    intro j hj hjβ hjc
    by_contra h0
    exact not_three_mem_plane P b (β := β) (ε := ε) hβmem hc hj hcβ.symm (Ne.symm hjβ)
      (Ne.symm hjc) (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with h | h | h
      · rw [h]; exact hβplane
      · rw [h]; exact hplane_c
      · rw [h]; exact hmp j hj h0)
  refine ⟨b, c, hβmem, hc, hcβ.symm, m β, m c, ?_⟩
  rw [hm, ← Finset.sum_pair (f := fun j => m j • P.root j) hcβ.symm]
  symm
  refine Finset.sum_subset (by simp [Finset.insert_subset_iff, hβmem, hc]) fun j hj hj' => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj'
  rw [hthird j hj hj'.1 hj'.2, zero_smul]

/-- The index of the root obtained by applying the reflections of a word, the last letter
first. -/
def wordPerm (l : List J) (j : J) : J :=
  l.foldr (fun c e => P.reflectionPerm c e) j

omit [Fintype I] [Finite J] [DecidableEq J] in
theorem root_wordPerm (l : List J) (j : J) :
    P.root (wordPerm P l j) = Langlands.GroupScheme.LocalSplitCell.wordReflect P l (P.root j) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    change P.root (P.reflectionPerm c (wordPerm P l j)) =
      P.reflection c (Langlands.GroupScheme.LocalSplitCell.wordReflect P l (P.root j))
    rw [RootPairing.root_reflectionPerm, ih]

omit [Fintype I] [Finite J] [DecidableEq J] in
/-- Conjugating a reflection by the reflections of a word. -/
theorem reflection_wordPerm_wordReflect (l : List J) (t : J) (x : I → ℤ) :
    P.reflection (wordPerm P l t) (Langlands.GroupScheme.LocalSplitCell.wordReflect P l x) =
      Langlands.GroupScheme.LocalSplitCell.wordReflect P l (P.reflection t x) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    change P.reflection (P.reflectionPerm c (wordPerm P l t))
        (P.reflection c (Langlands.GroupScheme.LocalSplitCell.wordReflect P l x)) =
      P.reflection c (Langlands.GroupScheme.LocalSplitCell.wordReflect P l (P.reflection t x))
    rw [RootPairing.reflection_reflectionPerm]
    simp only [LinearEquiv.mul_apply, RootPairing.reflection_same]
    rw [ih]

omit [DecidableEq J] in
/-- Positivity for the base reflected by a reflection. -/
theorem isPos_map_reflection [DecidableEq J] [P.IsReduced] (b : P.Base) (s : J) (α : J) :
    (b.map (RootPairing.Equiv.reflection P s)).IsPos α ↔ b.IsPos (P.reflectionPerm s α) := by
  obtain ⟨d, hd, ν, hν⟩ := Langlands.GroupScheme.LocalSplitCell.exists_coPairing_eq_height P b
  let f : Dual ℤ (I → ℤ) :=
    { toFun := fun v => P.reflection s v ⬝ᵥ ν
      map_add' := fun v v' => by rw [map_add, add_dotProduct]
      map_smul' := fun r v => by rw [map_smul, smul_dotProduct]; rfl }
  have hf : ∀ j, f (P.root j) = d * b.height (P.reflectionPerm s j) := by
    intro j
    change P.reflection s (P.root j) ⬝ᵥ ν = _
    rw [← RootPairing.root_reflectionPerm]
    exact hν _
  have hsimple : ∀ j ∈ (b.map (RootPairing.Equiv.reflection P s)).support, 0 < f (P.root j) := by
    intro j hj
    rw [RootPairing.Base.support_map_eq, Finset.mem_image] at hj
    obtain ⟨t, ht, rfl⟩ := hj
    rw [hf]
    change 0 < d * b.height (P.reflectionPerm s (P.reflectionPerm s t))
    rw [RootPairing.reflectionPerm_self]
    exact mul_pos hd (RootPairing.Base.isPos_of_mem_support ht)
  rw [isPos_iff_of_pos_simple P _ f hsimple α, hf, RootPairing.Base.isPos_iff]
  constructor
  · intro h
    by_contra h'
    have : b.height (P.reflectionPerm s α) ≤ 0 := not_lt.mp h'
    nlinarith
  · intro h
    exact mul_pos hd h

/-- **The Weyl group is transitive on bases.** For two bases `b`, `b'` of a finite reduced root
datum on `ℤ^I`, some word `l` in the simple reflections of `b` carries the simple roots of `b`
onto those of `b'`. -/
theorem exists_word_of_base [P.IsReduced] (b b' : P.Base) :
    ∃ l : List J, (∀ c ∈ l, c ∈ b.support) ∧ ∀ s' ∈ b'.support, ∃ s ∈ b.support,
      P.root s' = Langlands.GroupScheme.LocalSplitCell.wordReflect P l (P.root s) := by
  classical
  have := Fintype.ofFinite J
  let N : P.Base → ℕ := fun b' => (Finset.univ.filter fun α => b.IsPos α ∧ ¬ b'.IsPos α).card
  -- the sign of a root for a base
  have hsign : ∀ (b₁ : P.Base) (α : J), b₁.IsPos (P.reflectionPerm α α) ↔ ¬ b₁.IsPos α := by
    intro b₁ α
    exact RootPairing.Base.IsPos.neg_iff_not (b := b₁) α
  suffices H : ∀ (n : ℕ) (b' : P.Base), N b' = n → ∃ l : List J, (∀ c ∈ l, c ∈ b.support) ∧
      ∀ s' ∈ b'.support, ∃ s ∈ b.support,
        P.root s' = Langlands.GroupScheme.LocalSplitCell.wordReflect P l (P.root s) from
    H _ b' rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b' hN
    by_cases hall : ∀ α, b.IsPos α → b'.IsPos α
    · -- the two bases have the same positive roots, hence the same simple roots
      have hpos' : ∀ α, b'.IsPos α → b.IsPos α := by
        intro α hα
        by_contra h
        have := hall _ ((hsign b α).mpr h)
        exact (hsign b' α).mp this hα
      refine ⟨[], by simp, fun s' hs' => ⟨s', ?_, rfl⟩⟩
      by_contra hns
      have hbpos := hpos' s' (RootPairing.Base.isPos_of_mem_support hs')
      obtain ⟨j, hj, hj'⟩ := hbpos.exists_mem_support_pos_pairingIn
      rw [P.zero_lt_pairingIn_iff'] at hj'
      have hne : s' ≠ j := fun h => hns (h ▸ hj)
      obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hj' hne
      have hkpos : b.IsPos k := hbpos.sub hj hk
      have h1 := RootPairing.Base.height_add (b := b') (i := k) (j := j) (k := s')
        (by rw [hk]; abel)
      rw [RootPairing.Base.height_one_of_mem_support hs'] at h1
      have h2 := hall k hkpos
      have h3 := hall j (RootPairing.Base.isPos_of_mem_support hj)
      rw [RootPairing.Base.isPos_iff] at h2 h3
      omega
    · -- a simple root of `b'` that is negative for `b`
      obtain ⟨s', hs', hneg⟩ : ∃ s' ∈ b'.support, ¬ b.IsPos s' := by
        by_contra! h
        apply hall
        intro α hα
        by_contra hα'
        have hnα : b'.IsPos (P.reflectionPerm α α) := (hsign b' α).mpr hα'
        have := hnα.induction_on_add (p := fun k => b.IsPos k) h
          (fun i j k hk hi hj => hi.add (h j hj) hk)
        exact (hsign b α).mp this hα
      set b'' := b'.map (RootPairing.Equiv.reflection P s') with hb''
      have hpos'' : ∀ α, b''.IsPos α ↔ b'.IsPos (P.reflectionPerm s' α) :=
        fun α => isPos_map_reflection P b' s' α
      have hlt : N b'' < n := by
        rw [← hN]
        apply Finset.card_lt_card
        refine ⟨fun α hα => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
          refine ⟨hα.1, fun h' => hα.2 ?_⟩
          rw [hpos'']
          have hαs : α ≠ s' := fun h => hneg (h ▸ hα.1)
          exact h'.reflectionPerm hs' hαs
        · have hmem : P.reflectionPerm s' s' ∈
              (Finset.univ.filter fun α => b.IsPos α ∧ ¬ b'.IsPos α) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨(hsign b s').mpr hneg,
              (hsign b' s').not.mpr (not_not.mpr (RootPairing.Base.isPos_of_mem_support hs'))⟩
          have := hsub hmem
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          apply this.2
          rw [hpos'', RootPairing.reflectionPerm_self]
          exact RootPairing.Base.isPos_of_mem_support hs'
      obtain ⟨l, hl, hmap⟩ := ih _ hlt b'' rfl
      -- the negative of `s'` is simple for `b''`
      obtain ⟨t, ht, hroot⟩ := hmap (P.reflectionPerm s' s') (by
        rw [hb'', RootPairing.Base.support_map_eq, Finset.mem_image]
        exact ⟨s', hs', rfl⟩)
      have hwt : wordPerm P l t = P.reflectionPerm s' s' :=
        P.root.injective (by rw [root_wordPerm, hroot])
      refine ⟨l ++ [t], ?_, fun x hx => ?_⟩
      · intro c hc
        rcases List.mem_append.mp hc with h | h
        · exact hl c h
        · rw [List.mem_singleton.mp h]
          exact ht
      · obtain ⟨z, hz, hzroot⟩ := hmap (P.reflectionPerm s' x) (by
          rw [hb'', RootPairing.Base.support_map_eq, Finset.mem_image]
          exact ⟨x, hx, rfl⟩)
        refine ⟨z, hz, ?_⟩
        have hrx : P.root x = P.reflection s' (P.root (P.reflectionPerm s' x)) := by
          rw [RootPairing.root_reflectionPerm, RootPairing.reflection_same]
        rw [hrx, hzroot]
        have hrefl : P.reflection (P.reflectionPerm s' s') = P.reflection s' := by
          ext v
          rw [RootPairing.reflection_reflectionPerm]
          simp only [LinearEquiv.mul_apply, RootPairing.reflection_same]
        rw [← hrefl, ← hwt, reflection_wordPerm_wordReflect]
        simp only [Langlands.GroupScheme.LocalSplitCell.wordReflect, List.foldr_append,
          List.foldr_cons, List.foldr_nil]

omit [Fintype I] [Finite J] [DecidableEq J] in
theorem wordReflect_combo (l : List J) (p q : ℤ) (x y : I → ℤ) :
    Langlands.GroupScheme.LocalSplitCell.wordReflect P l (p • x + q • y) =
      p • Langlands.GroupScheme.LocalSplitCell.wordReflect P l x +
        q • Langlands.GroupScheme.LocalSplitCell.wordReflect P l y := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    change P.reflection c (Langlands.GroupScheme.LocalSplitCell.wordReflect P l (p • x + q • y)) =
      p • P.reflection c (Langlands.GroupScheme.LocalSplitCell.wordReflect P l x) +
        q • P.reflection c (Langlands.GroupScheme.LocalSplitCell.wordReflect P l y)
    rw [ih, map_add, map_zsmul, map_zsmul]

/-- **Two roots in a standard rank-two subsystem, up to the Weyl group.** For linearly
independent roots `β`, `ε` of a finite reduced root datum on `ℤ^I` and a base `b`, some word
`l` in the simple reflections of `b` and distinct simple roots `s₁`, `s₂` of `b` give
`β = w_l(p s₁ + q s₂)` and `ε = w_l(p' s₁ + q' s₂)` with natural coefficients. -/
theorem exists_word_rankTwo [P.IsReduced] (b : P.Base) {β ε : J}
    (hli : LinearIndependent ℤ ![P.root β, P.root ε]) :
    ∃ (l : List J) (s₁ s₂ : J), (∀ c ∈ l, c ∈ b.support) ∧ s₁ ∈ b.support ∧
      s₂ ∈ b.support ∧ s₁ ≠ s₂ ∧
      P.root β = Langlands.GroupScheme.LocalSplitCell.wordReflect P l (P.root s₁) ∧
      ∃ p q : ℕ, P.root ε = Langlands.GroupScheme.LocalSplitCell.wordReflect P l
        ((p : ℤ) • P.root s₁ + (q : ℤ) • P.root s₂) := by
  obtain ⟨b', c, hβ, hc, hβc, p', q', hε⟩ := exists_base_rankTwo P hli
  obtain ⟨l, hl, hmap⟩ := exists_word_of_base P b b'
  obtain ⟨s₁, hs₁, h₁⟩ := hmap β hβ
  obtain ⟨s₂, hs₂, h₂⟩ := hmap c hc
  have hne : s₁ ≠ s₂ := by
    rintro rfl
    exact hβc (P.root.injective (h₁.trans h₂.symm))
  refine ⟨l, s₁, s₂, hl, hs₁, hs₂, hne, h₁, p', q', ?_⟩
  rw [wordReflect_combo, ← h₁, ← h₂, hε, natCast_zsmul, natCast_zsmul]

end Base

end Langlands.LinearAlgebra
