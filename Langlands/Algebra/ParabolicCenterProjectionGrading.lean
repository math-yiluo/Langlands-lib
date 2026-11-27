import Langlands.Algebra.ReductiveGradingData
import Langlands.Algebra.LieCenterProjectionInjective

/-! # Consequences of grading data: weights, dual bases and the Cartan part of brackets -/

noncomputable section

universe v

set_option autoImplicit false

namespace Langlands.Algebra.ParabolicCenterProjection.GradingData

open LieAlgebra Langlands.Algebra.LieWeightProjection

variable {g : Type v} [LieRing g] [LieAlgebra ℂ g] {H : g} (D : GradingData g H)

/-- The real grading `φ i = Re (wt i reg)`. -/
def φ (i : D.ι) : ℝ := (D.wt i D.reg).re

/-- The eigenvalues of `ad reg` on the basis. -/
def ev (i : D.ι) : ℂ := D.wt i D.reg

theorem re_ev (i : D.ι) : Complex.reAddGroupHom (D.ev i) = D.φ i := rfl

theorem lie_reg (i : D.ι) : ⁅(D.reg : g), D.basis i⁆ = D.ev i • D.basis i := D.lie_basis i D.reg

theorem φ_eq_zero_iff (i : D.ι) : D.φ i = 0 ↔ D.wt i = 0 := D.re_wt_reg_eq_zero_iff i

theorem mem_cartan_of_φ_eq_zero {i : D.ι} (hi : D.φ i = 0) : D.basis i ∈ D.cartan :=
  D.mem_of_wt_eq_zero i ((D.φ_eq_zero_iff i).mp hi)

theorem wt_eq_of_repr_ne_zero {x : g} {μ : D.cartan → ℂ}
    (hx : ∀ h : D.cartan, ⁅(h : g), x⁆ = μ h • x) {c : D.ι} (hc : D.basis.repr x c ≠ 0) :
    ∀ h, D.wt c h = μ h :=
  ParabolicCenterProjection.wt_eq_of_repr_ne_zero D.lie_basis hx hc

/-- A vector commuting with `cartan` has coordinates only on basis vectors of grading zero. -/
theorem φ_eq_zero_of_repr_ne_zero {x : g} (hx : ∀ h : D.cartan, ⁅(h : g), x⁆ = 0)
    {c : D.ι} (hc : D.basis.repr x c ≠ 0) : D.φ c = 0 := by
  rw [φ_eq_zero_iff]
  ext h
  have := D.wt_eq_of_repr_ne_zero (μ := fun _ => 0) (fun h => by rw [hx, zero_smul]) hc h
  simpa using this

theorem wt_eq_neg_of_form_ne_zero {e i : D.ι} (h0 : D.form (D.basis e) (D.basis i) ≠ 0) :
    D.wt e = -D.wt i :=
  ParabolicCenterProjection.wt_eq_neg_of_form_ne_zero D.lie_basis D.form D.invariant h0

theorem φ_eq_neg_of_form_ne_zero {e i : D.ι} (h0 : D.form (D.basis e) (D.basis i) ≠ 0) :
    D.φ e = -D.φ i := by
  simp [φ, D.wt_eq_neg_of_form_ne_zero h0]

theorem φ_eq_add_of_repr_lie_ne_zero {e i c : D.ι}
    (hc : D.basis.repr ⁅D.basis e, D.basis i⁆ c ≠ 0) : D.φ c = D.φ e + D.φ i := by
  have h := D.wt_eq_of_repr_ne_zero (μ := fun h => D.wt e h + D.wt i h)
    (fun h => lie_basis_eig D.lie_basis e i h) hc D.reg
  simp only [φ, h, Complex.add_re]

/-- A vector is determined by its pairings with the basis. -/
theorem eq_of_form_basis {x y : g} (h : ∀ c, D.form x (D.basis c) = D.form y (D.basis c)) :
    x = y := by
  rw [← sub_eq_zero]
  refine D.nondegenerate.1 _ fun z => ?_
  rw [← D.basis.sum_repr z, map_sub, LinearMap.sub_apply, map_sum, map_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, map_smul, h c]

/-- The dual basis for the invariant form. -/
def dual : Module.Basis D.ι ℂ g := D.form.dualBasis D.nondegenerate D.basis

theorem form_dual (i c : D.ι) : D.form (D.dual i) (D.basis c) = if c = i then 1 else 0 :=
  LinearMap.BilinForm.apply_dualBasis_left _ _ _ _

/-- The dual basis vector `b^i` has weight `-wt i`. -/
theorem lie_dual (i : D.ι) (h : D.cartan) : ⁅(h : g), D.dual i⁆ = -(D.wt i h) • D.dual i := by
  apply D.eq_of_form_basis
  intro c
  have h1 := form_lie_add_form_lie D.form D.invariant (h : g) (D.dual i) (D.basis c)
  rw [D.lie_basis, map_smul, D.form_dual, smul_eq_mul] at h1
  rw [eq_neg_of_add_eq_zero_left h1, LinearMap.BilinForm.smul_left, D.form_dual]
  split_ifs with hc
  · subst hc; ring
  · ring

theorem φ_eq_neg_of_repr_dual_ne_zero {i c : D.ι} (hc : D.basis.repr (D.dual i) c ≠ 0) :
    D.φ c = -D.φ i := by
  have h := D.wt_eq_of_repr_ne_zero (μ := fun h => -(D.wt i h)) (fun h => D.lie_dual i h) hc D.reg
  simp only [φ, h, Complex.neg_re]

/-- The vector of `cartan` dual to a linear form `γ` on `cartan`:
`T γ = ∑_{φ c = 0} γ(b c) b^c`. -/
def dualOf (γ : D.cartan →ₗ[ℂ] ℂ) : g :=
  ∑ c : {c : D.ι // D.φ c = 0}, γ ⟨D.basis c, D.mem_cartan_of_φ_eq_zero c.2⟩ • D.dual c

theorem repr_dualOf_eq_zero (γ : D.cartan →ₗ[ℂ] ℂ) {c : D.ι} (hc : D.φ c ≠ 0) :
    D.basis.repr (D.dualOf γ) c = 0 := by
  simp only [dualOf, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : D.basis.repr (D.dual a) c = 0
  · rw [ha, mul_zero]
  · exact absurd (by rw [D.φ_eq_neg_of_repr_dual_ne_zero ha, a.2, neg_zero]) hc

theorem form_dualOf (γ : D.cartan →ₗ[ℂ] ℂ) {c : D.ι} (hc : D.φ c = 0) :
    D.form (D.dualOf γ) (D.basis c) = γ ⟨D.basis c, D.mem_cartan_of_φ_eq_zero hc⟩ := by
  classical
  simp only [dualOf, map_sum, LinearMap.sum_apply, LinearMap.BilinForm.smul_left, D.form_dual]
  rw [Finset.sum_eq_single ⟨c, hc⟩]
  · simp
  · intro a _ ha
    rw [ite_eq_right (fun h => ha (Subtype.ext h.symm)), mul_zero]
  · simp

/-- A vector commuting with `cartan` is orthogonal to the basis vectors of nonzero grading. -/
theorem form_eq_zero_of_commute {x : g} (hx : ∀ h : D.cartan, ⁅(h : g), x⁆ = 0) {c : D.ι}
    (hc : D.φ c ≠ 0) : D.form x (D.basis c) = 0 := by
  have hwc : D.wt c ≠ 0 := fun h => hc ((D.φ_eq_zero_iff c).mpr h)
  obtain ⟨h, hh⟩ : ∃ h, D.wt c h ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hwc (LinearMap.ext hcon)
  have h1 := form_lie_add_form_lie D.form D.invariant (h : g) x (D.basis c)
  rw [hx, LinearMap.BilinForm.zero_left, zero_add, D.lie_basis, map_smul, smul_eq_mul] at h1
  exact (mul_eq_zero.mp h1).resolve_left hh

theorem lie_dualOf (γ : D.cartan →ₗ[ℂ] ℂ) (h : D.cartan) : ⁅(h : g), D.dualOf γ⁆ = 0 := by
  simp only [dualOf, lie_sum, lie_smul, D.lie_dual]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [(D.φ_eq_zero_iff c).mp c.2, LinearMap.zero_apply, neg_zero, zero_smul, smul_zero]

omit [LieRing g] [LieAlgebra ℂ g] in
theorem sum_subtype_eq_sum_of_zero {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (p : ι → Prop) [DecidablePred p] (f : ι → M) (hf : ∀ c, ¬ p c → f c = 0) :
    ∑ c : {c // p c}, f c = ∑ c, f c := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) f]
  exact Finset.sum_filter_of_ne fun c _ hc => by
    by_contra h
    exact hc (hf c h)

theorem commute_cartan (h : D.cartan) (h' : D.cartan) : ⁅(h' : g), (h : g)⁆ = 0 :=
  D.lie_eq_zero _ h'.2 _ h.2

/-- The elements of `cartan` are combinations of the basis vectors of grading zero. -/
theorem cartan_eq_sum (h : D.cartan) :
    h = ∑ c : {c : D.ι // D.φ c = 0},
      D.basis.repr h c • (⟨D.basis c, D.mem_cartan_of_φ_eq_zero c.2⟩ : D.cartan) := by
  classical
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [sum_subtype_eq_sum_of_zero (fun c => D.φ c = 0)
    (fun c => D.basis.repr h c • D.basis c) (fun c hc => by
      have : D.basis.repr h c = 0 := by
        by_contra hne
        exact hc (D.φ_eq_zero_of_repr_ne_zero (fun h' => D.commute_cartan h h') hne)
      rw [this, zero_smul])]
  exact (D.basis.sum_repr (h : g)).symm

theorem dualOf_wt_ne_zero {i : D.ι} (hi : D.φ i ≠ 0) : D.dualOf (D.wt i) ≠ 0 := by
  intro h0
  apply hi
  rw [φ_eq_zero_iff]
  ext h
  rw [D.cartan_eq_sum h, map_sum, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [map_smul, ← D.form_dualOf (D.wt i) c.2, h0, LinearMap.BilinForm.zero_left, smul_zero]

/-- **The Cartan part of a bracket.** The grading-zero coordinates of `⁅b e, b i⁆` are those of
`-B(b e, b i) T(wt i)`. -/
theorem repr_lie_of_φ_eq_zero {e i c : D.ι} (hc : D.φ c = 0) :
    D.basis.repr ⁅D.basis e, D.basis i⁆ c =
      -(D.form (D.basis e) (D.basis i) * D.basis.repr (D.dualOf (D.wt i)) c) := by
  by_cases hw : D.wt e = -D.wt i
  · set v := ⁅D.basis e, D.basis i⁆
    have hv (h : D.cartan) : ⁅(h : g), v⁆ = 0 := by
      rw [lie_basis_eig D.lie_basis, hw, LinearMap.neg_apply, neg_add_cancel, zero_smul]
    have hw0 : v + D.form (D.basis e) (D.basis i) • D.dualOf (D.wt i) = 0 := by
      apply D.eq_of_form_basis
      intro c'
      rw [LinearMap.BilinForm.zero_left]
      by_cases hc' : D.φ c' = 0
      · rw [map_add, LinearMap.add_apply, LinearMap.BilinForm.smul_left, D.form_dualOf _ hc',
          D.invariant, ← lie_skew, map_neg]
        have := D.lie_basis i ⟨D.basis c', D.mem_cartan_of_φ_eq_zero hc'⟩
        simp only at this
        rw [this, map_smul, smul_eq_mul]
        ring
      · rw [map_add, LinearMap.add_apply, D.form_eq_zero_of_commute hv hc',
          LinearMap.BilinForm.smul_left, D.form_eq_zero_of_commute (D.lie_dualOf _) hc',
          mul_zero, add_zero]
    have hv' : v = -(D.form (D.basis e) (D.basis i) • D.dualOf (D.wt i)) :=
      eq_neg_of_add_eq_zero_left hw0
    rw [hv', map_neg, map_smul, Finsupp.neg_apply, Finsupp.smul_apply, smul_eq_mul]
  · have hB : D.form (D.basis e) (D.basis i) = 0 := by
      by_contra hne
      exact hw (D.wt_eq_neg_of_form_ne_zero hne)
    rw [hB, zero_mul, neg_zero]
    by_contra hne
    have h1 := D.wt_eq_of_repr_ne_zero (μ := fun h => D.wt e h + D.wt i h)
      (fun h => lie_basis_eig D.lie_basis e i h) hne
    apply hw
    ext h
    have h2 := h1 h
    rw [(D.φ_eq_zero_iff c).mp hc, LinearMap.zero_apply] at h2
    rw [LinearMap.neg_apply]
    exact eq_neg_of_add_eq_zero_left h2.symm

/-- The invariant form separates points through the basis. -/
theorem form_basis_separating (v : g) (hv : ∀ e, D.form (D.basis e) v = 0) : v = 0 := by
  apply D.eq_of_form_basis
  intro c
  rw [D.isSymm.eq, hv, LinearMap.BilinForm.zero_left]

/-- The nondegeneracy hypothesis of the vanishing theorem for central elements, for `g`. -/
theorem exists_shiftPart_ne_zero_g (t : MvPolynomial D.ι ℂ) (ht : t ≠ 0)
    (htpos : ∀ α ∈ t.support, ∃ i, 0 < D.φ i ∧ α i ≠ 0) :
    ∃ y, MvPolynomialDerivationGrading.shiftPart (LieCenterProjectionInjective.letterWeight D.φ)
      (LieEnvelopingSymbol.adDer D.basis y) (-1) t ≠ 0 :=
  LieCenterProjectionInjective.exists_shiftPart_ne_zero D.basis D.φ D.wt D.form D.dualOf
    D.form_basis_separating (fun _ _ h => D.wt_eq_neg_of_form_ne_zero h)
    (fun _ _ h => D.φ_eq_neg_of_form_ne_zero h) (fun _ _ _ h => D.φ_eq_add_of_repr_lie_ne_zero h)
    (fun _ _ _ _ _ hc => D.repr_lie_of_φ_eq_zero hc)
    (fun _ hi => D.dualOf_wt_ne_zero hi.ne') (fun γ _ hc => D.repr_dualOf_eq_zero γ hc) t ht htpos

/-- A vector commuting with `cartan` lies in `cartan`. -/
theorem mem_cartan_of_commute {x : g} (hx : ∀ h : D.cartan, ⁅(h : g), x⁆ = 0) : x ∈ D.cartan := by
  rw [← D.basis.sum_repr x]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : D.basis.repr x c = 0
  · rw [hc, zero_smul]; exact D.cartan.zero_mem
  · exact D.cartan.smul_mem _ (D.mem_cartan_of_φ_eq_zero (D.φ_eq_zero_of_repr_ne_zero hx hc))

theorem dualOf_mem_cartan (γ : D.cartan →ₗ[ℂ] ℂ) : D.dualOf γ ∈ D.cartan :=
  D.mem_cartan_of_commute (D.lie_dualOf γ)

theorem center_le_cartan : (center ℂ g : Submodule ℂ g) ≤ D.cartan := fun c hc =>
  D.mem_cartan_of_commute fun h => (LieModule.mem_maxTrivSubmodule ℂ g g c).mp hc h

/-- `T γ` represents `γ` on `cartan` through the invariant form. -/
theorem form_dualOf_cartan (γ : D.cartan →ₗ[ℂ] ℂ) (h : D.cartan) : D.form (D.dualOf γ) h = γ h := by
  conv_rhs => rw [D.cartan_eq_sum h]
  conv_lhs => rw [D.cartan_eq_sum h]
  rw [Submodule.coe_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Submodule.coe_smul, map_smul, map_smul, D.form_dualOf γ c.2]

/-- **The Cartan subspace is spanned by the vectors `T(wt q)` and the centre.** -/
theorem cartan_le_span_dualOf_sup_center [FiniteDimensional ℂ g] :
    D.cartan ≤ Submodule.span ℂ (Set.range fun q => D.dualOf (D.wt q)) ⊔
      (center ℂ g : Submodule ℂ g) := by
  classical
  set W : Submodule ℂ g := Submodule.span ℂ (Set.range fun q => D.dualOf (D.wt q)) ⊔
      (center ℂ g : Submodule ℂ g)
  let W' : Submodule ℂ D.cartan := W.comap D.cartan.subtype
  suffices hW : W' = ⊤ by
    intro h hh
    have : (⟨h, hh⟩ : D.cartan) ∈ W' := hW ▸ Submodule.mem_top
    exact this
  let B' := D.form.restrict D.cartan
  have hsepB : ∀ x : D.cartan, (∀ y : D.cartan, B' x y = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    apply D.form_basis_separating
    intro c
    rw [D.isSymm.eq]
    by_cases hc : D.φ c = 0
    · exact hx ⟨D.basis c, D.mem_cartan_of_φ_eq_zero hc⟩
    · exact D.form_eq_zero_of_commute (fun h => D.commute_cartan x h) hc
  have hB' : B'.Nondegenerate := ⟨hsepB, fun y hy => hsepB y fun x => by
    have h1 := hy x
    change D.form x y = 0 at h1
    change D.form y x = 0
    rw [D.isSymm.eq]
    exact h1⟩
  by_contra hne
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne)
    inferInstance
  have hfW' : ∀ x ∈ W', f x = 0 := fun x hx => by
    have : f x ∈ W'.map f := ⟨x, hx, rfl⟩
    rw [hfW] at this
    exact this
  let h₀ : D.cartan := (B'.toDual hB').symm f
  have hf (x : D.cartan) : f x = D.form (h₀ : g) (x : g) :=
    (LinearMap.BilinForm.apply_toDual_symm_apply (B := B') (hB := hB') f x).symm
  have hwt (q : D.ι) : D.wt q h₀ = 0 := by
    rw [← D.form_dualOf_cartan, D.isSymm.eq]
    rw [← hf ⟨D.dualOf (D.wt q), D.dualOf_mem_cartan _⟩]
    exact hfW' ⟨D.dualOf (D.wt q), D.dualOf_mem_cartan _⟩
      (Submodule.mem_sup_left (Submodule.subset_span ⟨q, rfl⟩))
  have hcen : (h₀ : g) ∈ center ℂ g := by
    rw [LieModule.mem_maxTrivSubmodule]
    intro x
    rw [← D.basis.sum_repr x, sum_lie]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [smul_lie, ← lie_skew, D.lie_basis, hwt, zero_smul, neg_zero, smul_zero]
  have hzero : (h₀ : g) = 0 := D.center_nondegenerate _ hcen fun c hc => by
    rw [← hf ⟨c, D.center_le_cartan hc⟩]
    exact hfW' _ (Submodule.mem_sup_right hc)
  apply hf0
  ext x
  rw [hf, hzero, LinearMap.BilinForm.zero_left, LinearMap.zero_apply]

end Langlands.Algebra.ParabolicCenterProjection.GradingData
