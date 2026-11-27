import Langlands.Algebra.ParabolicCenterProjectionGrading

/-! # The Levi factor of grading data and its Harish-Chandra projection -/

noncomputable section

universe v w

set_option autoImplicit false

namespace Langlands.Algebra.ParabolicCenterProjection.GradingData

open LieAlgebra Langlands.Algebra.LieWeightProjection

variable {g : Type v} [LieRing g] [LieAlgebra ℂ g] {H : g} (D : GradingData g H)
  {m : Type w} [LieRing m] [LieAlgebra ℂ m] {j : m →ₗ⁅ℂ⁆ g}

/-- The indices of the basis vectors commuting with `H`. -/
abbrev leviIndex : Type v := {i : D.ι // D.wt i ⟨H, D.H_mem⟩ = 0}

theorem lie_H_basis_levi (i : D.leviIndex) : ⁅H, D.basis i.1⁆ = 0 := by
  have := D.lie_basis i.1 ⟨H, D.H_mem⟩
  rw [i.2, zero_smul] at this
  exact this

variable (hj : Function.Injective j) (hrange : ∀ X : g, X ∈ Set.range j ↔ ⁅H, X⁆ = 0)

include hrange in
theorem exists_levi_preimage (i : D.leviIndex) : ∃ x : m, j x = D.basis i.1 :=
  (hrange _).mpr (D.lie_H_basis_levi i)

/-- The preimages in `m` of the basis vectors commuting with `H`. -/
def leviFamily (i : D.leviIndex) : m := (D.exists_levi_preimage hrange i).choose

theorem j_leviFamily (i : D.leviIndex) : j (D.leviFamily hrange i) = D.basis i.1 :=
  (D.exists_levi_preimage hrange i).choose_spec

theorem linearIndependent_leviFamily : LinearIndependent ℂ (D.leviFamily hrange) := by
  apply LinearIndependent.of_comp j.toLinearMap
  have : (j.toLinearMap : m → g) ∘ D.leviFamily hrange = D.basis ∘ Subtype.val :=
    funext fun i => D.j_leviFamily hrange i
  rw [this]
  exact D.basis.linearIndependent.comp _ Subtype.val_injective

include hj in
theorem top_le_span_leviFamily : ⊤ ≤ Submodule.span ℂ (Set.range (D.leviFamily hrange)) := by
  classical
  intro x _
  have hx : j x ∈ Submodule.span ℂ (D.basis '' {i | D.wt i ⟨H, D.H_mem⟩ = 0}) :=
    mem_eigenSpan_of_ad D.basis (fun i => D.wt i ⟨H, D.H_mem⟩) H
      (fun i => D.lie_basis i ⟨H, D.H_mem⟩) 0 (by rw [(hrange _).mp ⟨x, rfl⟩, zero_smul])
  have hmap : Submodule.span ℂ (D.basis '' {i | D.wt i ⟨H, D.H_mem⟩ = 0}) =
      (Submodule.span ℂ (Set.range (D.leviFamily hrange))).map j.toLinearMap := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨D.leviFamily hrange ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, D.j_leviFamily hrange ⟨a, ha⟩⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a.1, a.2, (D.j_leviFamily hrange a).symm⟩
  rw [hmap] at hx
  obtain ⟨y, hy, hjy⟩ := hx
  rw [← hj hjy]
  exact hy

/-- The basis of the Levi factor `m` mapping to the basis vectors commuting with `H`. -/
def leviBasis : Module.Basis D.leviIndex ℂ m :=
  Module.Basis.mk (D.linearIndependent_leviFamily hrange) (D.top_le_span_leviFamily hj hrange)

theorem j_leviBasis (i : D.leviIndex) : j (D.leviBasis hj hrange i) = D.basis i.1 := by
  rw [leviBasis, Module.Basis.mk_apply]
  exact D.j_leviFamily hrange i

/-- The coordinates of `j x` are those of `x`. -/
theorem repr_j (x : m) (i : D.leviIndex) :
    D.basis.repr (j x) i.1 = (D.leviBasis hj hrange).repr x i := by
  classical
  conv_lhs => rw [← (D.leviBasis hj hrange).sum_repr x]
  simp only [map_sum, map_smul, D.j_leviBasis, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro a _ ha
    rw [ite_eq_right (fun h => ha (Subtype.ext h))]
  · simp

include hj hrange in
theorem repr_j_eq_zero (x : m) {c : D.ι} (hc : D.wt c ⟨H, D.H_mem⟩ ≠ 0) :
    D.basis.repr (j x) c = 0 := by
  classical
  conv_lhs => rw [← (D.leviBasis hj hrange).sum_repr x]
  simp only [map_sum, map_smul, D.j_leviBasis, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  have hac : ¬ (a : D.ι) = c := fun h => hc (by rw [← h]; exact a.2)
  rw [ite_eq_right hac, mul_zero]

/-- The grading on the Levi indices. -/
def φm (i : D.leviIndex) : ℝ := D.φ i.1

/-- The eigenvalues of the regular element on the Levi basis. -/
def evm (i : D.leviIndex) : ℂ := D.ev i.1

theorem re_evm (i : D.leviIndex) : Complex.reAddGroupHom (D.evm i) = D.φm i := rfl

theorem lie_H_reg : ⁅H, (D.reg : g)⁆ = 0 := D.lie_eq_zero H D.H_mem _ D.reg.2

/-- The regular element as an element of the Levi factor. -/
def regLevi : m := ((hrange (D.reg : g)).mpr D.lie_H_reg).choose

theorem j_regLevi : j (D.regLevi hrange) = D.reg := ((hrange (D.reg : g)).mpr D.lie_H_reg).choose_spec

theorem lie_regLevi (i : D.leviIndex) :
    ⁅D.regLevi hrange, D.leviBasis hj hrange i⁆ = D.evm i • D.leviBasis hj hrange i := by
  apply hj
  rw [LieHom.map_lie, D.j_regLevi, D.j_leviBasis, D.lie_reg, map_smul, D.j_leviBasis]
  rfl

/-- The invariant form pulled back to the Levi factor. -/
def leviForm : LinearMap.BilinForm ℂ m := D.form.compl₁₂ j.toLinearMap j.toLinearMap

theorem leviForm_apply (x y : m) : D.leviForm (j := j) x y = D.form (j x) (j y) := rfl

/-- The preimage in `m` of the vector `T γ` of `cartan`. -/
def leviDualOf (γ : D.cartan →ₗ[ℂ] ℂ) : m :=
  ((hrange (D.dualOf γ)).mpr (D.lie_dualOf γ ⟨H, D.H_mem⟩)).choose

theorem j_leviDualOf (γ : D.cartan →ₗ[ℂ] ℂ) : j (D.leviDualOf hrange γ) = D.dualOf γ :=
  ((hrange (D.dualOf γ)).mpr (D.lie_dualOf γ ⟨H, D.H_mem⟩)).choose_spec

include hj in
theorem leviForm_separating (v : m)
    (hv : ∀ e, D.leviForm (j := j) (D.leviBasis hj hrange e) v = 0) : v = 0 := by
  have hjv : ⁅H, j v⁆ = 0 := (hrange _).mp ⟨v, rfl⟩
  have hall : ∀ c, D.form (D.basis c) (j v) = 0 := by
    intro c
    by_cases hc : D.wt c ⟨H, D.H_mem⟩ = 0
    · have := hv ⟨c, hc⟩
      rwa [leviForm_apply, D.j_leviBasis] at this
    · have h1 := form_lie_add_form_lie D.form D.invariant H (D.basis c) (j v)
      have h2 := D.lie_basis c ⟨H, D.H_mem⟩
      simp only at h2
      rw [h2, hjv, map_zero, add_zero, LinearMap.BilinForm.smul_left] at h1
      exact (mul_eq_zero.mp h1).resolve_left hc
  have := D.form_basis_separating (j v) hall
  exact hj (by rw [this, map_zero])

theorem j_lie_leviBasis (e i : D.leviIndex) :
    j ⁅D.leviBasis hj hrange e, D.leviBasis hj hrange i⁆ = ⁅D.basis e.1, D.basis i.1⁆ := by
  rw [LieHom.map_lie, D.j_leviBasis, D.j_leviBasis]

/-- The nondegeneracy hypothesis of the vanishing theorem for central elements, for the Levi
factor. -/
theorem exists_shiftPart_ne_zero_levi (t : MvPolynomial D.leviIndex ℂ) (ht : t ≠ 0)
    (htpos : ∀ α ∈ t.support, ∃ i, 0 < D.φm i ∧ α i ≠ 0) :
    ∃ y, MvPolynomialDerivationGrading.shiftPart (LieCenterProjectionInjective.letterWeight D.φm)
      (LieEnvelopingSymbol.adDer (D.leviBasis hj hrange) y) (-1) t ≠ 0 := by
  refine LieCenterProjectionInjective.exists_shiftPart_ne_zero (D.leviBasis hj hrange) D.φm
    (fun i => D.wt i.1) (D.leviForm (j := j)) (D.leviDualOf hrange)
    (D.leviForm_separating hj hrange) (fun e i h => ?_) (fun e i h => ?_) (fun e i c h => ?_)
    (fun e i c _ _ hc => ?_) (fun i hi => ?_) (fun γ c hc => ?_) t ht htpos
  · rw [leviForm_apply, D.j_leviBasis, D.j_leviBasis] at h
    exact D.wt_eq_neg_of_form_ne_zero h
  · rw [leviForm_apply, D.j_leviBasis, D.j_leviBasis] at h
    exact D.φ_eq_neg_of_form_ne_zero h
  · rw [← D.repr_j hj hrange, D.j_lie_leviBasis] at h
    exact D.φ_eq_add_of_repr_lie_ne_zero h
  · rw [← D.repr_j hj hrange, D.j_lie_leviBasis, ← D.repr_j hj hrange, D.j_leviDualOf,
      leviForm_apply, D.j_leviBasis, D.j_leviBasis]
    exact D.repr_lie_of_φ_eq_zero hc
  · intro h0
    apply D.dualOf_wt_ne_zero hi.ne'
    rw [← D.j_leviDualOf hrange, h0, map_zero]
  · rw [← D.repr_j hj hrange, D.j_leviDualOf]
    exact D.repr_dualOf_eq_zero γ hc

/-- The Levi indices of grading zero. -/
abbrev leviZeroIndex : Type v := {i : D.leviIndex // D.φm i = 0}

theorem j_mem_cartan_of_mem_span {x : m}
    (hx : x ∈ Submodule.span ℂ (Set.range fun a : D.leviZeroIndex => D.leviBasis hj hrange a.1)) :
    j x ∈ D.cartan := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [D.j_leviBasis]
    exact D.mem_cartan_of_φ_eq_zero a.2
  | zero => rw [map_zero]; exact D.cartan.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact D.cartan.add_mem hx hy
  | smul t x _ hx => rw [map_smul]; exact D.cartan.smul_mem t hx

/-- The Cartan subalgebra of the Levi factor: the span of the Levi basis vectors of grading
zero, an abelian Lie subalgebra. -/
def leviCartan : LieSubalgebra ℂ m where
  __ := Submodule.span ℂ (Set.range fun a : D.leviZeroIndex => D.leviBasis hj hrange a.1)
  lie_mem' {x y} hx hy := by
    have h : ⁅x, y⁆ = 0 := hj (by
      rw [LieHom.map_lie, map_zero]
      exact D.lie_eq_zero _ (D.j_mem_cartan_of_mem_span hj hrange hx) _
        (D.j_mem_cartan_of_mem_span hj hrange hy))
    rw [h]
    exact Submodule.zero_mem _

theorem leviCartan_lie_eq_zero (x y : D.leviCartan hj hrange) : ⁅x, y⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero]
  exact hj (by
    rw [LieHom.map_lie, map_zero]
    exact D.lie_eq_zero _ (D.j_mem_cartan_of_mem_span hj hrange x.2) _
      (D.j_mem_cartan_of_mem_span hj hrange y.2))

/-- The basis of the Levi Cartan subalgebra indexed by the Levi indices of grading zero. -/
def leviCartanBasis : Module.Basis D.leviZeroIndex ℂ (D.leviCartan hj hrange) :=
  (Module.Basis.span ((D.leviBasis hj hrange).linearIndependent.comp Subtype.val
    Subtype.val_injective)).map (LinearEquiv.ofEq _ _ rfl)

@[simp]
theorem incl_leviCartanBasis (a : D.leviZeroIndex) :
    (D.leviCartan hj hrange).incl (D.leviCartanBasis hj hrange a) = D.leviBasis hj hrange a.1 := by
  rw [leviCartanBasis, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

/-- The positive part of the Levi factor for the grading `φ`. -/
def leviPositive : LieSubalgebra ℂ m :=
  positiveWeightLieSubalgebra (D.leviBasis hj hrange) D.φm D.evm Complex.reAddGroupHom D.re_evm
    (D.regLevi hrange) (D.lie_regLevi hj hrange)

/-- The decomposition of `U(m)` defining the Harish-Chandra projection of the Levi factor onto its
Cartan subalgebra. -/
def leviDecomposition :
    RelativeEnvelopingDecomposition
      (Langlands.Algebra.LieEnvelopingEquiv.map (D.leviCartan hj hrange).incl) :=
  relativeEnvelopingDecomposition_of_weight (D.leviBasis hj hrange) D.φm
    (D.leviCartan hj hrange).incl (D.leviPositive hj hrange).incl (D.leviCartanBasis hj hrange)
    (positiveWeightLieBasis (D.leviBasis hj hrange) D.φm D.evm Complex.reAddGroupHom D.re_evm
      (D.regLevi hrange) (D.lie_regLevi hj hrange))
    (D.incl_leviCartanBasis hj hrange)
    (positiveWeightLieSubalgebra_incl_basis (D.leviBasis hj hrange) D.φm D.evm
      Complex.reAddGroupHom D.re_evm (D.regLevi hrange) (D.lie_regLevi hj hrange))
    D.evm Complex.reAddGroupHom D.re_evm (D.regLevi hrange) (D.lie_regLevi hj hrange)

/-- The Harish-Chandra projection of the centre of `U(m)` to `U(leviCartan)`. -/
def leviProj : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ m) →ₐ[ℂ]
    Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (D.leviCartan hj hrange)) :=
  (D.leviDecomposition hj hrange).centerProjection

theorem sub_leviProj_mem (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ m)) :
    z.val - Langlands.Algebra.LieEnvelopingEquiv.map (D.leviCartan hj hrange).incl
      (D.leviProj hj hrange z).val ∈ positiveWeightRightIdeal (D.leviBasis hj hrange) D.φm :=
  (D.leviDecomposition hj hrange).sub_centerProjection_mem z

/-- **Injectivity of the Levi Harish-Chandra projection.** -/
theorem leviProj_injective : Function.Injective (D.leviProj hj hrange) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have h := D.sub_leviProj_mem hj hrange z
  rw [hz, ZeroMemClass.coe_zero, map_zero, sub_zero] at h
  apply Subtype.ext
  exact LieCenterProjectionInjective.center_eq_zero_of_mem_positiveWeightRightIdeal
    (D.leviBasis hj hrange) D.φm D.evm Complex.reAddGroupHom D.re_evm (D.regLevi hrange)
    (D.lie_regLevi hj hrange) (D.exists_shiftPart_ne_zero_levi hj hrange) z h

end Langlands.Algebra.ParabolicCenterProjection.GradingData
