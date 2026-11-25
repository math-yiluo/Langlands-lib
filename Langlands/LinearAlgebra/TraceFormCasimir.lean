import Langlands.MathlibBase

/-! # Casimir elements of dual families and the trace-form radical -/

noncomputable section

open Module

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.LinearAlgebra.TraceFormCasimir

section Commute

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- Let `T` be a linear form with `T (x y) = T (y x)`, and let `b`, `d` be finite families in
a subspace `g` such that every `v ∈ g` expands as `v = ∑ T (v d_a) b_a` and as
`v = ∑ T (b_a v) d_a`. Then the Casimir element `∑ b_a d_a` commutes with every `x` whose
commutators with all `b_a` and all `d_a` lie in `g`. -/
theorem commute_sum_mul {ι : Type*} [Fintype ι] (T : A →ₗ[k] k)
    (hT : ∀ x y, T (x * y) = T (y * x)) (g : Submodule k A) (b d : ι → A)
    (h1 : ∀ v ∈ g, v = ∑ a, T (v * d a) • b a) (h2 : ∀ v ∈ g, v = ∑ a, T (b a * v) • d a)
    {x : A} (hxb : ∀ a, x * b a - b a * x ∈ g) (hxd : ∀ a, x * d a - d a * x ∈ g) :
    Commute x (∑ a, b a * d a) := by
  have key : ∀ a c, T ((x * b a - b a * x) * d c) + T (b a * (x * d c - d c * x)) = 0 := by
    intro a c
    rw [sub_mul, mul_sub, map_sub, map_sub, mul_assoc, ← mul_assoc (b a) x, ← mul_assoc (b a) (d c),
      hT x (b a * d c)]
    abel
  have e1 : ∀ a, (x * b a - b a * x) * d a =
      ∑ c, T ((x * b a - b a * x) * d c) • (b c * d a) := by
    intro a
    conv_lhs => rw [h1 _ (hxb a)]
    rw [Finset.sum_mul]
    simp_rw [smul_mul_assoc]
  have e2 : ∀ a, b a * (x * d a - d a * x) =
      ∑ c, T (b c * (x * d a - d a * x)) • (b a * d c) := by
    intro a
    conv_lhs => rw [h2 _ (hxd a)]
    rw [Finset.mul_sum]
    simp_rw [mul_smul_comm]
  have hsplit : x * (∑ a, b a * d a) - (∑ a, b a * d a) * x =
      ∑ a, ((x * b a - b a * x) * d a + b a * (x * d a - d a * x)) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [sub_mul, mul_sub, mul_assoc]
    abel
  rw [Commute, SemiconjBy, ← sub_eq_zero, hsplit]
  simp_rw [e1, e2]
  rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun a c =>
    T (b c * (x * d a - d a * x)) • (b a * d c)), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [← add_smul, key, zero_smul]

end Commute

section Radical

variable {k U : Type*} [Field k] [CharZero k] [AddCommGroup U] [Module k U]
  [FiniteDimensional k U]

omit [CharZero k] [FiniteDimensional k U] in
theorem toEnd_eq (g : LieSubalgebra k (Module.End k U)) (x : g) :
    LieModule.toEnd k g U x = (x : Module.End k U) := by
  ext u
  rfl

omit [CharZero k] [FiniteDimensional k U] in
theorem traceForm_eq (g : LieSubalgebra k (Module.End k U)) (x y : g) :
    LieModule.traceForm k g U x y = LinearMap.trace k U ((x : Module.End k U) * y) := by
  rw [LieModule.traceForm_apply_apply, toEnd_eq, toEnd_eq]
  rfl

/-- If a Lie algebra `g` of endomorphisms of a finite-dimensional space in characteristic zero
has no nonzero ideal of nilpotent endomorphisms, any two elements of `g` that are orthogonal
to all of `g` under the trace form commute. This is Cartan's criterion applied to the
radical of the trace form. -/
theorem commute_of_trace_mul_eq_zero (g : LieSubalgebra k (Module.End k U))
    (hN : ∀ I : LieIdeal k g, (∀ x ∈ I, IsNilpotent ((x : g) : Module.End k U)) → I = ⊥)
    {x y : Module.End k U} (hx : x ∈ g) (hy : y ∈ g)
    (hx' : ∀ z ∈ g, LinearMap.trace k U (x * z) = 0)
    (hy' : ∀ z ∈ g, LinearMap.trace k U (y * z) = 0) : Commute x y := by
  let R : LieIdeal k g := LieAlgebra.InvariantForm.orthogonal (LieModule.traceForm k g U)
    (LieModule.traceForm_lieInvariant k g U) ⊤
  have hmemR : ∀ (z : Module.End k U) (hz : z ∈ g),
      (∀ w ∈ g, LinearMap.trace k U (z * w) = 0) → (⟨z, hz⟩ : g) ∈ R := by
    intro z hz hz'
    rw [LieAlgebra.InvariantForm.mem_orthogonal]
    intro w _
    rw [LieModule.traceForm_comm, traceForm_eq]
    exact hz' w w.2
  have hR : ∀ z : g, z ∈ R → ∀ w : g, LinearMap.trace k U ((z : Module.End k U) * w) = 0 := by
    intro z hz w
    have h := (LieAlgebra.InvariantForm.mem_orthogonal _ _ _ _).mp hz w (LieSubmodule.mem_top w)
    rwa [LieModule.traceForm_comm, traceForm_eq] at h
  have htf : LieModule.traceForm k R U = 0 := by
    ext a b
    rw [LieModule.traceForm_apply_apply, LinearMap.zero_apply, LinearMap.zero_apply]
    have ha : LieModule.toEnd k R U a = ((a : g) : Module.End k U) := by ext u; rfl
    have hb : LieModule.toEnd k R U b = ((b : g) : Module.End k U) := by ext u; rfl
    rw [ha, hb]
    exact hR a a.2 b
  have hnil := LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero htf
  rw [LieModule.isNilpotent_iff_forall' (R := k)] at hnil
  have hI : ⁅R, R⁆ = ⊥ := by
    refine hN _ fun z hz => ?_
    have hzR : z ∈ R := LieSubmodule.lie_le_left R R hz
    have hzD : (⟨z, hzR⟩ : R) ∈ LieAlgebra.derivedSeries k R 1 := by
      rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap, LieIdeal.mem_comap]
      simpa [LieAlgebra.derivedSeriesOfIdeal_succ, LieAlgebra.derivedSeriesOfIdeal_zero] using hz
    have h := hnil ⟨⟨z, hzR⟩, hzD⟩
    have he : LieModule.toEnd k (LieAlgebra.derivedSeries k R 1) U ⟨⟨z, hzR⟩, hzD⟩ =
        ((z : g) : Module.End k U) := by ext u; rfl
    rwa [he] at h
  have hxy : ⁅(⟨x, hx⟩ : g), (⟨y, hy⟩ : g)⁆ ∈ ⁅R, R⁆ :=
    LieSubmodule.lie_mem_lie (hmemR x hx hx') (hmemR y hy hy')
  rw [hI, LieSubmodule.mem_bot] at hxy
  have h := congrArg (fun z : g => (z : Module.End k U)) hxy
  simp only [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket,
    ZeroMemClass.coe_zero] at h
  exact sub_eq_zero.mp h

end Radical

end Langlands.LinearAlgebra.TraceFormCasimir
