import Langlands.BushnellKutzko.SplittingBasis

/-! # Coordinates of the endomorphism filtration in a splitting basis

Derived supporting definitions and lemmas for the radical filtration of a lattice chain.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u v

section Elementary

variable {F : Type u} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
variable {κ : Type*} (β : Module.Basis κ F V)

/-- The elementary endomorphism `E_{kl}(t) : v ↦ t β^*_l(v) β_k`. -/
def elementaryEnd (k l : κ) (t : F) : Module.End F V :=
  t • (β.coord l).smulRight (β k)

theorem elementaryEnd_apply (k l : κ) (t : F) (v : V) :
    elementaryEnd β k l t v = (t * β.coord l v) • β k := by
  simp [elementaryEnd, mul_smul]

theorem elementaryEnd_apply_basis [DecidableEq κ] (k l j : κ) (t : F) :
    elementaryEnd β k l t (β j) = if l = j then t • β k else 0 := by
  rw [elementaryEnd_apply, Module.Basis.coord_apply, β.repr_self]
  by_cases h : l = j
  · subst h
    simp
  · simp [h]

theorem elementaryEnd_zero (k l : κ) : elementaryEnd β k l 0 = 0 := by
  simp [elementaryEnd]

/-- Composition of matching elementary maps multiplies their coefficients. -/
theorem elementaryEnd_mul (k l j : κ) (t s : F) :
    elementaryEnd β k l t * elementaryEnd β l j s = elementaryEnd β k j (t * s) := by
  classical
  apply β.ext
  intro a
  simp only [Module.End.mul_apply, elementaryEnd_apply_basis]
  by_cases h : j = a
  · simp [h, map_smul, elementaryEnd_apply_basis, smul_smul, mul_comm]
  · simp [h]

/-- The matrix entry `x_{kl} = β^*_k(x β_l)`. -/
def entry (x : Module.End F V) (k l : κ) : F :=
  β.repr (x (β l)) k

/-- `x = ∑_{k,l} E_{kl}(x_{kl})`. -/
theorem sum_elementaryEnd_entry [Fintype κ] (x : Module.End F V) :
    ∑ k, ∑ l, elementaryEnd β k l (entry β x k l) = x := by
  classical
  apply β.ext
  intro j
  simp only [LinearMap.sum_apply, elementaryEnd_apply_basis]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, entry]
  exact β.sum_repr (x (β j))

/-- `E_{kk}(1) x E_{ll}(1) = E_{kl}(x_{kl})`. -/
theorem elementaryEnd_mul_mul (x : Module.End F V) (k l : κ) :
    elementaryEnd β k k 1 * x * elementaryEnd β l l 1 = elementaryEnd β k l (entry β x k l) := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, elementaryEnd_apply, one_mul, map_smul, entry,
    Module.Basis.coord_apply]
  rw [smul_smul, mul_comm]

/-- `tr(b E_{kl}(t)) = t b_{lk}`. -/
theorem trace_mul_elementaryEnd [Module.Free F V] [Module.Finite F V] (b : Module.End F V)
    (k l : κ) (t : F) :
    LinearMap.trace F V (b * elementaryEnd β k l t) = t * entry β b l k := by
  have h : b * elementaryEnd β k l t = t • (β.coord l).smulRight (b (β k)) := by
    apply LinearMap.ext
    intro v
    simp [elementaryEnd]
  rw [h, map_smul, LinearMap.trace_smulRight, smul_eq_mul, entry, Module.Basis.coord_apply]

end Elementary

/-! ### Elementary endomorphisms and the filtration of a split lattice chain -/

section Filtration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
variable {V : Type v} [AddCommGroup V] [Module F V]
variable {κ : Type*} [Fintype κ]

theorem ordOf_one : ordOf hϖ (1 : F) = 0 := by
  simpa using ordOf_zpow hϖ 0

namespace LatticeChain

variable (𝓛 : LatticeChain 𝒪[F] F V)

/-- For a basis splitting `𝓛` and `t ≠ 0`, `E_{kl}(t) ∈ 𝔓^j(𝓛)` if and only if
`j + ν(β_l) ≤ e ord(t) + ν(β_k)`. -/
theorem elementaryEnd_mem_iff {β : Module.Basis κ F V} (hβ : 𝓛.Splits β) (k l : κ)
    {t : F} (ht : t ≠ 0) (j : ℤ) :
    elementaryEnd β k l t ∈ 𝓛.endFiltration j ↔
      j + 𝓛.index hϖ (β l) ≤ 𝓛.period * ordOf hϖ t + 𝓛.index hϖ (β k) := by
  classical
  constructor
  · intro h
    have h1 := h _ _ (𝓛.mem_lattice_index hϖ (β.ne_zero l))
    rw [elementaryEnd_apply_basis, ite_eq_left_iff.2 (fun h => absurd rfl h),
      𝓛.mem_iff_le_index hϖ (smul_ne_zero ht (β.ne_zero k)),
      𝓛.index_smul hϖ ht (β.ne_zero k)] at h1
    omega
  · intro h i v hv
    rw [elementaryEnd_apply]
    by_cases hc : β.coord l v = 0
    · rw [hc, mul_zero, zero_smul]
      exact zero_mem _
    have h1 : β.coord l v • β l ∈ 𝓛.lattice i :=
      hβ (fun m => β.repr v m) i (by rw [β.sum_repr]; exact hv) l
    rw [𝓛.mem_iff_le_index hϖ (smul_ne_zero hc (β.ne_zero l)),
      𝓛.index_smul hϖ hc (β.ne_zero l)] at h1
    rw [𝓛.mem_iff_le_index hϖ (smul_ne_zero (mul_ne_zero ht hc) (β.ne_zero k)),
      𝓛.index_smul hϖ (mul_ne_zero ht hc) (β.ne_zero k), ordOf_mul hϖ ht hc, mul_add]
    omega

include hϖ in
theorem elementaryEnd_diag_mem_order {β : Module.Basis κ F V} (hβ : 𝓛.Splits β)
    (k : κ) : elementaryEnd β k k 1 ∈ 𝓛.endFiltration 0 := by
  rw [𝓛.elementaryEnd_mem_iff hϖ hβ k k one_ne_zero, ordOf_one hϖ]
  omega

/-- The entries of an element of `𝔓^j(𝓛)` in a splitting basis. -/
theorem le_of_mem_endFiltration {β : Module.Basis κ F V} (hβ : 𝓛.Splits β)
    {x : Module.End F V} {j : ℤ} (hx : x ∈ 𝓛.endFiltration j) (k l : κ)
    (hkl : entry β x k l ≠ 0) :
    j + 𝓛.index hϖ (β l) ≤ 𝓛.period * ordOf hϖ (entry β x k l) + 𝓛.index hϖ (β k) := by
  rw [← 𝓛.elementaryEnd_mem_iff hϖ hβ k l hkl, ← elementaryEnd_mul_mul]
  have h := 𝓛.mul_mem_endFiltration
    (𝓛.mul_mem_endFiltration (𝓛.elementaryEnd_diag_mem_order hϖ hβ k) hx)
    (𝓛.elementaryEnd_diag_mem_order hϖ hβ l)
  simpa using h

end LatticeChain

end Filtration


end Langlands.BushnellKutzko
