import Langlands.BushnellKutzko.RadicalFiltrationStatement
import Langlands.BushnellKutzko.UnitFiltration
import Langlands.BushnellKutzko.FiltrationCoordinates

/-! # The radical filtration of a lattice-chain order -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u v

namespace LatticeChain

section General

variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable (𝓛 : LatticeChain O K V)

/-- The product inclusion for the endomorphism filtration. -/
theorem endFiltration_mul_le (m n : ℤ) :
    𝓛.endFiltration m * 𝓛.endFiltration n ≤ 𝓛.endFiltration (m + n) :=
  Submodule.mul_le.2 fun _ hx _ hy => 𝓛.mul_mem_endFiltration hx hy

/-- The span of the action of a filtration step lies in the shifted lattice. -/
theorem span_endFiltration_apply_le (n i : ℤ) :
    Submodule.span O
      (Set.image2 (fun (x : Module.End K V) (w : V) => x w)
        (𝓛.endFiltration n : Set (Module.End K V)) (𝓛.lattice i : Set V)) ≤
      𝓛.lattice (i + n) := by
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  exact hx i w hw

/-- Positive filtration elements belong to the Jacobson radical of the order. -/
theorem mem_jacobson_of_mem_endFiltration_one (x : 𝓛.order)
    (hx : (x : Module.End K V) ∈ 𝓛.endFiltration 1) : x ∈ Ring.jacobson 𝓛.order := by
  rw [← Ideal.jacobson_bot]
  apply Ideal.mem_jacobson_iff.2
  intro y
  have hxy : (y : Module.End K V) * (x : Module.End K V) ∈ 𝓛.endFiltration 1 := by
    simpa using 𝓛.mul_mem_endFiltration (m := 0) y.2 hx
  obtain ⟨g, hg, hgy⟩ := 𝓛.exists_mem_unitFiltration (n := 1) le_rfl hxy
  let z : 𝓛.order := ⟨((g⁻¹ : (Module.End K V)ˣ) : Module.End K V), hg.2.1⟩
  have hz : z * (y * x + 1) = 1 := by
    apply Subtype.ext
    change ((g⁻¹ : (Module.End K V)ˣ) : Module.End K V) *
      ((y : Module.End K V) * (x : Module.End K V) + 1) = 1
    rw [add_comm, ← hgy]
    exact g.inv_mul
  refine ⟨z, ?_⟩
  rw [Ideal.mem_bot]
  calc
    z * y * x + z - 1 = z * (y * x + 1) - 1 := by noncomm_ring
    _ = 0 := by rw [hz, sub_self]

end General

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (𝓛 : LatticeChain 𝒪[F] F V)
variable {κ : Type*} [Fintype κ] {β : Module.Basis κ F V} (hβ : 𝓛.Splits β)

include hβ in
/-- Strictness forces every integer to occur as the index of a scaled basis vector. -/
theorem exists_scaled_basis_index (i : ℤ) :
    ∃ (k : κ) (c : F), c ≠ 0 ∧ 𝓛.index hϖ (c • β k) = i := by
  classical
  obtain ⟨v, hv, hv'⟩ := SetLike.exists_of_lt (𝓛.lattice_succ_lt i)
  have hex : ∃ k, β.repr v k • β k ∉ 𝓛.lattice (i + 1) := by
    by_contra h
    push Not at h
    apply hv'
    rw [← β.sum_repr v]
    exact sum_mem fun k _ => h k
  obtain ⟨k, hk⟩ := hex
  have hc : β.repr v k ≠ 0 := by
    intro hc
    apply hk
    rw [hc, zero_smul]
    exact zero_mem _
  have hmem := hβ (fun j => β.repr v j) i (by rw [β.sum_repr]; exact hv) k
  have hnz := smul_ne_zero hc (β.ne_zero k)
  rw [𝓛.mem_iff_le_index hϖ hnz] at hmem hk
  exact ⟨k, β.repr v k, hc, by omega⟩

include hϖ hβ in
/-- Reverse product inclusion, by factoring elementary maps through a vector of exact index. -/
theorem endFiltration_mul_eq_of_splits (m n : ℤ) :
    𝓛.endFiltration m * 𝓛.endFiltration n = 𝓛.endFiltration (m + n) := by
  classical
  refine le_antisymm (𝓛.endFiltration_mul_le m n) ?_
  intro x hx
  rw [← sum_elementaryEnd_entry β x]
  refine sum_mem fun k _ => sum_mem fun l _ => ?_
  set t := entry β x k l with ht_def
  by_cases ht : t = 0
  · rw [ht, elementaryEnd_zero]
    exact zero_mem _
  have hdeg := 𝓛.le_of_mem_endFiltration hϖ hβ hx k l ht
  rw [← ht_def] at hdeg
  obtain ⟨a, c, hc, hi⟩ := 𝓛.exists_scaled_basis_index hϖ hβ (𝓛.index hϖ (β l) + n)
  rw [𝓛.index_smul hϖ hc (β.ne_zero a)] at hi
  have hcdeg : elementaryEnd β a l c ∈ 𝓛.endFiltration n := by
    rw [𝓛.elementaryEnd_mem_iff hϖ hβ a l hc]
    omega
  have ht' : t * c⁻¹ ≠ 0 := mul_ne_zero ht (inv_ne_zero hc)
  have htdeg : elementaryEnd β k a (t * c⁻¹) ∈ 𝓛.endFiltration m := by
    rw [𝓛.elementaryEnd_mem_iff hϖ hβ k a ht', ordOf_mul hϖ ht (inv_ne_zero hc),
      ordOf_inv hϖ hc, mul_add, mul_neg]
    omega
  have heq : elementaryEnd β k a (t * c⁻¹) * elementaryEnd β a l c =
      elementaryEnd β k l t := by
    rw [elementaryEnd_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  rw [← heq]
  exact Submodule.mul_mem_mul htdeg hcdeg

include hϖ hβ in
/-- The action of a filtration step spans exactly the shifted lattice. -/
theorem span_endFiltration_apply_eq_of_splits (n i : ℤ) :
    Submodule.span 𝒪[F]
      (Set.image2 (fun (x : Module.End F V) (w : V) => x w)
        (𝓛.endFiltration n : Set (Module.End F V)) (𝓛.lattice i : Set V)) =
      𝓛.lattice (i + n) := by
  classical
  refine le_antisymm (𝓛.span_endFiltration_apply_le n i) ?_
  intro v hv
  obtain ⟨a, c, hc, hi⟩ := 𝓛.exists_scaled_basis_index hϖ hβ i
  have hca : c • β a ∈ 𝓛.lattice i := by
    rw [𝓛.mem_iff_le_index hϖ (smul_ne_zero hc (β.ne_zero a)), hi]
  rw [𝓛.index_smul hϖ hc (β.ne_zero a)] at hi
  rw [← β.sum_repr v]
  refine sum_mem fun k _ => ?_
  set t := β.repr v k
  by_cases ht : t = 0
  · rw [ht, zero_smul]
    exact zero_mem _
  have hterm := hβ (fun j => β.repr v j) (i + n) (by rw [β.sum_repr]; exact hv) k
  rw [𝓛.mem_iff_le_index hϖ (smul_ne_zero ht (β.ne_zero k)),
    𝓛.index_smul hϖ ht (β.ne_zero k)] at hterm
  have htc : t * c⁻¹ ≠ 0 := mul_ne_zero ht (inv_ne_zero hc)
  have hE : elementaryEnd β k a (t * c⁻¹) ∈ 𝓛.endFiltration n := by
    rw [𝓛.elementaryEnd_mem_iff hϖ hβ k a htc, ordOf_mul hϖ ht (inv_ne_zero hc),
      ordOf_inv hϖ hc, mul_add, mul_neg]
    omega
  apply Submodule.subset_span
  refine ⟨elementaryEnd β k a (t * c⁻¹), hE, c • β a, hca, ?_⟩
  change elementaryEnd β k a (t * c⁻¹) (c • β a) = t • β k
  simp only [map_smul, elementaryEnd_apply_basis, ↓reduceIte, smul_smul]
  rw [mul_left_comm c t, mul_inv_cancel₀ hc, mul_one]

include hϖ in
/-- Multiplying by a uniformizer shifts the endomorphism filtration by one period. -/
theorem uniformizer_smul_mem_endFiltration_iff (x : Module.End F V) (n : ℤ) :
    (ϖ : F) • x ∈ 𝓛.endFiltration (n + 𝓛.period) ↔ x ∈ 𝓛.endFiltration n := by
  constructor
  · intro h i v hv
    have h' := h i v hv
    change (ϖ : F) • x v ∈ 𝓛.lattice (i + (n + 𝓛.period)) at h'
    rw [𝓛.uniformizer_smul_mem_iff hϖ] at h'
    simpa only [← add_assoc, add_sub_cancel_right] using h'
  · intro h i v hv
    change (ϖ : F) • x v ∈ 𝓛.lattice (i + (n + 𝓛.period))
    rw [𝓛.uniformizer_smul_mem_iff hϖ]
    simpa only [← add_assoc, add_sub_cancel_right] using h i v hv

include hϖ in
/-- The uniformizer generates a period shift of the filtration as a submodule. -/
theorem endFiltration_add_period_eq_smul (n : ℤ) :
    𝓛.endFiltration (n + 𝓛.period) = ϖ • 𝓛.endFiltration n := by
  ext x
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro hx
    let y := ((ϖ : F)⁻¹) • x
    have hyx : (ϖ : F) • y = x := by
      dsimp [y]
      rw [smul_smul, mul_inv_cancel₀ (coe_uniformizer_ne_zero hϖ), one_smul]
    refine ⟨y, ?_, ?_⟩
    · apply (𝓛.uniformizer_smul_mem_endFiltration_iff hϖ y n).1
      rwa [hyx]
    · rw [← algebraMap_smul F ϖ y]
      exact hyx
  · rintro ⟨y, hy, rfl⟩
    rw [← algebraMap_smul F ϖ y]
    exact (𝓛.uniformizer_smul_mem_endFiltration_iff hϖ y n).2 hy

include hϖ in
/-- The maximal ideal times the order is the filtration step at the period. -/
theorem maximalIdeal_smul_order_eq :
    𝓂[F] • Subalgebra.toSubmodule 𝓛.order = 𝓛.endFiltration 𝓛.period := by
  rw [hϖ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul, 𝓛.toSubmodule_order,
    ← 𝓛.endFiltration_add_period_eq_smul hϖ 0, zero_add]

include hϖ hβ in
/-- A radical element advances the chain by at least one step. -/
theorem mem_endFiltration_one_of_mem_jacobson (x : 𝓛.order)
    (hx : x ∈ Ring.jacobson 𝓛.order) : (x : Module.End F V) ∈ 𝓛.endFiltration 1 := by
  classical
  by_contra hx1
  have hbad : ∃ k l, elementaryEnd β k l (entry β (x : Module.End F V) k l) ∉
      𝓛.endFiltration 1 := by
    by_contra h
    push Not at h
    apply hx1
    rw [← sum_elementaryEnd_entry β (x : Module.End F V)]
    exact sum_mem fun k _ => sum_mem fun l _ => h k l
  obtain ⟨k, l, hkl⟩ := hbad
  let t := entry β (x : Module.End F V) k l
  change elementaryEnd β k l t ∉ _ at hkl
  have ht : t ≠ 0 := by
    intro ht
    apply hkl
    rw [ht, elementaryEnd_zero]
    exact zero_mem _
  rw [𝓛.elementaryEnd_mem_iff hϖ hβ k l ht] at hkl
  have hy0 : elementaryEnd β l k t⁻¹ ∈ 𝓛.endFiltration 0 := by
    rw [𝓛.elementaryEnd_mem_iff hϖ hβ l k (inv_ne_zero ht), ordOf_inv hϖ ht, mul_neg]
    omega
  let y : 𝓛.order := ⟨elementaryEnd β l k t⁻¹, hy0⟩
  have hyx : (y : Module.End F V) ((x : Module.End F V) (β l)) = β l := by
    change elementaryEnd β l k t⁻¹ ((x : Module.End F V) (β l)) = _
    rw [elementaryEnd_apply, Module.Basis.coord_apply]
    change (t⁻¹ * t) • β l = _
    rw [inv_mul_cancel₀ ht, one_smul]
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff] at hx
  obtain ⟨z, hz⟩ := hx (-y)
  rw [Ideal.mem_bot] at hz
  have hzero := congrArg (fun w : 𝓛.order => (w : Module.End F V) (β l)) hz
  change (z : Module.End F V) (-((y : Module.End F V) ((x : Module.End F V) (β l)))) +
    (z : Module.End F V) (β l) - β l = 0 at hzero
  rw [hyx, map_neg, neg_add_cancel, zero_sub, neg_eq_zero] at hzero
  exact β.ne_zero l hzero

include hϖ hβ in
/-- The filtration is exhaustive on endomorphisms and bounded above away from zero. -/
theorem endFiltration_nonempty_bddAbove_of_splits (x : Module.End F V) (hx : x ≠ 0) :
    {n : ℤ | x ∈ 𝓛.endFiltration n}.Nonempty ∧
      BddAbove {n : ℤ | x ∈ 𝓛.endFiltration n} := by
  classical
  let degree : κ × κ → ℤ := fun p =>
    𝓛.period * ordOf hϖ (entry β x p.1 p.2) + 𝓛.index hϖ (β p.1) - 𝓛.index hϖ (β p.2)
  obtain ⟨b, hb⟩ := Finite.bddBelow_range degree
  have hmem : x ∈ 𝓛.endFiltration b := by
    rw [← sum_elementaryEnd_entry β x]
    refine sum_mem fun k _ => sum_mem fun l _ => ?_
    by_cases hkl : entry β x k l = 0
    · rw [hkl, elementaryEnd_zero]
      exact zero_mem _
    rw [𝓛.elementaryEnd_mem_iff hϖ hβ k l hkl]
    have h := hb ⟨(k, l), rfl⟩
    dsimp [degree] at h
    omega
  have hex : ∃ k l, entry β x k l ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    rw [← sum_elementaryEnd_entry β x]
    exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => by
      rw [h k l, elementaryEnd_zero]
  obtain ⟨k, l, hkl⟩ := hex
  refine ⟨⟨b, hmem⟩, degree (k, l), ?_⟩
  intro n hn
  have h := 𝓛.le_of_mem_endFiltration hϖ hβ hn k l hkl
  dsimp [degree]
  omega

end LocalField

end LatticeChain

/-- The radical filtration of a lattice-chain order, as stated in BK93 §1.1. -/
theorem radicalFiltration : RadicalFiltrationStatement.{u, v} := by
  intro F _ _ _ _ V _ _ 𝓛
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨r, β, hβ⟩ := 𝓛.exists_basis_splits hϖ
  exact ⟨𝓛.endFiltration_mul_eq_of_splits hϖ hβ,
    𝓛.span_endFiltration_apply_eq_of_splits hϖ hβ,
    𝓛.maximalIdeal_smul_order_eq hϖ,
    fun x => ⟨𝓛.mem_endFiltration_one_of_mem_jacobson hϖ hβ x,
      𝓛.mem_jacobson_of_mem_endFiltration_one x⟩,
    𝓛.endFiltration_nonempty_bddAbove_of_splits hϖ hβ⟩

end Langlands.BushnellKutzko
