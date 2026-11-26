import Langlands.BushnellKutzko.MoyReduction
import Langlands.BushnellKutzko.FundamentalStratumDual

/-! # A coset satisfying the power condition contains a nilpotent element

Let `𝓛` be an `𝔬_F`-lattice chain in a finite-dimensional vector space `V` over a nonarchimedean
local field `F`, let `x ∈ 𝔓^j(𝓛)` and suppose `x^n ∈ 𝔓^{nj+1}(𝓛)` for some `n`. Then the coset
`x + 𝔓^{j+1}(𝓛)` contains a nilpotent element
(`LatticeChain.exists_isNilpotent_add_of_pow_mem_endFiltration`).
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u v

section Coordinates

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
variable {ι : Type*} [Fintype ι]

namespace LatticeChain

include hϖ in
/-- Let `m'' e < m e''`. If `b ∈ 𝔓^{-m}(𝓛) ∩ 𝔓^{-m''}(𝓛'')`, then `b + y` is nilpotent for
some `y ∈ 𝔓^{1-m}(𝓛)`. -/
theorem exists_isNilpotent_add_of_mem_both (𝓛 𝓛'' : LatticeChain 𝒪[F] F (ι → F)) {m m'' : ℤ}
    (hlt : m'' * 𝓛.period < m * 𝓛''.period) {b : Module.End F (ι → F)}
    (hb : b ∈ 𝓛.endFiltration (-m)) (hb'' : b ∈ 𝓛''.endFiltration (-m'')) :
    ∃ y ∈ 𝓛.endFiltration (1 - m), IsNilpotent (b + y) := by
  classical
  obtain ⟨r, β, hβ, hβ''⟩ := 𝓛.exists_basis_splits_both hϖ 𝓛''
  have he : (0 : ℤ) < 𝓛.period := Int.natCast_pos.mpr 𝓛.period_pos
  have he'' : (0 : ℤ) < 𝓛''.period := Int.natCast_pos.mpr 𝓛''.period_pos
  let w : Fin r → ℤ := fun k =>
    (𝓛''.period : ℤ) * 𝓛.index hϖ (β k) - (𝓛.period : ℤ) * 𝓛''.index hϖ (β k)
  let bad : Fin r → Fin r → Prop := fun l k =>
    elementaryEnd β l k (entry β b l k) ∉ 𝓛.endFiltration (1 - m)
  have hbad : ∀ l k, bad l k → w l < w k := by
    intro l k hlk
    have hblk : entry β b l k ≠ 0 := by
      intro h0
      apply hlk
      rw [h0, elementaryEnd_zero]
      exact zero_mem _
    have h1 := 𝓛.le_of_mem_endFiltration hϖ hβ hb l k hblk
    have h2 : ¬ (1 - m + 𝓛.index hϖ (β k) ≤
        (𝓛.period : ℤ) * ordOf hϖ (entry β b l k) + 𝓛.index hϖ (β l)) := by
      rw [← 𝓛.elementaryEnd_mem_iff hϖ hβ l k hblk]
      exact hlk
    have hc' : (𝓛.period : ℤ) * ordOf hϖ (entry β b l k) =
        𝓛.index hϖ (β k) - 𝓛.index hϖ (β l) - m := by omega
    have h3' := 𝓛''.le_of_mem_endFiltration hϖ hβ'' hb'' l k hblk
    have h3 : (𝓛''.period : ℤ) * ordOf hϖ (entry β b l k) ≥
        𝓛''.index hϖ (β k) - 𝓛''.index hϖ (β l) - m'' := by
      omega
    have h4 : (𝓛''.period : ℤ) * ((𝓛.period : ℤ) * ordOf hϖ (entry β b l k)) =
        (𝓛''.period : ℤ) * (𝓛.index hϖ (β k) - 𝓛.index hϖ (β l) - m) := by
      rw [hc']
    have h5 : (𝓛.period : ℤ) * ((𝓛''.period : ℤ) * ordOf hϖ (entry β b l k)) ≥
        (𝓛.period : ℤ) * (𝓛''.index hϖ (β k) - 𝓛''.index hϖ (β l) - m'') :=
      mul_le_mul_of_nonneg_left h3 he.le
    show (𝓛''.period : ℤ) * 𝓛.index hϖ (β l) - (𝓛.period : ℤ) * 𝓛''.index hϖ (β l) <
      (𝓛''.period : ℤ) * 𝓛.index hϖ (β k) - (𝓛.period : ℤ) * 𝓛''.index hϖ (β k)
    nlinarith
  let z : Module.End F (ι → F) :=
    ∑ l, ∑ k, if bad l k then elementaryEnd β l k (entry β b l k) else 0
  let g : Module.End F (ι → F) :=
    ∑ l, ∑ k, if bad l k then 0 else elementaryEnd β l k (entry β b l k)
  have hbzg : b = z + g := by
    conv_lhs => rw [← sum_elementaryEnd_entry β b]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  refine ⟨-g, neg_mem (sum_mem fun l _ => sum_mem fun k _ => ?_), ?_⟩
  · split_ifs with h
    · exact zero_mem _
    · exact not_not.1 h
  · rw [hbzg, add_neg_cancel_right]
    apply isNilpotent_of_lt_weight β w
    intro j
    simp only [z, LinearMap.sum_apply]
    refine sum_mem fun l _ => sum_mem fun k _ => ?_
    split_ifs with hlk
    · rw [elementaryEnd_apply_basis]
      split_ifs with hkj
      · subst hkj
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hbad l k hlk, rfl⟩)
      · exact zero_mem _
    · rw [LinearMap.zero_apply]
      exact zero_mem _

include hϖ in
/-- In coordinates: if `x ∈ 𝔓^j(𝓛)` and `x^n ∈ 𝔓^{nj+1}(𝓛)`, then `x + y` is nilpotent for some
`y ∈ 𝔓^{j+1}(𝓛)`. -/
theorem exists_isNilpotent_add_of_pow_mem (𝓛 : LatticeChain 𝒪[F] F (ι → F)) {j : ℤ}
    {x : Module.End F (ι → F)} (hx : x ∈ 𝓛.endFiltration j) {n : ℕ}
    (hn : x ^ n ∈ 𝓛.endFiltration (n * j + 1)) :
    ∃ y ∈ 𝓛.endFiltration (j + 1), IsNilpotent (x + y) := by
  obtain ⟨𝓜, j', hcos, hlt⟩ := 𝓛.exists_latticeChain_of_pow_mem hx hn (by simp)
  have hx' : x ∈ 𝓜.endFiltration j' := hcos x (by simp)
  obtain ⟨y, hy, hnil⟩ := 𝓛.exists_isNilpotent_add_of_mem_both hϖ 𝓜 (m := -j) (m'' := -j')
    (by linarith) (by simpa using hx) (by simpa using hx')
  exact ⟨y, by simpa [show 1 - -j = j + 1 by ring] using hy, hnil⟩

end LatticeChain

end Coordinates

section Transport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable {W : Type*} [AddCommGroup W] [Module F W]

namespace LatticeChain

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Conjugation by a linear equivalence identifies the filtrations of a chain and of its
transport. -/
theorem conj_mem_endFiltration_linearEquivMap (𝓛 : LatticeChain 𝒪[F] F V) (f : V ≃ₗ[F] W)
    {j : ℤ} {x : Module.End F V} :
    f.conj x ∈ (𝓛.linearEquivMap f).endFiltration j ↔ x ∈ 𝓛.endFiltration j := by
  constructor
  · intro h i v hv
    have h' := h i (f v) ((𝓛.mem_linearEquivMap f i _).mpr (by simpa using hv))
    rw [mem_linearEquivMap] at h'
    simpa using h'
  · intro h i w hw
    rw [mem_linearEquivMap] at hw ⊢
    simpa using h i _ hw

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Transport along a linear equivalence preserves the period. -/
theorem period_linearEquivMap (𝓛 : LatticeChain 𝒪[F] F V) (f : V ≃ₗ[F] W) :
    (𝓛.linearEquivMap f).period = 𝓛.period := by
  symm
  apply (𝓛.linearEquivMap f).period_unique
  intro i
  change (𝓛.lattice (i + 𝓛.period)).map (f.toLinearMap.restrictScalars 𝒪[F]) =
    Ring.jacobson 𝒪[F] • (𝓛.lattice i).map (f.toLinearMap.restrictScalars 𝒪[F])
  rw [𝓛.lattice_add_period, Submodule.map_smul'']

/-- Let `x ∈ 𝔓^j(𝓛)` with `x^n ∈ 𝔓^{nj+1}(𝓛)` for some `n`. Then the coset `x + 𝔓^{j+1}(𝓛)`
contains a nilpotent element. -/
theorem exists_isNilpotent_add_of_pow_mem_endFiltration [FiniteDimensional F V]
    (𝓛 : LatticeChain 𝒪[F] F V) {j : ℤ} {x : Module.End F V} (hx : x ∈ 𝓛.endFiltration j)
    {n : ℕ} (hn : x ^ n ∈ 𝓛.endFiltration (n * j + 1)) :
    ∃ y ∈ 𝓛.endFiltration (j + 1), IsNilpotent (x + y) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let f := (Module.finBasis F V).equivFun
  let C := 𝓛.linearEquivMap f
  have hx' : f.conj x ∈ C.endFiltration j := (𝓛.conj_mem_endFiltration_linearEquivMap f).mpr hx
  have hn' : (f.conj x) ^ n ∈ C.endFiltration (n * j + 1) := by
    have h : (f.conj x) ^ n = f.conj (x ^ n) := by
      change (f.conjAlgEquiv F x) ^ n = f.conjAlgEquiv F (x ^ n)
      exact (map_pow _ x n).symm
    rw [h]
    exact (𝓛.conj_mem_endFiltration_linearEquivMap f).mpr hn
  obtain ⟨y', hy', hnil⟩ := C.exists_isNilpotent_add_of_pow_mem hϖ hx' hn'
  refine ⟨f.symm.conj y', ?_, ?_⟩
  · rw [← 𝓛.conj_mem_endFiltration_linearEquivMap f]
    simpa using hy'
  · have h : x + f.symm.conj y' = f.symm.conj (f.conj x + y') := by
      rw [map_add, LinearEquiv.symm_conj_apply]
      congr 1
      ext v
      simp
    rw [h]
    exact hnil.map (f.symm.conjAlgEquiv F)

end LatticeChain

end Transport

end Langlands.BushnellKutzko
