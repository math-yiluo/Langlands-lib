import Langlands.BushnellKutzko.LatticeChain

/-! # Splitting bases for pairs of lattice chains

For a nonarchimedean local field `F` with uniformizer `ϖ`:

* `ordOf hϖ c`: the integer `t` with `c = ϖ^t u`, `u ∈ 𝔬_F^×`, for `c ≠ 0`.
* For an `𝔬_F`-lattice chain `𝓛` in `V`, `𝓛.index hϖ x` is the largest `i` with `x ∈ L_i`
  (`x ≠ 0`), and `index (c • x) = index x + e(𝓛) ord(c)`.
* `exists_basis_splits_both`: for any two lattice chains `𝓛, 𝓛'` in `F^ι` there is a basis of
  `F^ι` that splits both: every `L_i` and every `L'_i` is the direct sum of its intersections
  with the lines spanned by the basis vectors. This is the lattice-chain form of the
  Goldman–Iwahori theorem that two norms on a finite-dimensional space over a discretely valued
  field have a common orthogonal basis.
* `exists_basis_splits`: every lattice chain in an arbitrary vector space has a finite
  splitting basis, obtained by transport to a coordinate space.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u v

/-! ### The integer valuation attached to a uniformizer -/

section Ord

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem coe_uniformizer_ne_zero : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coe_unit_ne_zero (w : 𝒪[F]ˣ) : ((w : 𝒪[F]) : F) ≠ 0 := by
  intro h
  have h' : (w : 𝒪[F]) = 0 := Subtype.ext h
  exact w.ne_zero h'

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coe_unit_inv (w : 𝒪[F]ˣ) :
    (((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = ((w : 𝒪[F]) : F)⁻¹ := by
  have h : (((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) * ((w : 𝒪[F]) : F) = 1 := by
    rw [← Subring.coe_mul, Units.inv_mul]
    rfl
  exact eq_inv_of_mul_eq_one_left h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem inv_mem_integer_of_not_mem {c : F} (hc : c ∉ 𝒪[F]) : c⁻¹ ∈ 𝒪[F] := by
  rw [Valuation.mem_integer_iff] at hc ⊢
  rw [map_inv₀]
  push Not at hc
  exact inv_le_one_of_one_le₀ hc.le

include hϖ in
/-- A nonzero integral element is `ϖ^n u` with `n ≥ 0` and `u` a unit of `𝔬_F`. -/
theorem exists_eq_pow_mul_unit_of_mem {c : F} (hc : c ≠ 0) (h : c ∈ 𝒪[F]) :
    ∃ (n : ℕ) (w : 𝒪[F]ˣ), c = (ϖ : F) ^ n * ((w : 𝒪[F]) : F) := by
  have hx : (⟨c, h⟩ : 𝒪[F]) ≠ 0 := fun h0 => hc (congrArg Subtype.val h0)
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  refine ⟨n, w, ?_⟩
  have h2 := congrArg Subtype.val hw
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow] at h2
  rw [mul_comm]
  exact h2

include hϖ in
/-- Every nonzero `c ∈ F` is `ϖ^t u` with `t ∈ ℤ` and `u` a unit of `𝔬_F`. -/
theorem exists_eq_zpow_mul_unit {c : F} (hc : c ≠ 0) :
    ∃ (t : ℤ) (w : 𝒪[F]ˣ), c = (ϖ : F) ^ t * ((w : 𝒪[F]) : F) := by
  by_cases h : c ∈ 𝒪[F]
  · obtain ⟨n, w, hw⟩ := exists_eq_pow_mul_unit_of_mem hϖ hc h
    exact ⟨n, w, by rw [zpow_natCast]; exact hw⟩
  · obtain ⟨n, w, hw⟩ :=
      exists_eq_pow_mul_unit_of_mem hϖ (inv_ne_zero hc) (inv_mem_integer_of_not_mem h)
    refine ⟨-(n : ℤ), w⁻¹, ?_⟩
    rw [← inv_inv c, hw, mul_inv, zpow_neg, zpow_natCast, coe_unit_inv]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem pow_eq_coe_unit {n : ℕ} {w : 𝒪[F]ˣ} (h : (ϖ : F) ^ n = ((w : 𝒪[F]) : F)) : n = 0 := by
  by_contra hn
  have h' : ϖ ^ n = (w : 𝒪[F]) := Subtype.ext (by simpa using h)
  have hu : IsUnit (ϖ ^ n) := h' ▸ w.isUnit
  exact hϖ.not_isUnit ((isUnit_pow_iff hn).1 hu)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem zpow_eq_coe_unit {k : ℤ} {w : 𝒪[F]ˣ} (h : (ϖ : F) ^ k = ((w : 𝒪[F]) : F)) : k = 0 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast] at h
    exact_mod_cast pow_eq_coe_unit hϖ h
  · rw [zpow_neg, zpow_natCast] at h
    have h2 : (ϖ : F) ^ n = (((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) := by
      rw [coe_unit_inv, ← h, inv_inv]
    simp [pow_eq_coe_unit hϖ h2]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem zpow_mul_unit_inj {t s : ℤ} {w w' : 𝒪[F]ˣ}
    (h : (ϖ : F) ^ t * ((w : 𝒪[F]) : F) = (ϖ : F) ^ s * ((w' : 𝒪[F]) : F)) : t = s := by
  have hne := coe_uniformizer_ne_zero hϖ
  have hw := coe_unit_ne_zero w
  have h2 : (ϖ : F) ^ (t - s) = (((w' * w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) := by
    rw [Units.val_mul, Subring.coe_mul, coe_unit_inv, zpow_sub₀ hne,
      div_eq_iff (zpow_ne_zero _ hne)]
    field_simp
    linear_combination h
  have := zpow_eq_coe_unit hϖ h2
  omega

/-- The valuation `ord(c)` of `c ∈ F` normalized by the uniformizer `ϖ`: the integer `t` with
`c = ϖ^t u`, `u ∈ 𝔬_F^×` (and `0` for `c = 0`). -/
def ordOf (c : F) : ℤ := by
  classical
  exact if hc : c = 0 then 0 else Classical.choose (exists_eq_zpow_mul_unit hϖ hc)

theorem exists_eq_zpow_ordOf_mul {c : F} (hc : c ≠ 0) :
    ∃ w : 𝒪[F]ˣ, c = (ϖ : F) ^ ordOf hϖ c * ((w : 𝒪[F]) : F) := by
  classical
  simp only [ordOf, hc, ↓reduceDIte]
  exact Classical.choose_spec (exists_eq_zpow_mul_unit hϖ hc)

theorem ordOf_eq {c : F} {t : ℤ} {w : 𝒪[F]ˣ} (h : c = (ϖ : F) ^ t * ((w : 𝒪[F]) : F)) :
    ordOf hϖ c = t := by
  have hc : c ≠ 0 := by
    rw [h]
    exact mul_ne_zero (zpow_ne_zero _ (coe_uniformizer_ne_zero hϖ)) (coe_unit_ne_zero w)
  obtain ⟨w', hw'⟩ := exists_eq_zpow_ordOf_mul hϖ hc
  exact zpow_mul_unit_inj hϖ (hw'.symm.trans h)

theorem ordOf_mul {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) :
    ordOf hϖ (c * d) = ordOf hϖ c + ordOf hϖ d := by
  obtain ⟨w, hw⟩ := exists_eq_zpow_ordOf_mul hϖ hc
  obtain ⟨w', hw'⟩ := exists_eq_zpow_ordOf_mul hϖ hd
  apply ordOf_eq hϖ (w := w * w')
  conv_lhs => rw [hw, hw']
  rw [zpow_add₀ (coe_uniformizer_ne_zero hϖ), Units.val_mul, Subring.coe_mul]
  ring

theorem ordOf_inv {c : F} (hc : c ≠ 0) : ordOf hϖ c⁻¹ = -ordOf hϖ c := by
  obtain ⟨w, hw⟩ := exists_eq_zpow_ordOf_mul hϖ hc
  apply ordOf_eq hϖ (w := w⁻¹)
  conv_lhs => rw [hw]
  rw [mul_inv, coe_unit_inv, zpow_neg]

theorem ordOf_zpow_mul_unit (t : ℤ) (w : 𝒪[F]ˣ) :
    ordOf hϖ ((ϖ : F) ^ t * ((w : 𝒪[F]) : F)) = t :=
  ordOf_eq hϖ rfl

theorem ordOf_zpow (t : ℤ) : ordOf hϖ ((ϖ : F) ^ t) = t :=
  ordOf_eq hϖ (w := 1) (by simp)

theorem ordOf_nonneg {c : F} (hc : c ≠ 0) (h : c ∈ 𝒪[F]) : 0 ≤ ordOf hϖ c := by
  obtain ⟨n, w, hw⟩ := exists_eq_pow_mul_unit_of_mem hϖ hc h
  rw [ordOf_eq hϖ (t := n) (w := w) (by rw [zpow_natCast]; exact hw)]
  positivity

theorem mem_integer_of_ordOf_nonneg {c : F} (hc : c ≠ 0) (h : 0 ≤ ordOf hϖ c) : c ∈ 𝒪[F] := by
  obtain ⟨w, hw⟩ := exists_eq_zpow_ordOf_mul hϖ hc
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hw, hn, zpow_natCast]
  exact mul_mem (pow_mem ϖ.2 n) (w : 𝒪[F]).2

theorem mem_integer_iff_ordOf_nonneg {c : F} (hc : c ≠ 0) : c ∈ 𝒪[F] ↔ 0 ≤ ordOf hϖ c :=
  ⟨ordOf_nonneg hϖ hc, mem_integer_of_ordOf_nonneg hϖ hc⟩

end Ord

/-! ### The index of a vector with respect to a lattice chain -/

section Index

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
variable {V : Type v} [AddCommGroup V] [Module F V]

namespace LatticeChain

variable (𝓛 : LatticeChain 𝒪[F] F V)

include hϖ in
/-- `ϖ x ∈ L_j` if and only if `x ∈ L_{j - e}`. -/
theorem uniformizer_smul_mem_iff {j : ℤ} {x : V} :
    (ϖ : F) • x ∈ 𝓛.lattice j ↔ x ∈ 𝓛.lattice (j - 𝓛.period) := by
  have hL : 𝓛.lattice j = ϖ • 𝓛.lattice (j - 𝓛.period) := by
    rw [← Submodule.ideal_span_singleton_smul, ← hϖ.maximalIdeal_eq,
      ← jacobson_integer_eq_maximalIdeal, ← 𝓛.lattice_add_period, sub_add_cancel]
  rw [hL, show (ϖ : F) • x = ϖ • x from algebraMap_smul F ϖ x]
  constructor
  · intro h
    rw [Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨y, hy, hxy⟩ := h
    have hinj : Function.Injective (fun z : V => (ϖ : F) • z) :=
      smul_right_injective _ (coe_uniformizer_ne_zero hϖ)
    have : x = y := hinj (by
      simp only
      rw [show (ϖ : F) • x = ϖ • x from algebraMap_smul F ϖ x,
        show (ϖ : F) • y = ϖ • y from algebraMap_smul F ϖ y, hxy])
    rw [this]
    exact hy
  · intro h
    exact Submodule.smul_mem_pointwise_smul _ _ _ h

include hϖ in
/-- `ϖ^t x ∈ L_j` if and only if `x ∈ L_{j - e t}`. -/
theorem zpow_smul_mem_iff (t : ℤ) {j : ℤ} {x : V} :
    ((ϖ : F) ^ t) • x ∈ 𝓛.lattice j ↔ x ∈ 𝓛.lattice (j - 𝓛.period * t) := by
  induction t using Int.induction_on generalizing j with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one₀ (coe_uniformizer_ne_zero hϖ), mul_comm, mul_smul,
      𝓛.uniformizer_smul_mem_iff hϖ, ih]
    congr! 2
    ring
  | pred k ih =>
    have h1 : ((ϖ : F) ^ (-(k : ℤ) - 1)) • x =
        ((ϖ : F))⁻¹ • (((ϖ : F) ^ (-(k : ℤ))) • x) := by
      rw [smul_smul, zpow_sub_one₀ (coe_uniformizer_ne_zero hϖ), mul_comm]
    have h2 : ∀ y : V, ((ϖ : F))⁻¹ • y ∈ 𝓛.lattice j ↔ y ∈ 𝓛.lattice (j + 𝓛.period) := by
      intro y
      have h3 := 𝓛.uniformizer_smul_mem_iff hϖ (j := j + 𝓛.period) (x := ((ϖ : F))⁻¹ • y)
      rw [smul_smul, mul_inv_cancel₀ (coe_uniformizer_ne_zero hϖ), one_smul,
        add_sub_cancel_right] at h3
      exact h3.symm
    rw [h1, h2, ih]
    congr! 2
    ring

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Units of `𝔬_F` preserve every `L_j`. -/
theorem unit_smul_mem_iff (w : 𝒪[F]ˣ) {j : ℤ} {x : V} :
    ((w : 𝒪[F]) : F) • x ∈ 𝓛.lattice j ↔ x ∈ 𝓛.lattice j := by
  rw [show ((w : 𝒪[F]) : F) • x = (w : 𝒪[F]) • x from algebraMap_smul F (w : 𝒪[F]) x]
  constructor
  · intro h
    have h2 := Submodule.smul_mem _ ((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) h
    rwa [smul_smul, Units.inv_mul, one_smul] at h2
  · intro h
    exact Submodule.smul_mem _ _ h

/-- For `c ≠ 0`, `c x ∈ L_j` if and only if `x ∈ L_{j - e ord(c)}`. -/
theorem smul_mem_iff {c : F} (hc : c ≠ 0) {j : ℤ} {x : V} :
    c • x ∈ 𝓛.lattice j ↔ x ∈ 𝓛.lattice (j - 𝓛.period * ordOf hϖ c) := by
  obtain ⟨w, hw⟩ := exists_eq_zpow_ordOf_mul hϖ hc
  conv_lhs => rw [hw, mul_smul]
  rw [𝓛.zpow_smul_mem_iff hϖ, 𝓛.unit_smul_mem_iff]

include hϖ in
/-- Every vector lies in some `L_i`. -/
theorem exists_mem (x : V) : ∃ i, x ∈ 𝓛.lattice i := by
  let S : Submodule F V :=
    { carrier := {x | ∃ i, x ∈ 𝓛.lattice i}
      add_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        exact ⟨min i j, add_mem (𝓛.antitone (min_le_left i j) hi)
          (𝓛.antitone (min_le_right i j) hj)⟩
      zero_mem' := ⟨0, zero_mem _⟩
      smul_mem' := by
        rintro c a ⟨i, hi⟩
        by_cases hc : c = 0
        · exact ⟨0, by rw [hc, zero_smul]; exact zero_mem _⟩
        · refine ⟨i + 𝓛.period * ordOf hϖ c, ?_⟩
          rw [𝓛.smul_mem_iff hϖ hc, add_sub_cancel_right]
          exact hi }
  have hle : Submodule.span F (𝓛.lattice 0 : Set V) ≤ S := by
    rw [Submodule.span_le]
    intro y hy
    exact ⟨0, hy⟩
  rw [(𝓛.isLattice 0).span_eq_top] at hle
  exact hle (Submodule.mem_top (x := x))

instance isLattice_zero' : (𝓛.lattice 0).IsLattice F := 𝓛.isLattice 0

instance finite_zero' : Module.Finite 𝒪[F] (𝓛.lattice 0) :=
  Submodule.IsLattice.finite F (𝓛.lattice 0)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Coordinates, in the `F`-basis given by an `𝔬_F`-basis of `L_0`, of a vector of
`L_0` are integral. -/
theorem repr_extendOfIsLattice_mem {κ : Type*}
    (b : Module.Basis κ 𝒪[F] (𝓛.lattice 0)) {w : V} (hw : w ∈ 𝓛.lattice 0) (a : κ) :
    (b.extendOfIsLattice F).repr w a ∈ 𝒪[F] := by
  classical
  have : Finite κ := Module.Finite.finite_basis b
  let := Fintype.ofFinite κ
  have hsum : w = ∑ c, (algebraMap 𝒪[F] F (b.repr ⟨w, hw⟩ c)) • b.extendOfIsLattice F c := by
    have h := congrArg (Subtype.val) (b.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at h
    change _ = w at h
    refine h.symm.trans (Finset.sum_congr rfl fun c _ => ?_)
    rw [Submodule.coe_smul_of_tower, Module.Basis.extendOfIsLattice_apply, algebraMap_smul]
  rw [hsum, Module.Basis.repr_sum_self]
  exact (b.repr ⟨w, hw⟩ a).2

include hϖ in
/-- A vector lying in every `L_i` is zero. -/
theorem eq_zero_of_forall_mem {x : V} (hx : ∀ i, x ∈ 𝓛.lattice i) : x = 0 := by
  classical
  let b := Module.finBasis 𝒪[F] (𝓛.lattice 0)
  let bF := b.extendOfIsLattice F
  rw [← bF.forall_coord_eq_zero_iff]
  intro a
  by_contra hne
  set c := bF.coord a x with hc
  have hmem : ∀ t : ℕ, (ϖ : F) ^ (-(t : ℤ)) * c ∈ 𝒪[F] := by
    intro t
    have h1 : ((ϖ : F) ^ (-(t : ℤ))) • x ∈ 𝓛.lattice 0 := by
      rw [𝓛.zpow_smul_mem_iff hϖ]
      exact hx _
    have h2 := 𝓛.repr_extendOfIsLattice_mem b h1 a
    rwa [map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
  have hne' : ∀ t : ℕ, (ϖ : F) ^ (-(t : ℤ)) * c ≠ 0 := fun t =>
    mul_ne_zero (zpow_ne_zero _ (coe_uniformizer_ne_zero hϖ)) hne
  have h := ordOf_nonneg hϖ (hne' ((ordOf hϖ c).toNat + 1))
    (hmem ((ordOf hϖ c).toNat + 1))
  rw [ordOf_mul hϖ (zpow_ne_zero _ (coe_uniformizer_ne_zero hϖ)) hne, ordOf_zpow] at h
  push_cast at h
  have := Int.self_le_toNat (ordOf hϖ c)
  omega

include hϖ in
theorem exists_index {x : V} (hx : x ≠ 0) : ∃ i : ℤ, ∀ j, x ∈ 𝓛.lattice j ↔ j ≤ i := by
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, x ∈ 𝓛.lattice z → z ≤ b := by
    by_contra h
    push Not at h
    apply hx
    apply 𝓛.eq_zero_of_forall_mem hϖ
    intro i
    obtain ⟨z, hz, hiz⟩ := h i
    exact 𝓛.antitone hiz.le hz
  obtain ⟨i, hi, hmax⟩ := Int.exists_greatest_of_bdd hbdd (𝓛.exists_mem hϖ x)
  exact ⟨i, fun j => ⟨hmax j, fun hj => 𝓛.antitone hj hi⟩⟩

/-- The index `ν_𝓛(x)` of a nonzero vector: the largest `i` with `x ∈ L_i` (`0` for `x = 0`). -/
def index (x : V) : ℤ := by
  classical
  exact if hx : x = 0 then 0 else Classical.choose (𝓛.exists_index hϖ hx)

theorem mem_iff_le_index {x : V} (hx : x ≠ 0) (j : ℤ) :
    x ∈ 𝓛.lattice j ↔ j ≤ 𝓛.index hϖ x := by
  classical
  simp only [index, hx, ↓reduceDIte]
  exact Classical.choose_spec (𝓛.exists_index hϖ hx) j

theorem mem_lattice_index {x : V} (hx : x ≠ 0) : x ∈ 𝓛.lattice (𝓛.index hϖ x) :=
  (𝓛.mem_iff_le_index hϖ hx _).2 le_rfl

theorem not_mem_lattice_index_add_one {x : V} (hx : x ≠ 0) :
    x ∉ 𝓛.lattice (𝓛.index hϖ x + 1) := by
  rw [𝓛.mem_iff_le_index hϖ hx]
  omega

theorem index_eq_of_forall {x : V} (hx : x ≠ 0) {i : ℤ}
    (h : ∀ j, x ∈ 𝓛.lattice j ↔ j ≤ i) : 𝓛.index hϖ x = i := by
  have h1 := (h (𝓛.index hϖ x)).1 (𝓛.mem_lattice_index hϖ hx)
  have h2 := (𝓛.mem_iff_le_index hϖ hx i).1 ((h i).2 le_rfl)
  omega

/-- `ν(c x) = ν(x) + e ord(c)`. -/
theorem index_smul {c : F} (hc : c ≠ 0) {x : V} (hx : x ≠ 0) :
    𝓛.index hϖ (c • x) = 𝓛.index hϖ x + 𝓛.period * ordOf hϖ c := by
  apply 𝓛.index_eq_of_forall hϖ (smul_ne_zero hc hx)
  intro j
  rw [𝓛.smul_mem_iff hϖ hc, 𝓛.mem_iff_le_index hϖ hx]
  omega

/-! ### Comparison of two lattice chains -/

include hϖ in
theorem exists_forall_finset_mem (S : Finset V) : ∃ i, ∀ s ∈ S, s ∈ 𝓛.lattice i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := 𝓛.exists_mem hϖ a
    refine ⟨min i j, fun s hs => ?_⟩
    rw [Finset.mem_insert] at hs
    rcases hs with rfl | hs
    · exact 𝓛.antitone (min_le_right i j) hj
    · exact 𝓛.antitone (min_le_left i j) (hi s hs)

include hϖ in
/-- `L_0 ⊆ L'_i` for some `i`. -/
theorem exists_lattice_zero_le (𝓛' : LatticeChain 𝒪[F] F V) :
    ∃ i, 𝓛.lattice 0 ≤ 𝓛'.lattice i := by
  obtain ⟨S, hS⟩ := (𝓛.isLattice 0).fg
  obtain ⟨i, hi⟩ := 𝓛'.exists_forall_finset_mem hϖ S
  refine ⟨i, ?_⟩
  rw [← hS, Submodule.span_le]
  exact fun s hs => hi s hs

include hϖ in
/-- `L_B ⊆ L'_0` for some `B`. -/
theorem exists_le_lattice_zero (𝓛' : LatticeChain 𝒪[F] F V) :
    ∃ B, 𝓛.lattice B ≤ 𝓛'.lattice 0 := by
  obtain ⟨i, hi⟩ := 𝓛.exists_lattice_zero_le hϖ 𝓛'
  set t : ℕ := (-i).toNat with ht
  have hti : -i ≤ t := Int.self_le_toNat (-i)
  refine ⟨𝓛.period * t, fun x hx => ?_⟩
  have h1 : ((ϖ : F) ^ (-(t : ℤ))) • x ∈ 𝓛.lattice 0 := by
    rw [𝓛.zpow_smul_mem_iff hϖ]
    simpa using hx
  have h2 := hi h1
  have h3 : x = ((ϖ : F) ^ (t : ℤ)) • (((ϖ : F) ^ (-(t : ℤ))) • x) := by
    rw [smul_smul, ← zpow_add₀ (coe_uniformizer_ne_zero hϖ)]
    simp
  rw [h3]
  have hpos : (1 : ℤ) ≤ 𝓛'.period := by exact_mod_cast 𝓛'.period_pos
  refine 𝓛'.antitone (show (0 : ℤ) ≤ i + 𝓛'.period * t by nlinarith) ?_
  rw [𝓛'.zpow_smul_mem_iff hϖ, add_sub_cancel_right]
  exact h2

include hϖ in
/-- The function `e' ν_𝓛 - e ν_𝓛'` is bounded above on nonzero vectors. -/
theorem exists_bound (𝓛' : LatticeChain 𝒪[F] F V) :
    ∃ C : ℤ, ∀ x : V, x ≠ 0 →
      (𝓛'.period : ℤ) * 𝓛.index hϖ x - 𝓛.period * 𝓛'.index hϖ x ≤ C := by
  obtain ⟨B, hB⟩ := 𝓛.exists_le_lattice_zero hϖ 𝓛'
  set e := (𝓛.period : ℤ)
  set e' := (𝓛'.period : ℤ)
  have he : 0 < e := Int.natCast_pos.mpr 𝓛.period_pos
  have he' : 0 < e' := Int.natCast_pos.mpr 𝓛'.period_pos
  refine ⟨e' * B + e' * e, fun x hx => ?_⟩
  set j := 𝓛'.index hϖ x
  set q := j / e'
  have hq1 : e' * q ≤ j := Int.mul_ediv_self_le he'.ne'
  have hq2 : j < e' * q + e' := Int.lt_mul_ediv_self_add he'
  -- `L_{B + e(q+1)} ⊆ L'_{e'(q+1)}`.
  have hsub : 𝓛.lattice (B + e * (q + 1)) ≤ 𝓛'.lattice (e' * (q + 1)) := by
    intro y hy
    have h1 : ((ϖ : F) ^ (-(q + 1))) • y ∈ 𝓛.lattice B := by
      rw [𝓛.zpow_smul_mem_iff hϖ]
      convert hy using 2
      ring
    have h2 := hB h1
    have h3 : y = ((ϖ : F) ^ (q + 1)) • (((ϖ : F) ^ (-(q + 1))) • y) := by
      rw [smul_smul, ← zpow_add₀ (coe_uniformizer_ne_zero hϖ)]
      simp
    rw [h3, 𝓛'.zpow_smul_mem_iff hϖ]
    convert h2 using 2
    ring
  have hnot : x ∉ 𝓛.lattice (B + e * (q + 1)) := by
    intro hx'
    have h1 := hsub hx'
    rw [𝓛'.mem_iff_le_index hϖ hx] at h1
    linarith
  rw [𝓛.mem_iff_le_index hϖ hx, not_le] at hnot
  have h1 : e' * 𝓛.index hϖ x < e' * (B + e * (q + 1)) := mul_lt_mul_of_pos_left hnot he'
  have h2 : e * (e' * q) ≤ e * j := mul_le_mul_of_nonneg_left hq1 he.le
  nlinarith

end LatticeChain

end Index

/-! ### Splitting families and the common splitting basis -/

section Splitting

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
variable {V : Type v} [AddCommGroup V] [Module F V]

namespace LatticeChain

variable (𝓛 : LatticeChain 𝒪[F] F V)

/-- A finite family `w` *splits* the lattice chain `𝓛` if, whenever `∑ c_k w_k ∈ L_i`, every
term `c_k w_k` lies in `L_i`. For a basis this says that every `L_i` is the direct sum of its
intersections with the lines `F w_k`. -/
def Splits {κ : Type*} [Fintype κ] (w : κ → V) : Prop :=
  ∀ (c : κ → F) (i : ℤ), ∑ k, c k • w k ∈ 𝓛.lattice i → ∀ k, c k • w k ∈ 𝓛.lattice i

/-- The step of the Goldman–Iwahori induction for the chain `𝓛'` split by the basis `u`:
let `k₀` be a coordinate of `v₁` at which `ν'(c_k u_k)` is minimal. If `y` has zero
`k₀`-coordinate and `a v₁ + y ∈ L'_i`, then `a v₁ ∈ L'_i`. -/
theorem smul_mem_of_add_mem_of_splits (𝓛' : LatticeChain 𝒪[F] F V) {κ : Type*}
    [Fintype κ] (u : Module.Basis κ F V) (hu : 𝓛'.Splits u) {v₁ y : V} {k₀ : κ}
    (hk₀ : u.repr v₁ k₀ ≠ 0)
    (hmin : ∀ k, u.repr v₁ k ≠ 0 →
      𝓛'.index hϖ (u.repr v₁ k₀ • u k₀) ≤ 𝓛'.index hϖ (u.repr v₁ k • u k))
    (hy : u.repr y k₀ = 0) {a : F} {i : ℤ} (h : a • v₁ + y ∈ 𝓛'.lattice i) :
    a • v₁ ∈ 𝓛'.lattice i := by
  by_cases ha : a = 0
  · rw [ha, zero_smul]
    exact zero_mem _
  have h1 := hu (fun k => u.repr (a • v₁ + y) k) i (by rw [u.sum_repr]; exact h) k₀
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, hy, add_zero,
    smul_eq_mul, mul_smul] at h1
  have hu0 : ∀ k, u.repr v₁ k ≠ 0 → u.repr v₁ k • u k ≠ 0 := fun k hk =>
    smul_ne_zero hk (u.ne_zero k)
  rw [𝓛'.mem_iff_le_index hϖ (smul_ne_zero ha (hu0 k₀ hk₀)),
    𝓛'.index_smul hϖ ha (hu0 k₀ hk₀)] at h1
  rw [← u.sum_repr v₁, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  by_cases hk : u.repr v₁ k = 0
  · rw [hk, zero_smul, smul_zero]
    exact zero_mem _
  rw [𝓛'.mem_iff_le_index hϖ (smul_ne_zero ha (hu0 k hk)), 𝓛'.index_smul hϖ ha (hu0 k hk)]
  have := hmin k hk
  omega

/-- The step of the Goldman–Iwahori induction for the chain `𝓛`: if moreover `v₁` maximizes
`e(𝓛') ν_𝓛 - e(𝓛) ν_𝓛'` on the nonzero vectors of a subspace `W` containing `v₁` and `y`, then
`a v₁ + y ∈ L_i` implies `a v₁ ∈ L_i`. -/
theorem smul_mem_of_add_mem_of_maximal (𝓛' : LatticeChain 𝒪[F] F V) {κ : Type*}
    [Fintype κ] (u : Module.Basis κ F V) (hu : 𝓛'.Splits u) {v₁ y : V} {k₀ : κ}
    (hk₀ : u.repr v₁ k₀ ≠ 0)
    (hmin : ∀ k, u.repr v₁ k ≠ 0 →
      𝓛'.index hϖ (u.repr v₁ k₀ • u k₀) ≤ 𝓛'.index hϖ (u.repr v₁ k • u k))
    (hy : u.repr y k₀ = 0) {W : Submodule F V} (hv₁W : v₁ ∈ W) (hyW : y ∈ W)
    (hv₁0 : v₁ ≠ 0)
    (hmax : ∀ x ∈ W, x ≠ 0 →
      (𝓛'.period : ℤ) * 𝓛.index hϖ x - 𝓛.period * 𝓛'.index hϖ x ≤
        (𝓛'.period : ℤ) * 𝓛.index hϖ v₁ - 𝓛.period * 𝓛'.index hϖ v₁)
    {a : F} {i : ℤ} (h : a • v₁ + y ∈ 𝓛.lattice i) : a • v₁ ∈ 𝓛.lattice i := by
  by_cases ha : a = 0
  · rw [ha, zero_smul]
    exact zero_mem _
  by_contra hnot
  have hx0 : a • v₁ + y ≠ 0 := by
    intro h0
    have h2 := congrArg (fun z => u.repr z k₀) h0
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, hy, add_zero,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h2
    exact mul_ne_zero ha hk₀ h2
  have hxW : a • v₁ + y ∈ W := add_mem (W.smul_mem a hv₁W) hyW
  have hav0 : a • v₁ ≠ 0 := smul_ne_zero ha hv₁0
  have h1 : i ≤ 𝓛.index hϖ (a • v₁ + y) := (𝓛.mem_iff_le_index hϖ hx0 i).1 h
  have h2 : 𝓛.index hϖ (a • v₁) < i := by
    rw [𝓛.mem_iff_le_index hϖ hav0] at hnot
    omega
  have h3 : 𝓛'.index hϖ (a • v₁ + y) ≤ 𝓛'.index hϖ (a • v₁) := by
    rw [← 𝓛'.mem_iff_le_index hϖ hav0]
    exact smul_mem_of_add_mem_of_splits hϖ 𝓛' u hu hk₀ hmin hy (𝓛'.mem_lattice_index hϖ hx0)
  rw [𝓛.index_smul hϖ ha hv₁0] at h2
  rw [𝓛'.index_smul hϖ ha hv₁0] at h3
  have h4 := hmax _ hxW hx0
  have he : 0 < (𝓛.period : ℤ) := Int.natCast_pos.mpr 𝓛.period_pos
  have he' : 0 < (𝓛'.period : ℤ) := Int.natCast_pos.mpr 𝓛'.period_pos
  have h5 : (𝓛'.period : ℤ) * (𝓛.index hϖ v₁ + 𝓛.period * ordOf hϖ a) <
      𝓛'.period * 𝓛.index hϖ (a • v₁ + y) := mul_lt_mul_of_pos_left (by omega) he'
  have h6 : (𝓛.period : ℤ) * 𝓛'.index hϖ (a • v₁ + y) ≤
      𝓛.period * (𝓛'.index hϖ v₁ + 𝓛'.period * ordOf hϖ a) :=
    mul_le_mul_of_nonneg_left h3 he.le
  nlinarith

include hϖ in
/-- **Goldman–Iwahori induction.** Let `u` be a basis of `V` splitting `𝓛'`. For every finite
set `s` of indices there is a linearly independent family `w` with the same span as `u '' s`
that splits both `𝓛` and `𝓛'`. -/
theorem exists_splits_span (𝓛' : LatticeChain 𝒪[F] F V) {κ : Type*} [Fintype κ]
    (u : Module.Basis κ F V) (hu : 𝓛'.Splits u) (s : Finset κ) :
    ∃ (r : ℕ) (w : Fin r → V), LinearIndependent F w ∧
      Submodule.span F (Set.range w) = Submodule.span F (u '' (s : Set κ)) ∧
      𝓛.Splits w ∧ 𝓛'.Splits w := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | ⟨k1, hk1⟩
  · refine ⟨0, Fin.elim0, linearIndependent_empty_type, ?_, ?_, ?_⟩
    · simp
    · intro c i _ k
      exact k.elim0
    · intro c i _ k
      exact k.elim0
  set W := Submodule.span F (u '' (s : Set κ)) with hW
  let f : V → ℤ := fun x => (𝓛'.period : ℤ) * 𝓛.index hϖ x - 𝓛.period * 𝓛'.index hϖ x
  obtain ⟨C, hC⟩ := 𝓛.exists_bound hϖ 𝓛'
  have hu1W : u k1 ∈ W := Submodule.subset_span ⟨k1, hk1, rfl⟩
  obtain ⟨M, ⟨v₁, hv₁W, hv₁0, hv₁M⟩, hMmax⟩ :=
    Int.exists_greatest_of_bdd (P := fun M => ∃ x ∈ W, x ≠ 0 ∧ f x = M)
      ⟨C, fun z ⟨x, _, hx0, hxz⟩ => hxz ▸ hC x hx0⟩ ⟨_, u k1, hu1W, u.ne_zero k1, rfl⟩
  have hmax : ∀ x ∈ W, x ≠ 0 → f x ≤ f v₁ := fun x hx hx0 =>
    hv₁M ▸ hMmax _ ⟨x, hx, hx0, rfl⟩
  set c := u.repr v₁ with hc
  have hcs : ∀ k, c k ≠ 0 → k ∈ s := by
    intro k hk
    have := (u.mem_span_image.1 hv₁W) (Finsupp.mem_support_iff.2 hk)
    exact this
  -- the coordinate `k₀` minimizing `ν'(c_k u_k)`
  set T := s.filter (fun k => c k ≠ 0) with hT
  have hTne : T.Nonempty := by
    by_contra hT0
    rw [Finset.not_nonempty_iff_eq_empty] at hT0
    apply hv₁0
    rw [← u.sum_repr v₁]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : c k = 0
    · rw [← hc, hk, zero_smul]
    · have : k ∈ T := Finset.mem_filter.2 ⟨hcs k hk, hk⟩
      rw [hT0] at this
      exact absurd this (Finset.notMem_empty k)
  obtain ⟨k₀, hk₀T, hk₀min⟩ :=
    T.exists_min_image (fun k => 𝓛'.index hϖ (c k • u k)) hTne
  have hk₀s : k₀ ∈ s := (Finset.mem_filter.1 hk₀T).1
  have hk₀ : c k₀ ≠ 0 := (Finset.mem_filter.1 hk₀T).2
  have hmin : ∀ k, c k ≠ 0 → 𝓛'.index hϖ (c k₀ • u k₀) ≤ 𝓛'.index hϖ (c k • u k) :=
    fun k hk => hk₀min k (Finset.mem_filter.2 ⟨hcs k hk, hk⟩)
  -- the induction hypothesis on `s \ {k₀}`
  obtain ⟨r, w', hw'li, hw'span, hw'L, hw'L'⟩ := ih (s.erase k₀) (Finset.erase_ssubset hk₀s)
  have hrepr0 : ∀ y ∈ Submodule.span F (Set.range w'), u.repr y k₀ = 0 := by
    intro y hy
    rw [hw'span, u.mem_span_image] at hy
    by_contra hne
    have := hy (Finsupp.mem_support_iff.2 hne)
    simp at this
  have hspan_le : Submodule.span F (Set.range w') ≤ W := by
    rw [hw'span]
    exact Submodule.span_mono (Set.image_mono (by simp))
  refine ⟨r + 1, Fin.cons v₁ w', ?_, ?_, ?_, ?_⟩
  · rw [linearIndependent_finCons]
    refine ⟨hw'li, fun hv => hk₀ (hrepr0 v₁ hv)⟩
  · rw [Fin.range_cons, Submodule.span_insert]
    apply le_antisymm
    · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hv₁W) hspan_le
    · rw [hW, Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      by_cases hkk : k = k₀
      · subst hkk
        -- `c k₀ • u k₀ = v₁ - z` with `z` in the span of the `u_k`, `k ≠ k₀`
        have hz : v₁ - c k • u k ∈ Submodule.span F (Set.range w') := by
          rw [hw'span, u.mem_span_image]
          intro j hj
          rw [Finset.mem_coe, Finset.mem_erase]
          rw [Finset.mem_coe, Finsupp.mem_support_iff, map_sub, map_smul, u.repr_self,
            Finsupp.sub_apply,
            Finsupp.smul_apply, Finsupp.single_apply] at hj
          by_cases hjk : k = j
          · subst hjk
            simp [← hc] at hj
          · simp only [hjk, ↓reduceIte, smul_zero, sub_zero] at hj
            exact ⟨Ne.symm hjk, hcs j hj⟩
        have h1 : c k • u k ∈ Submodule.span F {v₁} ⊔ Submodule.span F (Set.range w') := by
          have : c k • u k = v₁ - (v₁ - c k • u k) := by abel
          rw [this]
          exact sub_mem (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
            (Submodule.mem_sup_right hz)
        have h2 := Submodule.smul_mem _ (c k)⁻¹ h1
        rwa [smul_smul, inv_mul_cancel₀ hk₀, one_smul] at h2
      · apply Submodule.mem_sup_right
        rw [hw'span]
        exact Submodule.subset_span ⟨k, Finset.mem_erase.2 ⟨hkk, hk⟩, rfl⟩
  · intro d i hd
    rw [Fin.sum_univ_succ] at hd
    simp only [Fin.cons_zero, Fin.cons_succ] at hd
    have hyspan : ∑ j : Fin r, d j.succ • w' j ∈ Submodule.span F (Set.range w') :=
      sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have h0 : d 0 • v₁ ∈ 𝓛.lattice i :=
      𝓛.smul_mem_of_add_mem_of_maximal hϖ 𝓛' u hu hk₀ hmin (hrepr0 _ hyspan) hv₁W
        (hspan_le hyspan) hv₁0 hmax hd
    have hrest : ∑ j : Fin r, d j.succ • w' j ∈ 𝓛.lattice i := by
      have := sub_mem hd h0
      rwa [add_sub_cancel_left] at this
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using h0
    · simpa using hw'L (fun j => d j.succ) i hrest j
  · intro d i hd
    rw [Fin.sum_univ_succ] at hd
    simp only [Fin.cons_zero, Fin.cons_succ] at hd
    have hyspan : ∑ j : Fin r, d j.succ • w' j ∈ Submodule.span F (Set.range w') :=
      sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have h0 : d 0 • v₁ ∈ 𝓛'.lattice i :=
      smul_mem_of_add_mem_of_splits hϖ 𝓛' u hu hk₀ hmin (hrepr0 _ hyspan) hd
    have hrest : ∑ j : Fin r, d j.succ • w' j ∈ 𝓛'.lattice i := by
      have := sub_mem hd h0
      rwa [add_sub_cancel_left] at this
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using h0
    · simpa using hw'L' (fun j => d j.succ) i hrest j

include hϖ in
/-- A basis of `V` splitting `𝓛'` yields a basis splitting both `𝓛` and `𝓛'`. -/
theorem exists_basis_splits_of_splits (𝓛' : LatticeChain 𝒪[F] F V) {κ : Type*}
    [Fintype κ] (u : Module.Basis κ F V) (hu : 𝓛'.Splits u) :
    ∃ (r : ℕ) (β : Module.Basis (Fin r) F V), 𝓛.Splits β ∧ 𝓛'.Splits β := by
  obtain ⟨r, w, hli, hspan, hL, hL'⟩ := 𝓛.exists_splits_span hϖ 𝓛' u hu Finset.univ
  have htop : ⊤ ≤ Submodule.span F (Set.range w) := by
    rw [hspan, Finset.coe_univ, Set.image_univ, u.span_eq]
  refine ⟨r, Module.Basis.mk hli htop, ?_, ?_⟩
  · rw [Module.Basis.coe_mk]
    exact hL
  · rw [Module.Basis.coe_mk]
    exact hL'

end LatticeChain

end Splitting

/-! ### The standard lattice chain and a basis splitting two chains -/

section Standard

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)

namespace LatticeChain

variable (F) in
/-- The standard lattice `𝔬_F^ι` in `F^ι`. -/
def standardLattice (ι : Type*) : Submodule 𝒪[F] (ι → F) :=
  LinearMap.range ((Algebra.linearMap 𝒪[F] F).compLeft ι)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_standardLattice {ι : Type*} {v : ι → F} :
    v ∈ standardLattice F ι ↔ ∀ k, v k ∈ 𝒪[F] := by
  constructor
  · rintro ⟨c, rfl⟩ k
    exact (c k).2
  · intro h
    exact ⟨fun k => ⟨v k, h k⟩, rfl⟩

instance isLattice_standardLattice (ι : Type*) [Fintype ι] :
    (standardLattice F ι).IsLattice F where
  fg := by
    rw [standardLattice, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  span_eq_top := by
    classical
    rw [eq_top_iff, ← (Pi.basisFun F ι).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    apply Submodule.subset_span
    rw [SetLike.mem_coe, mem_standardLattice]
    intro j
    rw [Pi.basisFun_apply, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A vector lies in `u • 𝔬_F^ι` exactly when `u⁻¹` times each coordinate is integral. -/
theorem mem_smul_standardLattice {ι : Type*} (u : Fˣ) {v : ι → F} :
    v ∈ u • standardLattice F ι ↔ ∀ k, ((u⁻¹ : Fˣ) : F) * v k ∈ 𝒪[F] := by
  rw [Units.smul_def, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, hb, rfl⟩ k
    rw [mem_standardLattice] at hb
    simpa [Units.smul_def] using hb k
  · intro h
    refine ⟨fun k => ((u⁻¹ : Fˣ) : F) * v k, mem_standardLattice.2 h, ?_⟩
    ext k
    simp

/-- The uniformizer `ϖ` as a unit of `F`. -/
def uniformizerAsUnit : Fˣ :=
  Units.mk0 (ϖ : F) (coe_uniformizer_ne_zero hϖ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp]
theorem coe_uniformizerAsUnit : ((uniformizerAsUnit hϖ : Fˣ) : F) = ϖ := rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem inv_coe_uniformizer_not_mem : ((ϖ : F))⁻¹ ∉ 𝒪[F] := by
  intro h
  apply hϖ.not_isUnit
  refine IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext ?_)
  simp [coe_uniformizer_ne_zero hϖ]

/-- The standard lattice chain `L_i = ϖ^i 𝔬_F^ι` in `F^ι` (period one). -/
def standard (ι : Type*) [Fintype ι] [Nonempty ι] : LatticeChain 𝒪[F] F (ι → F) where
  lattice i := (uniformizerAsUnit hϖ ^ i) • standardLattice F ι
  isLattice i := inferInstance
  lattice_succ_lt i := by
    classical
    obtain ⟨k0⟩ := ‹Nonempty ι›
    set ϖu := uniformizerAsUnit hϖ
    have hϖO : (ϖ : F) ∈ 𝒪[F] := ϖ.2
    refine lt_of_le_of_ne ?_ ?_
    · intro v hv
      rw [mem_smul_standardLattice] at hv ⊢
      intro k
      have h : ((ϖu ^ i)⁻¹ : Fˣ) = ϖu * (ϖu ^ (i + 1))⁻¹ := by group
      rw [h, Units.val_mul, mul_assoc]
      exact mul_mem hϖO (hv k)
    · intro hEq
      have hv : ((ϖu ^ i : Fˣ) : F) • Pi.single k0 (1 : F) ∈ ϖu ^ i • standardLattice F ι := by
        rw [mem_smul_standardLattice]
        intro k
        rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, Units.inv_mul, one_mul, Pi.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      rw [← hEq, mem_smul_standardLattice] at hv
      have h := hv k0
      rw [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, ← Units.val_mul] at h
      have h' : ((ϖu ^ (i + 1))⁻¹ * ϖu ^ i : Fˣ) = ϖu⁻¹ := by group
      rw [h', Units.val_inv_eq_inv_val, coe_uniformizerAsUnit] at h
      exact inv_coe_uniformizer_not_mem hϖ h
  exists_period := by
    refine ⟨1, one_pos, fun i => ?_⟩
    rw [jacobson_integer_eq_maximalIdeal, hϖ.maximalIdeal_eq,
      Submodule.ideal_span_singleton_smul, Nat.cast_one, add_comm, zpow_one_add, mul_smul]
    ext v
    simp only [Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b, hb, ?_⟩
      ext k
      simp [Subring.smul_def]
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b, hb, ?_⟩
      ext k
      simp [Subring.smul_def]

theorem mem_standard_lattice {ι : Type*} [Fintype ι] [Nonempty ι] {i : ℤ} {v : ι → F} :
    v ∈ (standard hϖ ι).lattice i ↔ ∀ k, ((uniformizerAsUnit hϖ ^ i)⁻¹ : Fˣ) * v k ∈ 𝒪[F] :=
  mem_smul_standardLattice _

/-- The standard basis of `F^ι` splits the standard lattice chain. -/
theorem standard_splits (ι : Type*) [Fintype ι] [Nonempty ι] :
    (standard hϖ ι).Splits (Pi.basisFun F ι) := by
  classical
  intro c i hc k
  have hsum : ∑ k, c k • Pi.basisFun F ι k = c := (Pi.basisFun F ι).sum_repr c
  rw [hsum, mem_standard_lattice] at hc
  rw [mem_standard_lattice]
  intro j
  rw [Pi.basisFun_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs with hjk
  · subst hjk
    rw [mul_one]
    exact hc j
  · rw [mul_zero, mul_zero]
    exact zero_mem _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A space carrying a lattice chain is nonzero, so the index type is nonempty. -/
theorem nonempty_of_latticeChain {ι : Type*} (𝓛 : LatticeChain 𝒪[F] F (ι → F)) :
    Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact (𝓛.lattice_succ_lt 0).ne (Subsingleton.elim _ _)

include hϖ in
/-- **Common splitting basis.** Any two lattice chains in `F^ι` are split by one basis of
`F^ι`. -/
theorem exists_basis_splits_both {ι : Type*} [Fintype ι]
    (𝓛 𝓛' : LatticeChain 𝒪[F] F (ι → F)) :
    ∃ (r : ℕ) (β : Module.Basis (Fin r) F (ι → F)), 𝓛.Splits β ∧ 𝓛'.Splits β := by
  have := 𝓛.nonempty_of_latticeChain
  obtain ⟨r₁, β₁, h₁, -⟩ :=
    𝓛'.exists_basis_splits_of_splits hϖ (standard hϖ ι) (Pi.basisFun F ι) (standard_splits hϖ ι)
  exact 𝓛.exists_basis_splits_of_splits hϖ 𝓛' β₁ h₁

end LatticeChain

end Standard

/-! ### Transfer to arbitrary vector spaces -/

section Transport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable {W : Type*} [AddCommGroup W] [Module F W]

namespace LatticeChain

/-- Transport a lattice chain along a linear equivalence. -/
def linearEquivMap (𝓛 : LatticeChain 𝒪[F] F V) (f : V ≃ₗ[F] W) :
    LatticeChain 𝒪[F] F W where
  lattice i := (𝓛.lattice i).map (f.toLinearMap.restrictScalars 𝒪[F])
  isLattice i :=
    { fg := (𝓛.isLattice i).fg.map _
      span_eq_top := by
        rw [Submodule.map_coe]
        change Submodule.span F (f.toLinearMap '' (𝓛.lattice i : Set V)) = ⊤
        rw [← Submodule.map_span, (𝓛.isLattice i).span_eq_top,
          Submodule.map_top, LinearMap.range_eq_top]
        exact f.surjective }
  lattice_succ_lt i := by
    exact Submodule.map_strictMono_of_injective
      (f := f.toLinearMap.restrictScalars 𝒪[F]) f.injective (𝓛.lattice_succ_lt i)
  exists_period := by
    obtain ⟨e, he, hper⟩ := 𝓛.exists_period
    refine ⟨e, he, fun i => ?_⟩
    rw [hper, Submodule.map_smul'']

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_linearEquivMap (𝓛 : LatticeChain 𝒪[F] F V) (f : V ≃ₗ[F] W)
    (i : ℤ) (x : W) :
    x ∈ (𝓛.linearEquivMap f).lattice i ↔ f.symm x ∈ 𝓛.lattice i := by
  change x ∈ (𝓛.lattice i).map (f.toLinearMap.restrictScalars 𝒪[F]) ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro h
    exact ⟨f.symm x, h, f.apply_symm_apply x⟩

/-- Every lattice chain in an arbitrary vector space has a finite splitting basis. -/
theorem exists_basis_splits {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (𝓛 : LatticeChain 𝒪[F] F V) :
    ∃ (r : ℕ) (β : Module.Basis (Fin r) F V), 𝓛.Splits β := by
  classical
  let b := (Module.finBasis 𝒪[F] (𝓛.lattice 0)).extendOfIsLattice F
  let f := b.equivFun
  let C := 𝓛.linearEquivMap f
  obtain ⟨r, β, hβ, -⟩ := C.exists_basis_splits_both hϖ C
  refine ⟨r, β.map f.symm, ?_⟩
  intro c i hc k
  have hsum : ∑ j, c j • β j ∈ C.lattice i := by
    rw [mem_linearEquivMap]
    simpa [map_sum] using hc
  have hterm := hβ c i hsum k
  rw [mem_linearEquivMap] at hterm
  simpa using hterm

end LatticeChain

end Transport

end Langlands.BushnellKutzko
