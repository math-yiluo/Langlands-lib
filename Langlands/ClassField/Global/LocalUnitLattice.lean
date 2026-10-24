import Langlands.Cohomology.CompleteFiltration

/-!
# Normal-basis filtrations of the units of a complete ultrametric field

Let `L/K` be a finite Galois extension, where `L` is a complete ultrametric normed field
whose norm is preserved by `Gal(L/K)`, and let `ϖ ∈ K` have norm in `(0, 1)`. A normal basis
`(σ α)_σ` with `‖α‖ ≤ 1` spans a `Gal(L/K)`-stable lattice `M` of `L` over the
`ϖ`-integral elements of `K`, and `ϖ^c O_L ⊆ M` for some `c`. For `m > c` the units
`u ≡ 1 mod ϖ^m M` form a `Gal(L/K)`-stable subgroup `V_m` of `Lˣ`. The graded pieces
`V_m / V_{m+1}` are coinduced, and the filtration is complete and separated. Hence every
multiplicative `1`- or `2`-cocycle of `Gal(L/K)` with values in `V_{c+1}` is a coboundary
with values in `V_{c+1}`.
-/

namespace Langlands.ClassField.Global.LocalUnitLattice

open groupCohomology Langlands.Cohomology.CompleteFiltration

/-- The data of the normal-basis filtration: a normal basis of vectors of norm at most `1`, an
element `ϖ` of `K` with `0 < ‖ϖ‖ < 1`, and an exponent `c` with `ϖ^c O_L ⊆ M`, for the lattice
`M` spanned by the basis over the `ϖ`-integral elements of `K`. The Galois action preserves
the norm. -/
structure LatticeData (K L : Type*) [Field K] [NormedField L] [Algebra K L] where
  /-- A normal basis. -/
  basis : Module.Basis (L ≃ₐ[K] L) K L
  /-- An element of `K` of norm strictly between `0` and `1`. -/
  ϖ : K
  /-- The exponent with `ϖ^c O_L ⊆ M`. -/
  c : ℕ
  basis_apply : ∀ σ : L ≃ₐ[K] L, basis σ = σ (basis 1)
  norm_basis_le : ∀ σ, ‖basis σ‖ ≤ 1
  norm_map : ∀ (σ : L ≃ₐ[K] L) (x : L), ‖σ x‖ = ‖x‖
  norm_ϖ_pos : 0 < ‖algebraMap K L ϖ‖
  norm_ϖ_lt_one : ‖algebraMap K L ϖ‖ < 1
  norm_coord_le : ∀ x σ, ‖x‖ ≤ ‖algebraMap K L ϖ‖ ^ c → ‖algebraMap K L (basis.repr x σ)‖ ≤ 1

namespace LatticeData

variable {K L : Type*} [Field K] [NormedField L] [Algebra K L] [FiniteDimensional K L]
  (D : LatticeData K L)

set_option linter.unusedSectionVars false

theorem coe_smul_units (σ : L ≃ₐ[K] L) (u : Lˣ) : ((σ • u : Lˣ) : L) = σ u := by
  rw [AlgEquiv.smul_units_def]
  rfl

/-- The norm `‖ϖ‖`. -/
noncomputable def radius : ℝ := ‖algebraMap K L D.ϖ‖

theorem radius_pos : 0 < D.radius := D.norm_ϖ_pos

theorem radius_lt_one : D.radius < 1 := D.norm_ϖ_lt_one

theorem norm_ϖ_pow (m : ℕ) : ‖algebraMap K L (D.ϖ ^ m)‖ = D.radius ^ m := by
  rw [map_pow, norm_pow]
  rfl

theorem ϖ_pow_ne_zero (m : ℕ) : algebraMap K L (D.ϖ ^ m) ≠ 0 := by
  intro h
  have := D.norm_ϖ_pow m
  rw [h, norm_zero] at this
  exact (pow_pos D.radius_pos m).ne' this.symm

theorem radius_pow_le {m n : ℕ} (h : m ≤ n) : D.radius ^ n ≤ D.radius ^ m :=
  pow_le_pow_of_le_one D.radius_pos.le D.radius_lt_one.le h

/-- The coordinates of `x` in the normal basis, as elements of `L`. -/
noncomputable def coord (x : L) (σ : L ≃ₐ[K] L) : L := algebraMap K L (D.basis.repr x σ)

theorem coord_add (x y : L) (σ : L ≃ₐ[K] L) : D.coord (x + y) σ = D.coord x σ + D.coord y σ := by
  simp [coord]

theorem coord_sub (x y : L) (σ : L ≃ₐ[K] L) : D.coord (x - y) σ = D.coord x σ - D.coord y σ := by
  simp [coord]

theorem coord_neg (x : L) (σ : L ≃ₐ[K] L) : D.coord (-x) σ = -D.coord x σ := by
  simp [coord]

theorem coord_algebraMap_mul (k : K) (x : L) (σ : L ≃ₐ[K] L) :
    D.coord (algebraMap K L k * x) σ = algebraMap K L k * D.coord x σ := by
  simp [coord, ← Algebra.smul_def]

theorem repr_map (τ : L ≃ₐ[K] L) (x : L) (σ : L ≃ₐ[K] L) :
    D.basis.repr (τ x) σ = D.basis.repr x (τ⁻¹ * σ) := by
  have : (Finsupp.lapply σ ∘ₗ D.basis.repr.toLinearMap ∘ₗ τ.toLinearMap) =
      Finsupp.lapply (τ⁻¹ * σ) ∘ₗ D.basis.repr.toLinearMap := by
    refine D.basis.ext fun ρ => ?_
    have hρ : τ (D.basis ρ) = D.basis (τ * ρ) := by
      rw [D.basis_apply ρ, D.basis_apply (τ * ρ), AlgEquiv.mul_apply]
    classical
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe,
      Finsupp.lapply_apply, hρ, Module.Basis.repr_self]
    rw [Finsupp.single_apply, Finsupp.single_apply]
    simp only [eq_inv_mul_iff_mul_eq]
  exact LinearMap.congr_fun this x

theorem coord_map (τ : L ≃ₐ[K] L) (x : L) (σ : L ≃ₐ[K] L) :
    D.coord (τ x) σ = D.coord x (τ⁻¹ * σ) := by
  rw [coord, coord, repr_map]

theorem repr_sum (k : (L ≃ₐ[K] L) → K) (σ : L ≃ₐ[K] L) :
    D.basis.repr (∑ ρ, k ρ • D.basis ρ) σ = k σ := by
  rw [Module.Basis.repr_sum_self]

variable [IsUltrametricDist L]

theorem norm_le_of_coord (x : L) {s : ℝ} (hs : 0 ≤ s) (h : ∀ σ, ‖D.coord x σ‖ ≤ s) :
    ‖x‖ ≤ s := by
  rw [← D.basis.sum_repr x]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hs fun σ _ => ?_
  rw [Algebra.smul_def, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (D.norm_basis_le σ)).trans (h σ)

theorem norm_coord_le_pow (x : L) (σ : L ≃ₐ[K] L) (j : ℕ) (h : ‖x‖ ≤ D.radius ^ (D.c + j)) :
    ‖D.coord x σ‖ ≤ D.radius ^ j := by
  set y := algebraMap K L (D.ϖ ^ j)⁻¹ * x with hy
  have hj := D.ϖ_pow_ne_zero j
  have hyn : ‖y‖ ≤ ‖algebraMap K L D.ϖ‖ ^ D.c := by
    rw [hy, map_inv₀, norm_mul, norm_inv, D.norm_ϖ_pow, inv_mul_le_iff₀ (pow_pos D.radius_pos j)]
    change ‖x‖ ≤ D.radius ^ j * D.radius ^ D.c
    rw [← pow_add, add_comm]
    exact h
  have hyc := D.norm_coord_le y σ hyn
  have hxy : D.coord x σ = algebraMap K L (D.ϖ ^ j) * D.coord y σ := by
    rw [hy, coord_algebraMap_mul, map_inv₀, mul_inv_cancel_left₀ hj]
  rw [hxy, norm_mul, D.norm_ϖ_pow]
  exact mul_le_of_le_one_right (pow_pos D.radius_pos j).le hyc

/-- `u ≡ 1 mod ϖ^m M`: every coordinate of `u - 1` has norm at most `‖ϖ‖^m`. -/
def IsNear (m : ℕ) (u : L) : Prop := ∀ σ, ‖D.coord (u - 1) σ‖ ≤ D.radius ^ m

variable {D} in
theorem IsNear.mono {m n : ℕ} {u : L} (hu : D.IsNear n u) (h : m ≤ n) : D.IsNear m u :=
  fun σ => (hu σ).trans (D.radius_pow_le h)

variable {D} in
theorem IsNear.norm_sub_one_le {m : ℕ} {u : L} (hu : D.IsNear m u) : ‖u - 1‖ ≤ D.radius ^ m :=
  D.norm_le_of_coord _ (pow_nonneg D.radius_pos.le m) hu

theorem isNear_of_norm_sub_one_le {m : ℕ} {u : L} (hu : ‖u - 1‖ ≤ D.radius ^ (D.c + m)) :
    D.IsNear m u :=
  fun σ => D.norm_coord_le_pow _ σ m hu

variable {D} in
theorem IsNear.norm_eq_one {m : ℕ} {u : L} (hu : D.IsNear m u) (hm : 0 < m) : ‖u‖ = 1 := by
  have h1 : ‖u - 1‖ < 1 :=
    hu.norm_sub_one_le.trans_lt (pow_lt_one₀ D.radius_pos.le D.radius_lt_one hm.ne')
  have h2 : ‖u - 1‖ ≠ ‖(1 : L)‖ := by rw [norm_one]; exact h1.ne
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2
  rw [sub_add_cancel, norm_one, max_eq_right h1.le] at this
  exact this

theorem isNear_one (m : ℕ) : D.IsNear m 1 := fun σ => by
  simp [coord, pow_nonneg D.radius_pos.le]

variable {D} in
theorem IsNear.map {m : ℕ} {u : L} (hu : D.IsNear m u) (τ : L ≃ₐ[K] L) : D.IsNear m (τ u) :=
  fun σ => by
    rw [show τ u - 1 = τ (u - 1) by rw [map_sub, map_one], coord_map]
    exact hu _

/-- The product estimate: for `u, u'` near `1` at level `m > c`, `(u - 1)(u' - 1)` is near `0`
at level `m + 1`. -/
theorem norm_coord_mul_le {m : ℕ} (hm : D.c < m) {x y : L} (hx : ‖x‖ ≤ D.radius ^ m)
    (hy : ‖y‖ ≤ D.radius ^ m) (σ : L ≃ₐ[K] L) : ‖D.coord (x * y) σ‖ ≤ D.radius ^ (m + 1) := by
  apply D.norm_coord_le_pow
  rw [norm_mul]
  calc ‖x‖ * ‖y‖ ≤ D.radius ^ m * D.radius ^ m :=
        mul_le_mul hx hy (norm_nonneg _) (pow_nonneg D.radius_pos.le m)
    _ = D.radius ^ (m + m) := (pow_add _ _ _).symm
    _ ≤ D.radius ^ (D.c + (m + 1)) := D.radius_pow_le (by omega)

variable {D} in
theorem IsNear.mul {m : ℕ} (hm : D.c < m) {u u' : L} (hu : D.IsNear m u)
    (hu' : D.IsNear m u') : D.IsNear m (u * u') := fun σ => by
  rw [show u * u' - 1 = (u - 1) + (u' - 1) + (u - 1) * (u' - 1) by ring, coord_add, coord_add]
  have h3 := D.norm_coord_mul_le hm hu.norm_sub_one_le hu'.norm_sub_one_le σ
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hu σ) (hu' σ))
  · exact h3.trans (D.radius_pow_le (Nat.le_succ m))

variable {D} in
theorem IsNear.inv {m : ℕ} (hm : D.c < m) {u : L} (hu : D.IsNear m u) :
    D.IsNear m u⁻¹ := fun σ => by
  have hu1 : ‖u‖ = 1 := hu.norm_eq_one (by omega)
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  rw [show u⁻¹ - 1 = -(u - 1) + (u - 1) * ((u - 1) * u⁻¹) by field_simp; ring, coord_add,
    coord_neg]
  have h2 : ‖(u - 1) * u⁻¹‖ ≤ D.radius ^ m := by
    rw [norm_mul, norm_inv, hu1, inv_one, mul_one]
    exact hu.norm_sub_one_le
  have h3 := D.norm_coord_mul_le hm hu.norm_sub_one_le h2 σ
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_neg]; exact hu σ
  · exact h3.trans (D.radius_pow_le (Nat.le_succ m))

/-- The subgroup `V_m` of units `u ≡ 1 mod ϖ^m M`, for `m > c`. -/
def filtration (m : ℕ) (hm : D.c < m) : Subgroup Lˣ where
  carrier := {u | D.IsNear m u}
  one_mem' := D.isNear_one m
  mul_mem' {u u'} hu hu' := by
    change D.IsNear m (u * u' : Lˣ)
    rw [Units.val_mul]
    exact IsNear.mul hm hu hu'
  inv_mem' {u} hu := by
    change D.IsNear m ((u⁻¹ : Lˣ) : L)
    rw [Units.val_inv_eq_inv_val]
    exact IsNear.inv hm hu

theorem mem_filtration {m : ℕ} (hm : D.c < m) (u : Lˣ) :
    u ∈ D.filtration m hm ↔ D.IsNear m u := Iff.rfl

/-- The canonical filtration `V k = V_{c+1+k}`. -/
def unitFiltration (k : ℕ) : Subgroup Lˣ := D.filtration (D.c + 1 + k) (by omega)

theorem mem_unitFiltration (k : ℕ) (u : Lˣ) :
    u ∈ D.unitFiltration k ↔ D.IsNear (D.c + 1 + k) u := Iff.rfl

theorem smul_mem_unitFiltration (k : ℕ) (g : L ≃ₐ[K] L) {u : Lˣ}
    (hu : u ∈ D.unitFiltration k) : g • u ∈ D.unitFiltration k := by
  rw [mem_unitFiltration, coe_smul_units]
  exact ((mem_unitFiltration D k u).1 hu).map g

theorem norm_eq_one_of_mem_unitFiltration {k : ℕ} {u : Lˣ} (hu : u ∈ D.unitFiltration k) :
    ‖(u : L)‖ = 1 :=
  IsNear.norm_eq_one ((mem_unitFiltration D k u).1 hu) (by omega)

theorem mem_unitFiltration_zero_of_norm_le (u : Lˣ)
    (hu : ‖(u : L) - 1‖ ≤ D.radius ^ (D.c + (D.c + 1))) : u ∈ D.unitFiltration 0 :=
  D.isNear_of_norm_sub_one_le hu

theorem eq_one_of_forall_mem_unitFiltration {u : Lˣ} (hu : ∀ k, u ∈ D.unitFiltration k) :
    u = 1 := by
  by_contra hne
  have hpos : 0 < ‖(u : L) - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hne (Units.ext h)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos D.radius_lt_one
  have h := (IsNear.norm_sub_one_le ((mem_unitFiltration D n u).1 (hu n))).trans
    (D.radius_pow_le (m := n) (n := D.c + 1 + n) (by omega))
  exact absurd (h.trans_lt hn) (lt_irrefl _)

section Complete

variable [CompleteSpace L]

theorem exists_prod_unitFiltration (b : ℕ → Lˣ) (hb : ∀ k, b k ∈ D.unitFiltration k) :
    ∃ s, ∀ k, s / ∏ i ∈ Finset.range k, b i ∈ D.unitFiltration k := by
  set m₀ := D.c + 1
  set Q : ℕ → L := fun k => ((∏ i ∈ Finset.range k, b i : Lˣ) : L) with hQ
  have hb1 : ∀ i, ‖(b i : L)‖ = 1 := fun i => D.norm_eq_one_of_mem_unitFiltration (hb i)
  have hQ1 : ∀ k, ‖Q k‖ = 1 := fun k => by
    simp only [hQ, Units.coe_prod, norm_prod, hb1, Finset.prod_const_one]
  have hdist : ∀ k, dist (Q k) (Q (k + 1)) ≤ D.radius ^ m₀ * D.radius ^ k := fun k => by
    rw [dist_eq_norm, show Q (k + 1) = Q k * b k by
      simp only [hQ, Finset.prod_range_succ, Units.val_mul],
      show Q k - Q k * b k = Q k * (1 - b k) by ring, norm_mul, hQ1, one_mul, norm_sub_rev,
      ← pow_add]
    exact IsNear.norm_sub_one_le ((mem_unitFiltration D k _).1 (hb k))
  have hcauchy := cauchySeq_of_le_geometric D.radius (D.radius ^ m₀) D.radius_lt_one hdist
  obtain ⟨s₀, hs₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hs₀1 : ‖s₀‖ = 1 := by
    have h := (continuous_norm.tendsto s₀).comp hs₀
    have h' : (fun k => ‖Q k‖) = fun _ => (1 : ℝ) := funext hQ1
    simp only [Function.comp_def, h'] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  have hs₀0 : s₀ ≠ 0 := by rintro rfl; simp at hs₀1
  refine ⟨Units.mk0 s₀ hs₀0, fun k => ?_⟩
  have hε : 0 < D.radius ^ (D.c + (m₀ + k)) := pow_pos D.radius_pos _
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hs₀ _ hε
  set n := max N k
  have hn := hN n (le_max_left _ _)
  have hQk : Q k ≠ 0 := by intro h; have := hQ1 k; rw [h, norm_zero] at this; simp at this
  have hmem : (∏ i ∈ Finset.Ico k n, b i) ∈ D.unitFiltration k :=
    Subgroup.prod_mem _ fun i hi => by
      rw [mem_unitFiltration]
      exact IsNear.mono (n := D.c + 1 + i) ((mem_unitFiltration D i _).1 (hb i))
        (by simp at hi; omega)
  have hprod : ((∏ i ∈ Finset.Ico k n, b i : Lˣ) : L) = Q n / Q k := by
    rw [Finset.prod_Ico_eq_div _ (le_max_right _ _), Units.val_div_eq_div_val]
  rw [mem_unitFiltration, Units.val_div_eq_div_val, Units.val_mk0]
  change D.IsNear (m₀ + k) (s₀ / Q k)
  intro σ
  rw [show s₀ / Q k - 1 = (s₀ - Q n) / Q k + (Q n / Q k - 1) by field_simp; ring, coord_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · apply D.norm_coord_le_pow
    rw [norm_div, hQ1, div_one, ← dist_eq_norm, dist_comm]
    exact hn.le
  · rw [← hprod]
    exact (mem_unitFiltration D k _).1 hmem σ

theorem isCompleteFiltration : IsCompleteFiltration (L ≃ₐ[K] L) D.unitFiltration where
  smul_mem k g _ hx := D.smul_mem_unitFiltration k g hx
  eq_one _ hx := D.eq_one_of_forall_mem_unitFiltration hx
  exists_prod b hb := D.exists_prod_unitFiltration b hb

end Complete


section Approximation

/-- The rescaled coordinates `(ϖ^{-m} (u - 1))_σ ∈ K` of an element `u`. -/
noncomputable def lin (m : ℕ) (u : L) (σ : L ≃ₐ[K] L) : K :=
  D.basis.repr (algebraMap K L (D.ϖ ^ m)⁻¹ * (u - 1)) σ

theorem ϖ_ne_zero : D.ϖ ≠ 0 := fun h => by
  have := D.norm_ϖ_pos
  rw [h, map_zero, norm_zero] at this
  exact lt_irrefl _ this

theorem norm_algebraMap_repr_scaled (m : ℕ) (z : L) (σ : L ≃ₐ[K] L) :
    ‖algebraMap K L (D.basis.repr (algebraMap K L (D.ϖ ^ m)⁻¹ * z) σ)‖ =
      (D.radius ^ m)⁻¹ * ‖D.coord z σ‖ := by
  change ‖D.coord (algebraMap K L (D.ϖ ^ m)⁻¹ * z) σ‖ = _
  rw [coord_algebraMap_mul, norm_mul, map_inv₀, norm_inv, D.norm_ϖ_pow]

theorem isNear_iff_lin (m : ℕ) (u : L) :
    D.IsNear m u ↔ ∀ σ, ‖algebraMap K L (D.lin m u σ)‖ ≤ 1 := by
  refine forall_congr' fun σ => ?_
  rw [lin, norm_algebraMap_repr_scaled, inv_mul_le_iff₀ (pow_pos D.radius_pos m), mul_one]

theorem isNear_succ_iff_lin (m : ℕ) (u : L) :
    D.IsNear (m + 1) u ↔ ∀ σ, ‖algebraMap K L (D.lin m u σ)‖ ≤ D.radius := by
  refine forall_congr' fun σ => ?_
  rw [lin, norm_algebraMap_repr_scaled, inv_mul_le_iff₀ (pow_pos D.radius_pos m), pow_succ]

theorem lin_map (m : ℕ) (τ : L ≃ₐ[K] L) (u : L) (σ : L ≃ₐ[K] L) :
    D.lin m (τ u) σ = D.lin m u (τ⁻¹ * σ) := by
  rw [lin, lin, ← repr_map]
  congr 2
  rw [map_mul, AlgEquiv.commutes, map_sub, map_one]

theorem lin_sum (m : ℕ) (k : (L ≃ₐ[K] L) → K) (σ : L ≃ₐ[K] L) :
    D.lin m (1 + algebraMap K L (D.ϖ ^ m) * ∑ ρ, k ρ • D.basis ρ) σ = k σ := by
  rw [lin, add_sub_cancel_left, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ (pow_ne_zero m D.ϖ_ne_zero), map_one, one_mul, repr_sum]

variable {D} in
theorem IsNear.div {m : ℕ} (hm : D.c < m) {u u' : L} (hu : D.IsNear m u)
    (hu' : D.IsNear m u') : D.IsNear m (u / u') := by
  rw [div_eq_mul_inv]
  exact hu.mul hm (hu'.inv hm)

theorem isNear_sum {m : ℕ} (k : (L ≃ₐ[K] L) → K) (hk : ∀ ρ, ‖algebraMap K L (k ρ)‖ ≤ 1) :
    D.IsNear m (1 + algebraMap K L (D.ϖ ^ m) * ∑ ρ, k ρ • D.basis ρ) := by
  rw [isNear_iff_lin]
  intro σ
  rw [lin_sum]
  exact hk σ

theorem lin_sub_lin (m : ℕ) (x y : L) (σ : L ≃ₐ[K] L) :
    D.lin m x σ - D.lin m y σ = D.basis.repr (algebraMap K L (D.ϖ ^ m)⁻¹ * (x - y)) σ := by
  rw [lin, lin, ← Finsupp.sub_apply, ← map_sub, ← mul_sub, sub_sub_sub_cancel_right]

variable (K L) in
/-- The elements of `K` whose image in `L` has norm at most `s`. -/
def normBall (s : ℝ) (hs : 0 ≤ s) : AddSubgroup K where
  carrier := {k | ‖algebraMap K L k‖ ≤ s}
  zero_mem' := by simp [hs]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, map_neg, norm_neg] at *
    exact ha

theorem repr_scaled_mem_normBall {m : ℕ} {z : L} {σ : L ≃ₐ[K] L}
    (h : ‖D.coord z σ‖ ≤ D.radius ^ (m + 1)) :
    D.basis.repr (algebraMap K L (D.ϖ ^ m)⁻¹ * z) σ ∈ normBall K L D.radius D.radius_pos.le := by
  change ‖algebraMap K L _‖ ≤ D.radius
  rw [norm_algebraMap_repr_scaled, inv_mul_le_iff₀ (pow_pos D.radius_pos m), ← pow_succ]
  exact h

/-- The rescaled coordinates are additive modulo `ϖ`, for products. -/
theorem lin_mul_mem {m : ℕ} (hm : D.c < m) {u u' : L} (hu : D.IsNear m u)
    (hu' : D.IsNear m u') (σ : L ≃ₐ[K] L) :
    D.lin m (u * u') σ - D.lin m u σ - D.lin m u' σ ∈ normBall K L D.radius D.radius_pos.le := by
  rw [sub_sub, lin, lin, lin, ← Finsupp.add_apply, ← map_add, ← mul_add, ← Finsupp.sub_apply,
    ← map_sub, ← mul_sub, show u * u' - 1 - (u - 1 + (u' - 1)) = (u - 1) * (u' - 1) by ring]
  exact D.repr_scaled_mem_normBall
    (D.norm_coord_mul_le hm hu.norm_sub_one_le hu'.norm_sub_one_le σ)

/-- The rescaled coordinates are additive modulo `ϖ`, for quotients. -/
theorem lin_div_mem {m : ℕ} (hm : D.c < m) {u u' : L} (hu : D.IsNear m u)
    (hu' : D.IsNear m u') (σ : L ≃ₐ[K] L) :
    D.lin m (u / u') σ - D.lin m u σ + D.lin m u' σ ∈ normBall K L D.radius D.radius_pos.le := by
  have hu'1 : ‖u'‖ = 1 := hu'.norm_eq_one (by omega)
  have hu'0 : u' ≠ 0 := by rintro rfl; simp at hu'1
  rw [sub_add, lin, lin, lin, ← Finsupp.sub_apply, ← map_sub, ← mul_sub,
    ← Finsupp.sub_apply, ← map_sub, ← mul_sub,
    show u / u' - 1 - (u - 1 - (u' - 1)) = (u - u') * ((1 - u') / u') by field_simp; ring]
  refine D.repr_scaled_mem_normBall (D.norm_coord_mul_le hm ?_ ?_ σ)
  · rw [show u - u' = (u - 1) + -(u' - 1) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le hu.norm_sub_one_le (by rw [norm_neg]; exact hu'.norm_sub_one_le))
  · rw [norm_div, hu'1, div_one, norm_sub_rev]
    exact hu'.norm_sub_one_le

theorem approx₁ {m : ℕ} (hm : D.c < m) (f : (L ≃ₐ[K] L) → Lˣ) (hf : IsMulCocycle₁ f)
    (hfm : ∀ g, D.IsNear m (f g)) :
    ∃ b : Lˣ, D.IsNear m b ∧ ∀ g, D.IsNear (m + 1) ((f g / coboundary1 b g : Lˣ) : L) := by
  set Y' := normBall K L D.radius D.radius_pos.le
  set Y'' := normBall K L 1 zero_le_one
  set a : (L ≃ₐ[K] L) → (L ≃ₐ[K] L) → K := fun g σ => D.lin m (f g) σ with ha_def
  have ha : ∀ g h σ, a (g * h) σ - a h (g⁻¹ * σ) - a g σ ∈ Y' := by
    intro g h σ
    have e : ((f (g * h) : Lˣ) : L) = g (f h) * f g := by
      rw [hf g h, Units.val_mul, coe_smul_units]
    simp only [ha_def, e, ← D.lin_map m g (f h) σ]
    exact D.lin_mul_mem hm ((hfm h).map g) (hfm g) σ
  have ha'' : ∀ g σ, a g σ ∈ Y'' := fun g σ => (D.isNear_iff_lin m _).1 (hfm g) σ
  obtain ⟨x, hx'', hx⟩ := coinduced_approx₁ Y' Y'' a ha ha''
  set b₀ : L := 1 + algebraMap K L (D.ϖ ^ m) * ∑ ρ, x ρ • D.basis ρ with hb₀_def
  have hb₀ : D.IsNear m b₀ := D.isNear_sum x hx''
  have hb₀1 : ‖b₀‖ = 1 := hb₀.norm_eq_one (by omega)
  have hb₀0 : b₀ ≠ 0 := by intro h; rw [h, norm_zero] at hb₀1; exact zero_ne_one hb₀1
  refine ⟨Units.mk0 b₀ hb₀0, hb₀, fun g => ?_⟩
  rw [D.isNear_succ_iff_lin m]
  intro σ
  change _ ∈ Y'
  have hcoe : ((f g / coboundary1 (Units.mk0 b₀ hb₀0) g : Lˣ) : L) = (f g : L) / (g b₀ / b₀) := by
    simp only [coboundary1, Units.val_div_eq_div_val, coe_smul_units, Units.val_mk0]
  rw [hcoe]
  have hgb : D.IsNear m (g b₀ / b₀) := (hb₀.map g).div hm hb₀
  have h1 := D.lin_div_mem hm (hfm g) hgb σ
  have h2 := D.lin_div_mem hm (hb₀.map g) hb₀ σ
  have h3 := hx g σ
  have e1 : D.lin m (g b₀) σ = x (g⁻¹ * σ) := by rw [D.lin_map, hb₀_def, D.lin_sum]
  have e2 : D.lin m b₀ σ = x σ := by rw [hb₀_def, D.lin_sum]
  convert Y'.add_mem (Y'.sub_mem h1 h2) h3 using 1
  rw [e1, e2]
  simp only [ha_def]
  ring

theorem approx₂ {m : ℕ} (hm : D.c < m) (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)
    (hf : IsMulCocycle₂ f) (hfm : ∀ p, D.IsNear m (f p)) :
    ∃ y : (L ≃ₐ[K] L) → Lˣ, (∀ g, D.IsNear m (y g)) ∧
      ∀ p, D.IsNear (m + 1) ((f p / coboundary2 y p : Lˣ) : L) := by
  set Y' := normBall K L D.radius D.radius_pos.le
  set Y'' := normBall K L 1 zero_le_one
  set a : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → (L ≃ₐ[K] L) → K := fun p σ => D.lin m (f p) σ
    with ha_def
  have ha : ∀ g h j σ, a (g * h, j) σ + a (g, h) σ - a (h, j) (g⁻¹ * σ) - a (g, h * j) σ ∈ Y' := by
    intro g h j σ
    have e : ((f (g * h, j) : Lˣ) : L) * f (g, h) = g (f (h, j)) * f (g, h * j) := by
      rw [← Units.val_mul, hf g h j, Units.val_mul, coe_smul_units]
    have h1 := D.lin_mul_mem hm (hfm (g * h, j)) (hfm (g, h)) σ
    have h2 := D.lin_mul_mem hm ((hfm (h, j)).map g) (hfm (g, h * j)) σ
    rw [e] at h1
    convert Y'.sub_mem h2 h1 using 1
    simp only [ha_def, D.lin_map m g]
    ring
  have ha'' : ∀ p σ, a p σ ∈ Y'' := fun p σ => (D.isNear_iff_lin m _).1 (hfm p) σ
  obtain ⟨x, hx'', hx⟩ := coinduced_approx₂ Y' Y'' a ha ha''
  set y₀ : (L ≃ₐ[K] L) → L := fun g => 1 + algebraMap K L (D.ϖ ^ m) * ∑ ρ, x g ρ • D.basis ρ
    with hy₀_def
  have hy₀ : ∀ g, D.IsNear m (y₀ g) := fun g => D.isNear_sum (x g) (hx'' g)
  have hy₀0 : ∀ g, y₀ g ≠ 0 := fun g h => by
    have := (hy₀ g).norm_eq_one (by omega)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hlin : ∀ g σ, D.lin m (y₀ g) σ = x g σ := fun g σ => D.lin_sum m (x g) σ
  refine ⟨fun g => Units.mk0 (y₀ g) (hy₀0 g), hy₀, fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  rw [D.isNear_succ_iff_lin m]
  intro σ
  change _ ∈ Y'
  set Q : L := g (y₀ h) / y₀ (g * h)
  set W : L := Q * y₀ g
  have hcoe : ((f (g, h) / coboundary2 (fun g => Units.mk0 (y₀ g) (hy₀0 g)) (g, h) : Lˣ) : L) =
      (f (g, h) : L) / W := by
    simp only [coboundary2, Units.val_div_eq_div_val, Units.val_mul, coe_smul_units,
      Units.val_mk0, W, Q]
  rw [hcoe]
  have hQ : D.IsNear m Q := ((hy₀ h).map g).div hm (hy₀ (g * h))
  have hW : D.IsNear m W := hQ.mul hm (hy₀ g)
  have h1 := D.lin_div_mem hm (hfm (g, h)) hW σ
  have h2 := D.lin_mul_mem hm hQ (hy₀ g) σ
  have h3 := D.lin_div_mem hm ((hy₀ h).map g) (hy₀ (g * h)) σ
  have h4 := hx g h σ
  convert Y'.sub_mem (Y'.sub_mem (Y'.sub_mem h1 h2) h3) h4 using 1
  rw [D.lin_map, hlin, hlin, hlin]
  simp only [ha_def]
  ring

section Complete

variable [CompleteSpace L]

/-- Every multiplicative `1`-cocycle with values in `V_{c+1}` is the coboundary of an element
of `V_{c+1}`. -/
theorem exists_coboundary1_eq_of_mem (f : (L ≃ₐ[K] L) → Lˣ) (hf : IsMulCocycle₁ f)
    (hf0 : ∀ g, f g ∈ D.unitFiltration 0) :
    ∃ s ∈ D.unitFiltration 0, ∀ g, g • s / s = f g :=
  exists_coboundary1_eq D.isCompleteFiltration
    (fun k f hf hfk => D.approx₁ (m := D.c + 1 + k) (by omega) f hf hfk) f hf hf0

/-- Every multiplicative `2`-cocycle with values in `V_{c+1}` is the coboundary of a
`1`-cochain with values in `V_{c+1}`. -/
theorem exists_coboundary2_eq_of_mem (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)
    (hf : IsMulCocycle₂ f) (hf0 : ∀ p, f p ∈ D.unitFiltration 0) :
    ∃ s : (L ≃ₐ[K] L) → Lˣ, (∀ g, s g ∈ D.unitFiltration 0) ∧
      ∀ g h, g • s h / s (g * h) * s g = f (g, h) := by
  obtain ⟨s, hs, hs'⟩ := exists_coboundary2_eq D.isCompleteFiltration
    (fun k f hf hfk => D.approx₂ (m := D.c + 1 + k) (by omega) f hf hfk) f hf hf0
  exact ⟨s, hs, fun g h => hs' (g, h)⟩

end Complete

end Approximation

end LatticeData


section Existence

variable {K L : Type*} [Field K] [NormedField L] [IsUltrametricDist L] [Algebra K L]

theorem norm_det_le_one {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n L)
    (h : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hprod : ‖∏ i, A (σ i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> rw [h1]
  · rw [one_smul]; exact hprod
  · rw [Units.neg_smul, one_smul, norm_neg]; exact hprod

theorem norm_adjugate_le_one {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n L)
    (h : ∀ i j, ‖A i j‖ ≤ 1) (i j : n) : ‖A.adjugate i j‖ ≤ 1 := by
  rw [Matrix.adjugate_apply]
  apply norm_det_le_one
  intro k l
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact h _ _

variable [FiniteDimensional K L]

omit [IsUltrametricDist L] in
open Classical in
/-- Dedekind independence: the matrix `(τ (b σ))_{τ,σ}` of a basis is invertible. -/
theorem det_ne_zero (b : Module.Basis (L ≃ₐ[K] L) K L) :
    (Matrix.of fun τ σ : L ≃ₐ[K] L => τ (b σ)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hli : LinearIndependent L (fun f : L ≃ₐ[K] L => (f : L → L)) :=
    LinearIndependent.comp (ι' := L ≃ₐ[K] L) (linearIndependent_monoidHom L L) (fun f => f)
      (fun x y h => by ext; exact DFunLike.ext_iff.1 h _)
  have hcol : ∀ σ, ∑ τ, v τ * τ (b σ) = 0 := fun σ => by
    have := congrFun hv0 σ
    simpa [Matrix.vecMul, dotProduct] using this
  have hsum : ∑ τ, v τ • (τ : L → L) = 0 := by
    funext x
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← b.sum_repr x]
    simp only [map_sum, Algebra.smul_def, map_mul, AlgEquiv.commutes, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [show (∑ τ, v τ * (algebraMap K L (b.repr x σ) * τ (b σ))) =
        algebraMap K L (b.repr x σ) * ∑ τ, v τ * τ (b σ) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring, hcol, mul_zero]
  exact hv (funext fun τ => Fintype.linearIndependent_iff.1 hli v hsum τ)

open Classical in
/-- Cramer's rule: `‖det A‖ · ‖x_σ‖ ≤ ‖x‖` for the coordinates of `x` in the basis. -/
theorem norm_det_mul_norm_coord_le (b : Module.Basis (L ≃ₐ[K] L) K L)
    (hnorm : ∀ (σ : L ≃ₐ[K] L) (x : L), ‖σ x‖ = ‖x‖) (hb : ∀ σ, ‖b σ‖ ≤ 1) (x : L)
    (σ : L ≃ₐ[K] L) :
    ‖(Matrix.of fun τ σ : L ≃ₐ[K] L => τ (b σ)).det‖ * ‖algebraMap K L (b.repr x σ)‖ ≤ ‖x‖ := by
  set A := Matrix.of fun τ σ : L ≃ₐ[K] L => τ (b σ) with hA
  have hAent : ∀ τ ρ, ‖A τ ρ‖ ≤ 1 := fun τ ρ => by
    rw [hA, Matrix.of_apply, hnorm]; exact hb ρ
  have hmv : Matrix.mulVec A (fun ρ => algebraMap K L (b.repr x ρ)) = fun τ => τ x := by
    funext τ
    simp only [Matrix.mulVec, dotProduct, hA, Matrix.of_apply]
    conv_rhs => rw [← b.sum_repr x]
    simp only [map_sum, Algebra.smul_def, map_mul, AlgEquiv.commutes, mul_comm]
  have hcr : A.det * algebraMap K L (b.repr x σ) = ∑ τ, A.adjugate σ τ * τ x := by
    have := congrFun (congrArg (fun w => Matrix.mulVec A.adjugate w) hmv) σ
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec] at this
    simpa [Matrix.mulVec, dotProduct] using this
  rw [← norm_mul, hcr]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg x) fun τ _ => ?_
  rw [norm_mul, hnorm]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_adjugate_le_one A hAent σ τ)

variable [IsGalois K L]

/-- Existence of the normal-basis filtration data for any `ϖ ∈ K` with `0 < ‖ϖ‖ < 1`. -/
theorem exists_latticeData (hnorm : ∀ (σ : L ≃ₐ[K] L) (x : L), ‖σ x‖ = ‖x‖) (ϖ : K)
    (hϖ0 : 0 < ‖algebraMap K L ϖ‖) (hϖ1 : ‖algebraMap K L ϖ‖ < 1) :
    ∃ D : LatticeData K L, D.ϖ = ϖ := by
  classical
  set b₀ := IsGalois.normalBasis K L
  have hb₀ : b₀ 1 ≠ 0 := b₀.ne_zero 1
  have hϖ : ϖ ≠ 0 := by rintro rfl; simp at hϖ0
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hb₀)) hϖ1
  set b := b₀.unitsSMul fun _ => Units.mk0 (ϖ ^ t) (pow_ne_zero t hϖ)
  have hb_apply : ∀ σ, b σ = algebraMap K L (ϖ ^ t) * σ (b₀ 1) := fun σ => by
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, Algebra.smul_def,
      IsGalois.normalBasis_apply]
  have hb_normal : ∀ σ, b σ = σ (b 1) := fun σ => by
    rw [hb_apply, hb_apply 1, map_mul, AlgEquiv.commutes, AlgEquiv.one_apply]
  have hb_norm : ∀ σ, ‖b σ‖ ≤ 1 := fun σ => by
    rw [hb_apply, norm_mul, hnorm, map_pow, norm_pow]
    calc ‖algebraMap K L ϖ‖ ^ t * ‖b₀ 1‖ ≤ ‖b₀ 1‖⁻¹ * ‖b₀ 1‖ :=
          mul_le_mul_of_nonneg_right ht.le (norm_nonneg _)
      _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.2 hb₀)
  have hA := det_ne_zero b
  obtain ⟨c, hc⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hA) hϖ1
  refine ⟨⟨b, ϖ, c, hb_normal, hb_norm, hnorm, hϖ0, hϖ1, fun x σ hx => ?_⟩, rfl⟩
  have h := norm_det_mul_norm_coord_le b hnorm hb_norm x σ
  by_contra hlt
  push Not at hlt
  have hdpos := norm_pos_iff.2 hA
  have : ‖(Matrix.of fun τ σ : L ≃ₐ[K] L => τ (b σ)).det‖ <
      ‖(Matrix.of fun τ σ : L ≃ₐ[K] L => τ (b σ)).det‖ * ‖algebraMap K L (b.repr x σ)‖ := by
    nlinarith
  linarith

end Existence

end Langlands.ClassField.Global.LocalUnitLattice
