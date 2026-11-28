import Langlands.LinearAlgebra.GMFamilies
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Projection

/-! # Euclidean coordinates for field descent

Abstract linear-algebra data for Arthur's descent across a field extension: an injective map
`κ : V₁ → V_T` of real vector spaces, a finite set of roots on `V_T` with positive multiplicities
and integral reflections preserving the multiplicities, and complementary subspaces `B`, `K` of
`V₁`. From these data we build an inner product on `V_T` for which the roots form a root set,
`B` and `K` are orthogonal in `V₁`, and the orthogonal projection to the central directions
preserves `B`. -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Module Submodule

namespace Langlands.GMFamily

/-- **Root sets from orthogonal reflections.** A finite set of nonzero vectors is a root set
if each `r` has a vector `v` with `⟪r, v⟫ = 2` such that `x ↦ x - ⟪r, x⟫ v` is orthogonal,
sends the other vectors `s` to `s - ⟪s, v⟫ r` inside the set, and has integral pairings. -/
theorem isRootSet_of_reflections {E₀ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀]
    {R₀ : Finset E₀} (h0 : (0 : E₀) ∉ R₀)
    (h : ∀ r ∈ R₀, ∃ v : E₀, ⟪r, v⟫ = 2 ∧
      (∀ x y : E₀, ⟪x - ⟪r, x⟫ • v, y - ⟪r, y⟫ • v⟫ = ⟪x, y⟫) ∧
      ∀ s ∈ R₀, s - ⟪s, v⟫ • r ∈ R₀ ∧ ∃ n : ℤ, ⟪s, v⟫ = n) :
    IsRootSet R₀ := by
  have hv : ∀ r ∈ R₀, ∃ v : E₀, v = (2 / ⟪r, r⟫) • r ∧
      ∀ s ∈ R₀, s - ⟪s, v⟫ • r ∈ R₀ ∧ ∃ n : ℤ, ⟪s, v⟫ = n := by
    intro r hr
    obtain ⟨v, hrv, horth, hs⟩ := h r hr
    have hr0 : r ≠ 0 := fun h => h0 (h ▸ hr)
    have hrr : ⟪r, r⟫ ≠ 0 := inner_self_ne_zero.mpr hr0
    refine ⟨v, ?_, hs⟩
    let w := v - (2 / ⟪r, r⟫) • r
    have hrw : ⟪r, w⟫ = 0 := by
      simp only [w, inner_sub_right, real_inner_smul_right, hrv]
      field_simp
      ring
    have hwv : ⟪w, v⟫ = 0 := by
      have h1 := horth w v
      rw [hrw, zero_smul, sub_zero, hrv, show v - (2 : ℝ) • v = -v by
        rw [two_smul]; abel, inner_neg_right] at h1
      linarith
    have hww : ⟪w, w⟫ = 0 := by
      have : ⟪w, w⟫ = ⟪w, v⟫ - (2 / ⟪r, r⟫) * ⟪w, r⟫ := by
        simp only [w]
        rw [inner_sub_right, real_inner_smul_right]
      rw [this, hwv, real_inner_comm r w, hrw, mul_zero, sub_zero]
    have := inner_self_eq_zero.mp hww
    exact sub_eq_zero.mp this
  refine ⟨h0, fun α hα β hβ => ?_, fun α hα β hβ => ?_⟩
  · obtain ⟨v, rfl, hs⟩ := hv α hα
    have h := (hs β hβ).1
    rwa [real_inner_smul_right, show 2 / ⟪α, α⟫ * ⟪β, α⟫ = 2 * ⟪β, α⟫ / ⟪α, α⟫ by ring] at h
  · obtain ⟨v, rfl, hs⟩ := hv α hα
    obtain ⟨n, hn⟩ := (hs β hβ).2
    refine ⟨n, ?_⟩
    rw [← hn, real_inner_smul_right]
    ring

/-- Linear-algebra data for descent across a field extension. -/
structure FieldDescentData (V₁ V : Type*) [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V]
    [Module ℝ V] where
  /-- The inclusion of the fine cocharacter space. -/
  κ : V₁ →ₗ[ℝ] V
  injective : Function.Injective κ
  /-- The roots on the ambient space. -/
  roots : Finset (Module.Dual ℝ V)
  zero_notMem : (0 : Module.Dual ℝ V) ∉ roots
  /-- The multiplicities of the roots. -/
  mult : Module.Dual ℝ V → ℝ
  mult_pos : ∀ γ ∈ roots, 0 < mult γ
  coroot : ∀ γ ∈ roots, ∃ γv : V, γ γv = 2 ∧ ∀ δ ∈ roots, δ - δ γv • γ ∈ roots ∧
    mult (δ - δ γv • γ) = mult δ ∧ ∃ n : ℤ, δ γv = n
  range_eq : LinearMap.range κ = ⨅ γ ∈ roots.filter (fun γ => γ.comp κ = 0), LinearMap.ker γ
  /-- The coarse subspace. -/
  B : Submodule ℝ V₁
  /-- The common kernel of the coarse rational characters. -/
  K : Submodule ℝ V₁
  isCompl : IsCompl B K
  special : ∀ γ ∈ roots, (γ.comp κ).domRestrict B ≠ 0 → ∀ y ∈ K,
    ∑ δ ∈ roots.filter (fun δ => (δ.comp κ).domRestrict B = (γ.comp κ).domRestrict B),
      mult δ * δ (κ y) = 0

namespace FieldDescentData

variable {V₁ V : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V] [Module ℝ V]
variable (D : FieldDescentData V₁ V)

/-- The central directions of `V`. -/
def ZT : Submodule ℝ V := ⨅ γ ∈ D.roots, LinearMap.ker γ

/-- The central directions of `V₁`. -/
def Z₁ : Submodule ℝ V₁ := D.ZT.comap D.κ

theorem mem_ZT {z : V} : z ∈ D.ZT ↔ ∀ γ ∈ D.roots, γ z = 0 := by
  simp [ZT, Submodule.mem_iInf, LinearMap.mem_ker]

theorem mem_Z₁ {x : V₁} : x ∈ D.Z₁ ↔ ∀ γ ∈ D.roots, γ (D.κ x) = 0 := by
  rw [Z₁, Submodule.mem_comap, mem_ZT]

theorem ZT_le_range : D.ZT ≤ LinearMap.range D.κ := by
  rw [D.range_eq]
  intro z hz
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro γ hγ
  exact (D.mem_ZT.mp hz) γ (Finset.mem_filter.mp hγ).1

/-- The projection to `B` along `K`. -/
def πB : V₁ →ₗ[ℝ] V₁ := D.B.projection D.K D.isCompl

/-- The projection to `K` along `B`. -/
def πK : V₁ →ₗ[ℝ] V₁ := D.K.projection D.B D.isCompl.symm

theorem πB_add_πK (x : V₁) : D.πB x + D.πK x = x :=
  Submodule.projection_add_projection_eq_self D.isCompl x

theorem fibre_sum_pos {γ : Module.Dual ℝ V} (hγ : γ ∈ D.roots) :
    0 < ∑ δ ∈ D.roots.filter
      (fun δ => (δ.comp D.κ).domRestrict D.B = (γ.comp D.κ).domRestrict D.B), D.mult δ := by
  apply Finset.sum_pos (fun δ hδ => D.mult_pos δ (Finset.mem_filter.mp hδ).1)
  exact ⟨γ, Finset.mem_filter.mpr ⟨hγ, rfl⟩⟩

/-- The central directions split along `B ⊕ K`. -/
theorem πB_mem_Z₁ {x : V₁} (hx : x ∈ D.Z₁) : D.πB x ∈ D.Z₁ := by
  rw [mem_Z₁]
  intro γ hγ
  have hBx : D.πB x ∈ D.B := Submodule.projection_apply_mem D.isCompl x
  let β := (γ.comp D.κ).domRestrict D.B
  by_cases hβ : β = 0
  · have h := LinearMap.congr_fun hβ ⟨D.πB x, hBx⟩
    simpa [β] using h
  · let fib := D.roots.filter (fun δ => (δ.comp D.κ).domRestrict D.B = β)
    have hK : D.πK x ∈ D.K := Submodule.projection_apply_mem D.isCompl.symm x
    have h1 := D.special γ hγ hβ _ hK
    have h2 : ∑ δ ∈ fib, D.mult δ * δ (D.κ x) = 0 :=
      Finset.sum_eq_zero fun δ hδ => by rw [(D.mem_Z₁.mp hx) δ (Finset.mem_filter.mp hδ).1, mul_zero]
    have h3 : ∑ δ ∈ fib, D.mult δ * δ (D.κ (D.πB x)) = 0 := by
      have hsplit : ∀ δ : Module.Dual ℝ V, δ (D.κ x) = δ (D.κ (D.πB x)) + δ (D.κ (D.πK x)) := by
        intro δ
        rw [← map_add, ← map_add, D.πB_add_πK]
      have : ∑ δ ∈ fib, D.mult δ * δ (D.κ x) = ∑ δ ∈ fib, D.mult δ * δ (D.κ (D.πB x)) +
          ∑ δ ∈ fib, D.mult δ * δ (D.κ (D.πK x)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun δ _ => by rw [hsplit, mul_add]
      rw [this, h1, add_zero] at h2
      exact h2
    have h4 : ∀ δ ∈ fib, δ (D.κ (D.πB x)) = γ (D.κ (D.πB x)) := by
      intro δ hδ
      have h := LinearMap.congr_fun (Finset.mem_filter.mp hδ).2 ⟨D.πB x, hBx⟩
      simpa [β] using h
    rw [Finset.sum_congr rfl fun δ hδ => by rw [h4 δ hδ], ← Finset.sum_mul] at h3
    exact (mul_eq_zero.mp h3).resolve_left (D.fibre_sum_pos hγ).ne'

theorem πK_mem_Z₁ {x : V₁} (hx : x ∈ D.Z₁) : D.πK x ∈ D.Z₁ := by
  rw [eq_sub_of_add_eq' (D.πB_add_πK x)]
  exact D.Z₁.sub_mem hx (D.πB_mem_Z₁ hx)

/-- The central part of `B`. -/
abbrev ZB : Submodule ℝ V₁ := D.Z₁ ⊓ D.B

/-- The central part of `K`. -/
abbrev ZK : Submodule ℝ V₁ := D.Z₁ ⊓ D.K

/-- A retraction onto the central part of `B`. -/
def rB : V₁ →ₗ[ℝ] V₁ :=
  D.ZB.projection (Submodule.exists_isCompl D.ZB).choose (Submodule.exists_isCompl D.ZB).choose_spec

/-- A retraction onto the central part of `K`. -/
def rK : V₁ →ₗ[ℝ] V₁ :=
  D.ZK.projection (Submodule.exists_isCompl D.ZK).choose (Submodule.exists_isCompl D.ZK).choose_spec

/-- The central component in `B`. -/
def pB : V₁ →ₗ[ℝ] V₁ := D.rB ∘ₗ D.πB

/-- The central component in `K`. -/
def pK : V₁ →ₗ[ℝ] V₁ := D.rK ∘ₗ D.πK

theorem pB_mem (x : V₁) : D.pB x ∈ D.ZB := Submodule.projection_apply_mem _ _

theorem pK_mem (x : V₁) : D.pK x ∈ D.ZK := Submodule.projection_apply_mem _ _

theorem pB_of_mem {z : V₁} (hz : z ∈ D.ZB) : D.pB z = z := by
  change D.rB (D.πB z) = z
  rw [πB, Submodule.projection_apply_of_mem_left _ hz.2, rB,
    Submodule.projection_apply_of_mem_left _ hz]

theorem pK_of_mem {z : V₁} (hz : z ∈ D.ZK) : D.pK z = z := by
  change D.rK (D.πK z) = z
  rw [πK, Submodule.projection_apply_of_mem_left _ hz.2, rK,
    Submodule.projection_apply_of_mem_left _ hz]

theorem pB_of_mem_K {y : V₁} (hy : y ∈ D.K) : D.pB y = 0 := by
  change D.rB (D.πB y) = 0
  rw [πB, Submodule.projection_apply_right D.isCompl ⟨y, hy⟩, map_zero]

theorem pK_of_mem_B {y : V₁} (hy : y ∈ D.B) : D.pK y = 0 := by
  change D.rK (D.πK y) = 0
  rw [πK, Submodule.projection_apply_right D.isCompl.symm ⟨y, hy⟩, map_zero]

theorem pB_add_pK {x : V₁} (hx : x ∈ D.Z₁) : D.pB x + D.pK x = x := by
  have hB : D.πB x ∈ D.ZB := ⟨D.πB_mem_Z₁ hx, Submodule.projection_apply_mem D.isCompl x⟩
  have hK : D.πK x ∈ D.ZK :=
    ⟨D.πK_mem_Z₁ hx, Submodule.projection_apply_mem D.isCompl.symm x⟩
  change D.rB (D.πB x) + D.rK (D.πK x) = x
  rw [rB, Submodule.projection_apply_of_mem_left _ hB, rK,
    Submodule.projection_apply_of_mem_left _ hK, D.πB_add_πK]

theorem pB_pB (x : V₁) : D.pB (D.pB x) = D.pB x := D.pB_of_mem (D.pB_mem x)

theorem pK_pK (x : V₁) : D.pK (D.pK x) = D.pK x := D.pK_of_mem (D.pK_mem x)

theorem pB_pK (x : V₁) : D.pB (D.pK x) = 0 := D.pB_of_mem_K (D.pK_mem x).2

theorem pK_pB (x : V₁) : D.pK (D.pB x) = 0 := D.pK_of_mem_B (D.pB_mem x).2

/-- A left inverse of `κ`. -/
def ρ : V →ₗ[ℝ] V₁ :=
  (D.κ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr D.injective)).choose

theorem ρ_κ (x : V₁) : D.ρ (D.κ x) = x :=
  LinearMap.congr_fun
    (D.κ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr D.injective)).choose_spec x

/-- The projection of `V` to its central directions. -/
def P : V →ₗ[ℝ] V := D.κ ∘ₗ (D.pB + D.pK) ∘ₗ D.ρ

theorem P_apply (x : V) : D.P x = D.κ (D.pB (D.ρ x) + D.pK (D.ρ x)) := rfl

theorem P_mem (x : V) : D.P x ∈ D.ZT := by
  rw [P_apply, mem_ZT]
  intro γ hγ
  rw [map_add, map_add, (D.mem_Z₁.mp (D.pB_mem _).1) γ hγ, (D.mem_Z₁.mp (D.pK_mem _).1) γ hγ,
    add_zero]

theorem P_of_mem {z : V} (hz : z ∈ D.ZT) : D.P z = z := by
  obtain ⟨x, rfl⟩ := D.ZT_le_range hz
  have hx : x ∈ D.Z₁ := hz
  rw [P_apply, D.ρ_κ, D.pB_add_pK hx]

theorem pB_ρ_P (x : V) : D.pB (D.ρ (D.P x)) = D.pB (D.ρ x) := by
  rw [P_apply, D.ρ_κ, map_add, D.pB_pB, D.pB_pK, add_zero]

theorem pK_ρ_P (x : V) : D.pK (D.ρ (D.P x)) = D.pK (D.ρ x) := by
  rw [P_apply, D.ρ_κ, map_add, D.pK_pB, D.pK_pK, zero_add]

/-! ### The Euclidean structure -/

section Metric

variable [FiniteDimensional ℝ V₁]

/-- The coordinate index set: the roots, and twice the coordinates of `V₁`. -/
abbrev Coord := D.roots ⊕ (Fin (finrank ℝ V₁) ⊕ Fin (finrank ℝ V₁))

/-- The coordinate functionals. -/
def coordFun : D.Coord → (V →ₗ[ℝ] ℝ) :=
  Sum.elim (fun γ => Real.sqrt (D.mult γ) • (γ : Module.Dual ℝ V))
    (Sum.elim (fun i => (Module.finBasis ℝ V₁).coord i ∘ₗ D.pB ∘ₗ D.ρ)
      (fun i => (Module.finBasis ℝ V₁).coord i ∘ₗ D.pK ∘ₗ D.ρ))

/-- The coordinate embedding of `V` into a Euclidean space. -/
def F : V →ₗ[ℝ] EuclideanSpace ℝ D.Coord :=
  (WithLp.linearEquiv 2 ℝ (D.Coord → ℝ)).symm.toLinearMap ∘ₗ LinearMap.pi D.coordFun

theorem F_apply (x : V) (i : D.Coord) : D.F x i = D.coordFun i x := rfl

/-- The quadratic part of the inner product. -/
def Q (x y : V) : ℝ := ∑ γ ∈ D.roots, D.mult γ * γ x * γ y

/-- The coordinate inner product on `V₁`. -/
def aux (u v : V₁) : ℝ := ∑ i, (Module.finBasis ℝ V₁).repr u i * (Module.finBasis ℝ V₁).repr v i

theorem aux_zero_left (v : V₁) : aux (0 : V₁) v = 0 := by simp [aux]

theorem aux_zero_right (u : V₁) : aux u (0 : V₁) = 0 := by simp [aux]

theorem inner_F (x y : V) :
    ⟪D.F x, D.F y⟫ = D.Q x y + aux (D.pB (D.ρ x)) (D.pB (D.ρ y)) +
      aux (D.pK (D.ρ x)) (D.pK (D.ρ y)) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, F_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
  congr 1
  · unfold Q coordFun
    rw [← Finset.sum_coe_sort D.roots]
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [Sum.elim_inl, LinearMap.smul_apply, smul_eq_mul]
    have h := Real.mul_self_sqrt (D.mult_pos γ γ.prop).le
    linear_combination (γ.1 x * γ.1 y) * h
  · congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
      simp [coordFun, Basis.coord_apply, mul_comm]

theorem F_injective : Function.Injective D.F := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hc (i : D.Coord) : D.coordFun i x = 0 := by
    rw [← F_apply, hx]
    rfl
  have hZ : x ∈ D.ZT := by
    rw [mem_ZT]
    intro γ hγ
    have h := hc (Sum.inl ⟨γ, hγ⟩)
    simp only [coordFun, Sum.elim_inl, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (Real.sqrt_pos.mpr (D.mult_pos γ hγ)).ne'
  have hB : D.pB (D.ρ x) = 0 := (Module.finBasis ℝ V₁).ext_elem fun i => by
    have h := hc (Sum.inr (Sum.inl i))
    simpa [coordFun] using h
  have hK : D.pK (D.ρ x) = 0 := (Module.finBasis ℝ V₁).ext_elem fun i => by
    have h := hc (Sum.inr (Sum.inr i))
    simpa [coordFun] using h
  rw [← D.P_of_mem hZ, P_apply, hB, hK, add_zero, map_zero]

/-- The modified coroot, with no central component. -/
def coroot' (γv : V) : V := γv - D.P γv

omit [FiniteDimensional ℝ V₁] in
theorem root_P {δ : Module.Dual ℝ V} (hδ : δ ∈ D.roots) (x : V) : δ (D.P x) = 0 :=
  (D.mem_ZT.mp (D.P_mem x)) δ hδ

omit [FiniteDimensional ℝ V₁] in
theorem pB_ρ_coroot' (γv : V) : D.pB (D.ρ (D.coroot' γv)) = 0 := by
  rw [coroot', map_sub, map_sub, D.pB_ρ_P, sub_self]

omit [FiniteDimensional ℝ V₁] in
theorem pK_ρ_coroot' (γv : V) : D.pK (D.ρ (D.coroot' γv)) = 0 := by
  rw [coroot', map_sub, map_sub, D.pK_ρ_P, sub_self]

/-- **The reflections are orthogonal.** -/
theorem inner_F_reflection {γ : Module.Dual ℝ V} {γv : V} (hγv : γ γv = 2)
    (hδ : ∀ δ ∈ D.roots, δ - δ γv • γ ∈ D.roots ∧ D.mult (δ - δ γv • γ) = D.mult δ)
    (x y : V) :
    ⟪D.F (x - γ x • D.coroot' γv), D.F (y - γ y • D.coroot' γv)⟫ = ⟪D.F x, D.F y⟫ := by
  rw [inner_F, inner_F]
  have hB (z : V) : D.pB (D.ρ (z - γ z • D.coroot' γv)) = D.pB (D.ρ z) := by
    rw [map_sub, map_sub, map_smul, map_smul, D.pB_ρ_coroot', smul_zero, sub_zero]
  have hK (z : V) : D.pK (D.ρ (z - γ z • D.coroot' γv)) = D.pK (D.ρ z) := by
    rw [map_sub, map_sub, map_smul, map_smul, D.pK_ρ_coroot', smul_zero, sub_zero]
  rw [hB, hB, hK, hK]
  congr 2
  let σ : Module.Dual ℝ V → Module.Dual ℝ V := fun δ => δ - δ γv • γ
  have hσσ : ∀ δ, σ (σ δ) = δ := by
    intro δ
    simp only [σ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hγv]
    ext z
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hval : ∀ δ ∈ D.roots, ∀ z : V, δ (z - γ z • D.coroot' γv) = σ δ z := by
    intro δ hδ' z
    simp only [σ, coroot', map_sub, map_smul, smul_eq_mul, LinearMap.sub_apply,
      LinearMap.smul_apply, D.root_P hδ']
    ring
  unfold Q
  apply Finset.sum_nbij' σ σ (fun δ h => (hδ δ h).1) (fun δ h => (hδ δ h).1)
    (fun δ _ => hσσ δ) (fun δ _ => hσσ δ)
  intro δ hδ'
  rw [hval δ hδ', hval δ hδ', (hδ δ hδ').2]

/-- **`B` and `K` are orthogonal.** -/
theorem inner_F_B_K {x y : V₁} (hx : x ∈ D.B) (hy : y ∈ D.K) :
    ⟪D.F (D.κ x), D.F (D.κ y)⟫ = 0 := by
  rw [inner_F, D.ρ_κ, D.ρ_κ, D.pB_of_mem_K hy, D.pK_of_mem_B hx, aux_zero_right, aux_zero_left,
    add_zero, add_zero]
  let β : Module.Dual ℝ V → (D.B →ₗ[ℝ] ℝ) := fun δ => (δ.comp D.κ).domRestrict D.B
  unfold Q
  rw [← Finset.sum_fiberwise_of_maps_to (g := β) (t := D.roots.image β)
    (fun δ hδ => Finset.mem_image_of_mem β hδ)]
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hj
  have hfib : ∀ δ ∈ D.roots.filter (fun δ => β δ = β γ),
      D.mult δ * δ (D.κ x) * δ (D.κ y) = β γ ⟨x, hx⟩ * (D.mult δ * δ (D.κ y)) := by
    intro δ hδ
    have h := LinearMap.congr_fun (Finset.mem_filter.mp hδ).2 ⟨x, hx⟩
    simp only [β, LinearMap.domRestrict_apply, LinearMap.comp_apply] at h
    simp only [β, LinearMap.domRestrict_apply, LinearMap.comp_apply, h]
    ring
  rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum]
  by_cases hβ : β γ = 0
  · rw [hβ, LinearMap.zero_apply, zero_mul]
  · rw [D.special γ hγ hβ y hy, mul_zero]

/-- **The central projection preserves `B`.** -/
theorem inner_F_central {x w : V₁} (hx : x ∈ D.B) (hw : w ∈ D.Z₁) :
    ⟪D.F (D.κ (x - D.pB x)), D.F (D.κ w)⟫ = 0 := by
  rw [inner_F, D.ρ_κ, D.ρ_κ]
  have h1 : D.pB (x - D.pB x) = 0 := by rw [map_sub, D.pB_pB, sub_self]
  have h2 : D.pK (x - D.pB x) = 0 := by rw [map_sub, D.pK_of_mem_B hx, D.pK_pB, sub_self]
  rw [h1, h2, aux_zero_left, aux_zero_left, add_zero, add_zero]
  unfold Q
  exact Finset.sum_eq_zero fun δ hδ => by rw [(D.mem_Z₁.mp hw) δ hδ, mul_zero]

end Metric

/-! ### The Euclidean models -/

section Realization

variable [FiniteDimensional ℝ V₁]

/-- The Euclidean model of `V`. -/
abbrev E₀ : Type _ := LinearMap.range D.F

/-- The identification of `V` with its Euclidean model. -/
def eT : V ≃ₗ[ℝ] D.E₀ := LinearEquiv.ofInjective D.F D.F_injective

theorem coe_eT (x : V) : (D.eT x : EuclideanSpace ℝ D.Coord) = D.F x := rfl

theorem inner_eT (x y : V) : ⟪D.eT x, D.eT y⟫ = ⟪D.F x, D.F y⟫ := rfl

/-- The vector of a functional in the Euclidean model. -/
def rv (γ : Module.Dual ℝ V) : D.E₀ :=
  (InnerProductSpace.toDual ℝ D.E₀).symm (LinearMap.toContinuousLinearMap (γ ∘ₗ D.eT.symm.toLinearMap))

theorem inner_rv (γ : Module.Dual ℝ V) (x : V) : ⟪D.rv γ, D.eT x⟫ = γ x := by
  rw [rv, InnerProductSpace.toDual_symm_apply]
  simp

theorem rv_sub_smul (δ γ : Module.Dual ℝ V) (c : ℝ) : D.rv (δ - c • γ) = D.rv δ - c • D.rv γ := by
  apply ext_inner_right ℝ
  intro v
  rw [← D.eT.apply_symm_apply v, inner_rv, inner_sub_left, inner_rv]
  have h : ⟪c • D.rv γ, D.eT (D.eT.symm v)⟫ = c * γ (D.eT.symm v) := by
    rw [← D.inner_rv γ (D.eT.symm v)]
    exact real_inner_smul_left (D.rv γ) (D.eT (D.eT.symm v)) c
  rw [h]
  simp

theorem rv_injective : Function.Injective D.rv := by
  intro δ γ h
  ext x
  rw [← D.inner_rv, h, inner_rv]

/-- The roots in the Euclidean model. -/
def R₀ : Finset D.E₀ := D.roots.image D.rv

/-- **The roots form a root set.** -/
theorem isRootSet_R₀ : IsRootSet D.R₀ := by
  apply isRootSet_of_reflections
  · intro h0
    obtain ⟨γ, hγ, he⟩ := Finset.mem_image.mp h0
    apply D.zero_notMem
    have : γ = 0 := D.rv_injective (he.trans (by
      apply ext_inner_right ℝ
      intro v
      rw [← D.eT.apply_symm_apply v, inner_rv, inner_zero_left]
      rfl))
    exact this ▸ hγ
  · intro r hr
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨γv, hγv, hδ⟩ := D.coroot γ hγ
    refine ⟨D.eT (D.coroot' γv), ?_, ?_, ?_⟩
    · rw [inner_rv, coroot', map_sub, D.root_P hγ, hγv, sub_zero]
    · intro x y
      have hx : x - ⟪D.rv γ, x⟫ • D.eT (D.coroot' γv) =
          D.eT (D.eT.symm x - γ (D.eT.symm x) • D.coroot' γv) := by
        rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, ← D.inner_rv γ (D.eT.symm x),
          LinearEquiv.apply_symm_apply]
      have hy : y - ⟪D.rv γ, y⟫ • D.eT (D.coroot' γv) =
          D.eT (D.eT.symm y - γ (D.eT.symm y) • D.coroot' γv) := by
        rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, ← D.inner_rv γ (D.eT.symm y),
          LinearEquiv.apply_symm_apply]
      rw [hx, hy, inner_eT, D.inner_F_reflection hγv (fun δ h => ⟨(hδ δ h).1, (hδ δ h).2.1⟩),
        ← inner_eT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    · intro s hs
      obtain ⟨δ, hδR, rfl⟩ := Finset.mem_image.mp hs
      have hval : ⟪D.rv δ, D.eT (D.coroot' γv)⟫ = δ γv := by
        rw [inner_rv, coroot', map_sub, D.root_P hδR, sub_zero]
      rw [hval, ← rv_sub_smul]
      exact ⟨Finset.mem_image_of_mem _ (hδ δ hδR).1, (hδ δ hδR).2.2⟩

/-- The coordinate embedding of `V₁`. -/
def G₁ : V₁ →ₗ[ℝ] EuclideanSpace ℝ D.Coord := D.F ∘ₗ D.κ

theorem G₁_injective : Function.Injective D.G₁ := D.F_injective.comp D.injective

theorem finrank_range_G₁ : finrank ℝ (LinearMap.range D.G₁) = finrank ℝ V₁ :=
  (LinearEquiv.ofInjective _ D.G₁_injective).finrank_eq.symm

/-- Euclidean coordinates on `V₁`, isometric for the restricted inner product. -/
def e₁ : V₁ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V₁)) :=
  (LinearEquiv.ofInjective D.G₁ D.G₁_injective).trans
    ((stdOrthonormalBasis ℝ (LinearMap.range D.G₁)).repr.toLinearEquiv.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr D.finrank_range_G₁)).toLinearEquiv)

theorem inner_e₁ (x y : V₁) : ⟪D.e₁ x, D.e₁ y⟫ = ⟪D.F (D.κ x), D.F (D.κ y)⟫ := by
  change ⟪(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr D.finrank_range_G₁))
      ((stdOrthonormalBasis ℝ (LinearMap.range D.G₁)).repr
        (LinearEquiv.ofInjective D.G₁ D.G₁_injective x)),
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr D.finrank_range_G₁))
      ((stdOrthonormalBasis ℝ (LinearMap.range D.G₁)).repr
        (LinearEquiv.ofInjective D.G₁ D.G₁_injective y))⟫ = _
  rw [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
  rfl

/-- The isometric embedding of the Euclidean coordinates of `V₁` into the model of `V`. -/
def φ : EuclideanSpace ℝ (Fin (finrank ℝ V₁)) →ₗᵢ[ℝ] D.E₀ :=
  LinearMap.isometryOfInner (D.eT.toLinearMap ∘ₗ D.κ ∘ₗ D.e₁.symm.toLinearMap) (fun x y => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [inner_eT, ← inner_e₁, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])

theorem φ_e₁ (x : V₁) : D.φ (D.e₁ x) = D.eT (D.κ x) := by
  change D.eT (D.κ (D.e₁.symm (D.e₁ x))) = _
  rw [LinearEquiv.symm_apply_apply]

end Realization

end FieldDescentData

end Langlands.GMFamily
