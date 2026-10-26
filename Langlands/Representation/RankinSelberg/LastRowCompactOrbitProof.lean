import Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
import Langlands.LocalField.Topology

/-!
# Proof of the exact compact open orbit of the last row

The geometry is proved over any Hausdorff topological field and then applied to the
topology supplied by a p-adic field realization. See the paired Markdown for the route.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Topology
open scoped Matrix

universe uF

section Algebra

variable {K : Type uF} [Field K] [TopologicalSpace K] {n : ℕ}

omit [TopologicalSpace K] in
/-- The last row of a product is the last row of the left factor times the right factor. -/
theorem lastRow_mul_eq_vecMul (g h : Langlands.GeneralLinear (n + 1) K) :
    lastRow (g * h) = lastRow g ᵥ* (h : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :=
  rfl

omit [TopologicalSpace K] in
/-- The mirabolic group is exactly the stabilizer of the last row of the identity. -/
theorem mem_mirabolic_iff_lastRow (a : Langlands.GeneralLinear (n + 1) K) :
    a ∈ mirabolic n K ↔ lastRow a = lastRow (1 : Langlands.GeneralLinear (n + 1) K) := by
  rw [mem_mirabolic, funext_iff]
  refine forall_congr' fun j => ?_
  simp [lastRow, Matrix.one_apply, eq_comm]

omit [TopologicalSpace K] in
/-- The last row of an invertible matrix is nonzero. -/
theorem lastRow_ne_zero (g : Langlands.GeneralLinear (n + 1) K) : lastRow g ≠ 0 := by
  intro h
  have h1 := lastRow_mul_eq_vecMul g g⁻¹
  rw [mul_inv_cancel, h, Matrix.zero_vecMul] at h1
  have h2 := congrFun h1 (Fin.last n)
  simp [lastRow] at h2

omit [TopologicalSpace K] in
/-- For any subgroup `J`, the matrices whose last row lies in the last-row image of `J`
are exactly the products `a * j` with `a` mirabolic and `j ∈ J`. -/
theorem lastRow_mem_image_iff (J : Subgroup (Langlands.GeneralLinear (n + 1) K))
    (g : Langlands.GeneralLinear (n + 1) K) :
    lastRow g ∈ lastRow '' (J : Set (Langlands.GeneralLinear (n + 1) K)) ↔
      ∃ (a : mirabolic n K) (j : J), g = a.val * j.val := by
  constructor
  · rintro ⟨j, hj, hjg⟩
    refine ⟨⟨g * j⁻¹, ?_⟩, ⟨j, hj⟩, by simp⟩
    rw [mem_mirabolic_iff_lastRow, lastRow_mul_eq_vecMul, ← hjg, ← lastRow_mul_eq_vecMul,
      mul_inv_cancel]
  · rintro ⟨a, j, rfl⟩
    refine ⟨j.val, j.property, ?_⟩
    rw [lastRow_mul_eq_vecMul, (mem_mirabolic_iff_lastRow a.val).mp a.property,
      ← lastRow_mul_eq_vecMul, one_mul]

end Algebra

section Topology

variable {K : Type uF} [Field K] [TopologicalSpace K]

/-- The last-row map is continuous for the matrix-unit topology. -/
theorem continuous_lastRow {n : ℕ} :
    Continuous (lastRow : Langlands.GeneralLinear (n + 1) K → Fin (n + 1) → K) :=
  continuous_pi fun j => (GeneralLinear.entry (Fin.last n) j).continuous

variable [IsTopologicalDivisionRing K]

/-- Over a topological field, the underlying-matrix map of the general linear group is a
topological embedding. -/
theorem isEmbedding_generalLinear_val (m : ℕ) :
    IsEmbedding (Units.val : Langlands.GeneralLinear m K → Matrix (Fin m) (Fin m) K) := by
  refine Units.isEmbedding_val_mk' (f := Inv.inv) ?_ fun u => (Matrix.coe_units_inv u).symm
  intro A hA
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_matrix_inv
  have hdet : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hdet

variable [T1Space K]

/-- Over a T1 topological field, invertible matrices form an open set and the
underlying-matrix map of the general linear group is an open embedding. -/
theorem isOpenEmbedding_generalLinear_val (m : ℕ) :
    IsOpenEmbedding (Units.val : Langlands.GeneralLinear m K → Matrix (Fin m) (Fin m) K) := by
  refine ⟨isEmbedding_generalLinear_val m, ?_⟩
  have hrange : Set.range (Units.val : Langlands.GeneralLinear m K → Matrix (Fin m) (Fin m) K) =
      Matrix.det ⁻¹' {0}ᶜ := by
    ext A
    simp only [Set.mem_range, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit).ne_zero
    · intro h
      exact ⟨((Matrix.isUnit_iff_isUnit_det A).mpr (Ne.isUnit h)).unit, rfl⟩
  rw [hrange]
  exact isOpen_compl_singleton.preimage (continuous_id.matrix_det)

/-- The last-row image of an open set containing the identity is a neighborhood of the
last standard row. -/
theorem lastRow_image_mem_nhds {n : ℕ} {U : Set (Langlands.GeneralLinear (n + 1) K)}
    (hU : IsOpen U) (h1 : (1 : Langlands.GeneralLinear (n + 1) K) ∈ U) :
    lastRow '' U ∈ 𝓝 (lastRow (1 : Langlands.GeneralLinear (n + 1) K)) := by
  let f : (Fin (n + 1) → K) → Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    fun s => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K).updateRow (Fin.last n) s
  have hf : Continuous f := continuous_const.matrix_updateRow (Fin.last n) continuous_id
  have hO : IsOpen (Units.val '' U) := (isOpenEmbedding_generalLinear_val (n + 1)).isOpenMap U hU
  have hf1 : f (lastRow (1 : Langlands.GeneralLinear (n + 1) K)) ∈ Units.val '' U := by
    refine ⟨1, h1, ?_⟩
    simp only [f, Units.val_one]
    exact (Matrix.updateRow_eq_self _ _).symm
  filter_upwards [hf.continuousAt.preimage_mem_nhds (hO.mem_nhds hf1)] with s hs
  obtain ⟨u, hu, hus⟩ := hs
  refine ⟨u, hu, ?_⟩
  funext k
  change (u : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (Fin.last n) k = s k
  rw [hus]
  simp [f, Matrix.updateRow_self]

/-- The last-row image of an open subgroup is open in the full row space. -/
theorem isOpen_lastRow_image {n : ℕ} (J : Subgroup (Langlands.GeneralLinear (n + 1) K))
    (hJ : IsOpen (J : Set (Langlands.GeneralLinear (n + 1) K))) :
    IsOpen (lastRow '' (J : Set (Langlands.GeneralLinear (n + 1) K))) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨j₀, hj₀, rfl⟩
  let φ : (Fin (n + 1) → K) → Fin (n + 1) → K :=
    fun t => t ᵥ* ((j₀⁻¹ : Langlands.GeneralLinear (n + 1) K) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) K)
  have hφ : Continuous φ := continuous_id.matrix_vecMul continuous_const
  have hφj : φ (lastRow j₀) = lastRow (1 : Langlands.GeneralLinear (n + 1) K) := by
    simp only [φ]
    rw [← lastRow_mul_eq_vecMul, mul_inv_cancel]
  have hmem := lastRow_image_mem_nhds hJ J.one_mem
  rw [← hφj] at hmem
  filter_upwards [hφ.continuousAt.preimage_mem_nhds hmem] with t ht
  obtain ⟨j₁, hj₁, hj₁t⟩ := ht
  refine ⟨j₁ * j₀, J.mul_mem hj₁ hj₀, ?_⟩
  rw [lastRow_mul_eq_vecMul, hj₁t]
  simp only [φ]
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.vecMul_one]

end Topology

section Indicator

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- The value-one indicator of a compact open set in a Hausdorff space is a
Schwartz–Bruhat function. -/
def compactOpenIndicator (U : Set X) (hc : IsCompact U) (ho : IsOpen U) :
    HarmonicAnalysis.SchwartzBruhat X :=
  ⟨U.indicator (fun _ => 1),
    ((LocallyConstant.const X (1 : ℂ)).indicator ⟨hc.isClosed, ho⟩).isLocallyConstant,
    HasCompactSupport.intro hc (fun _ hx => Set.indicator_of_notMem hx _)⟩

@[simp] theorem coe_compactOpenIndicator (U : Set X) (hc : IsCompact U) (ho : IsOpen U) :
    (compactOpenIndicator U hc ho : X → ℂ) = U.indicator (fun _ => (1 : ℂ)) :=
  rfl

end Indicator

/-- The exact compact open last-row orbit, over any Hausdorff topological field. -/
theorem lastRowCompactOrbit_of_field {K : Type uF} [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [T2Space K] (n : ℕ)
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1) K))
    (hJ : IsCompact (J : Set (Langlands.GeneralLinear (n + 1) K))) :
    let R : Set (Fin (n + 1) → K) := lastRow '' (J : Set (Langlands.GeneralLinear (n + 1) K))
    IsCompact R ∧ IsOpen R ∧
    (∀ r ∈ R, r ≠ 0) ∧
    lastRow (1 : Langlands.GeneralLinear (n + 1) K) ∈ R ∧
    (∃ Φ : HarmonicAnalysis.SchwartzBruhat (Fin (n + 1) → K),
      (Φ : (Fin (n + 1) → K) → ℂ) = R.indicator (fun _ => (1 : ℂ))) ∧
    (∀ g : Langlands.GeneralLinear (n + 1) K, lastRow g ∈ R ↔
      ∃ (a : mirabolic n K) (j : J), g = a.val * j.val) := by
  intro R
  have hc : IsCompact R := hJ.image continuous_lastRow
  have ho : IsOpen R := isOpen_lastRow_image J.toSubgroup J.isOpen
  refine ⟨hc, ho, ?_, ⟨1, J.one_mem, rfl⟩, ⟨compactOpenIndicator R hc ho, rfl⟩,
    fun g => lastRow_mem_image_iff J.toSubgroup g⟩
  rintro _ ⟨j, -, rfl⟩
  exact lastRow_ne_zero j

/-- The published last-row compact open orbit statement holds for every supplied
p-adic field realization and every rank. -/
theorem lastRowCompactOrbit {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    LastRowCompactOrbitStatement.{uF} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  exact fun J hJ => lastRowCompactOrbit_of_field n J hJ

end Langlands.RankinSelberg
