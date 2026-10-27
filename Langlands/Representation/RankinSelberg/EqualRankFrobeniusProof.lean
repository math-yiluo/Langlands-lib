import Langlands.Representation.RankinSelberg.EqualRankFrobeniusStatement
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.HarmonicAnalysis.RowTestSmoothProof
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Group.GL.IntegralSubgroup

/-!
# Proof of the equal-rank Frobenius equivalence

The equivalence is constructed directly on the nonzero-row orbit, using an
additive Haar measure on row space and its determinant scaling. See the paired
Markdown for the route and its correspondence with JPSS (2.10.5)--(2.10.6).
-/

noncomputable section

namespace Langlands.RankinSelberg

universe uF uV uW

namespace EqualRankFrobenius

open HarmonicAnalysis GeneralLinear TrilinearReduction MeasureTheory Topology
open scoped Matrix NNReal

section Geometry

variable {K : Type uF} [Field K] [TopologicalSpace K] {n : ℕ}

omit [TopologicalSpace K] in
/-- Every nonzero row is the last row of an invertible matrix. -/
theorem exists_lastRow_eq (x : Fin (n + 1) → K) (hx : x ≠ 0) :
    ∃ g : Langlands.GeneralLinear (n + 1) K, lastRow g = x := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    exact hx (funext fun j => by_contra fun hj => h ⟨j, hj⟩)
  let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap j (Fin.last n)
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K).updateRow j x).submatrix τ id
  have hsum : (∑ k, x k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) k) = x := by
    funext i
    simp [Matrix.one_apply]
  have hdet : M.det ≠ 0 := by
    have h1 := Matrix.det_updateRow_sum (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) j x
    rw [hsum, Matrix.det_one, smul_eq_mul, mul_one] at h1
    simp only [M, Matrix.det_permute, h1]
    refine mul_ne_zero ?_ hj
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).mpr (Ne.isUnit hdet)).unit, ?_⟩
  funext k
  change M (Fin.last n) k = x k
  simp [M, τ, Equiv.swap_apply_right]

/-- A chosen invertible matrix with prescribed nonzero last row. -/
def lift (x : Fin (n + 1) → K) : Langlands.GeneralLinear (n + 1) K := by
  classical
  exact if h : ∃ g : Langlands.GeneralLinear (n + 1) K, lastRow g = x then h.choose else 1

omit [TopologicalSpace K] in
theorem lastRow_lift (x : Fin (n + 1) → K) (hx : x ≠ 0) : lastRow (lift x) = x := by
  classical
  have h := exists_lastRow_eq x hx
  unfold lift
  split_ifs
  exact h.choose_spec

omit [TopologicalSpace K] in
/-- Two matrices with the same last row differ by a left mirabolic factor. -/
theorem mul_inv_mem_mirabolic_of_lastRow_eq {g g' : Langlands.GeneralLinear (n + 1) K}
    (h : lastRow g' = lastRow g) : g' * g⁻¹ ∈ mirabolic n K := by
  rw [mem_mirabolic_iff_lastRow, lastRow_mul_eq_vecMul, h, ← lastRow_mul_eq_vecMul,
    mul_inv_cancel]

omit [TopologicalSpace K] in
theorem lastRow_mirabolic_mul {p g : Langlands.GeneralLinear (n + 1) K}
    (hp : p ∈ mirabolic n K) : lastRow (p * g) = lastRow g := by
  rw [lastRow_mul_eq_vecMul, (mem_mirabolic_iff_lastRow p).mp hp, ← lastRow_mul_eq_vecMul,
    one_mul]

/-- The right orbit of the last row of `g` under a subgroup `H`. -/
def orbitSet (H : Subgroup (Langlands.GeneralLinear (n + 1) K))
    (g : Langlands.GeneralLinear (n + 1) K) : Set (Fin (n + 1) → K) :=
  (fun h => lastRow (g * h)) '' (H : Set (Langlands.GeneralLinear (n + 1) K))

omit [TopologicalSpace K] in
theorem mem_orbitSet {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    {g : Langlands.GeneralLinear (n + 1) K} {x : Fin (n + 1) → K} :
    x ∈ orbitSet H g ↔ ∃ h ∈ H, lastRow (g * h) = x := Iff.rfl

omit [TopologicalSpace K] in
theorem lastRow_mem_orbitSet (H : Subgroup (Langlands.GeneralLinear (n + 1) K))
    (g : Langlands.GeneralLinear (n + 1) K) : lastRow g ∈ orbitSet H g :=
  ⟨1, H.one_mem, by simp only [mul_one]⟩

omit [TopologicalSpace K] in
theorem zero_notMem_orbitSet (H : Subgroup (Langlands.GeneralLinear (n + 1) K))
    (g : Langlands.GeneralLinear (n + 1) K) : (0 : Fin (n + 1) → K) ∉ orbitSet H g := by
  rintro ⟨h, -, hh⟩
  exact lastRow_ne_zero (g * h) hh

omit [TopologicalSpace K] in
theorem orbitSet_mul_right (H : Subgroup (Langlands.GeneralLinear (n + 1) K))
    (g : Langlands.GeneralLinear (n + 1) K) {h : Langlands.GeneralLinear (n + 1) K}
    (hh : h ∈ H) : orbitSet H (g * h) = orbitSet H g := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨h * k, H.mul_mem hh hk, by simp only [mul_assoc]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨h⁻¹ * k, H.mul_mem (H.inv_mem hh) hk, by simp only [mul_assoc, mul_inv_cancel_left]⟩

omit [TopologicalSpace K] in
theorem orbitSet_eq_of_lastRow_eq (H : Subgroup (Langlands.GeneralLinear (n + 1) K))
    {g g' : Langlands.GeneralLinear (n + 1) K} (h : lastRow g' = lastRow g) :
    orbitSet H g' = orbitSet H g := by
  have hp := mul_inv_mem_mirabolic_of_lastRow_eq h
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k, hk, ?_⟩
    dsimp only
    rw [← lastRow_mirabolic_mul (g := g * k) hp, ← mul_assoc, inv_mul_cancel_right]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k, hk, ?_⟩
    dsimp only
    rw [← lastRow_mirabolic_mul (g := g * k) hp, ← mul_assoc, inv_mul_cancel_right]

omit [TopologicalSpace K] in
/-- Two orbits that meet are equal. -/
theorem orbitSet_eq_of_mem_inter (H : Subgroup (Langlands.GeneralLinear (n + 1) K))
    {g g' : Langlands.GeneralLinear (n + 1) K} {x : Fin (n + 1) → K}
    (hx : x ∈ orbitSet H g) (hx' : x ∈ orbitSet H g') : orbitSet H g = orbitSet H g' := by
  obtain ⟨h, hh, rfl⟩ := hx
  obtain ⟨h', hh', hx'⟩ := hx'
  dsimp only at hx'
  rw [← orbitSet_mul_right H g hh, ← orbitSet_mul_right H g' hh',
    orbitSet_eq_of_lastRow_eq H hx']

/-- The conjugate subgroup `k H k⁻¹`. -/
def conj (k : Langlands.GeneralLinear (n + 1) K)
    (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
    Subgroup (Langlands.GeneralLinear (n + 1) K) :=
  H.map (MulAut.conj k).toMonoidHom

omit [TopologicalSpace K] in
theorem mem_conj {k : Langlands.GeneralLinear (n + 1) K}
    {H : Subgroup (Langlands.GeneralLinear (n + 1) K)} {x : Langlands.GeneralLinear (n + 1) K} :
    x ∈ conj k H ↔ k⁻¹ * x * k ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro hx
    exact ⟨k⁻¹ * x * k, hx, by simp [mul_assoc]⟩

omit [TopologicalSpace K] in
theorem conj_conj_inv (k : Langlands.GeneralLinear (n + 1) K)
    (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) : conj k⁻¹ (conj k H) = H := by
  ext x
  simp only [mem_conj, inv_inv]
  simp [mul_assoc]

omit [TopologicalSpace K] in
theorem conj_eq_self {k : Langlands.GeneralLinear (n + 1) K}
    {H : Subgroup (Langlands.GeneralLinear (n + 1) K)} (hk : k ∈ H) : conj k H = H := by
  ext x
  rw [mem_conj]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hk hx) (H.inv_mem hk)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hk) hx) hk

omit [TopologicalSpace K] in
/-- Right multiplication by `k` pulls an orbit back to an orbit of the conjugate subgroup. -/
theorem preimage_vecMul_orbitSet (H : Subgroup (Langlands.GeneralLinear (n + 1) K))
    (g k : Langlands.GeneralLinear (n + 1) K) :
    (fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) ⁻¹' orbitSet H g =
      orbitSet (conj k H) (g * k⁻¹) := by
  ext x
  simp only [Set.mem_preimage, mem_orbitSet, mem_conj]
  constructor
  · rintro ⟨h, hh, hx⟩
    refine ⟨k * h * k⁻¹, by simpa [mul_assoc] using hh, ?_⟩
    have : g * k⁻¹ * (k * h * k⁻¹) = g * h * k⁻¹ := by group
    rw [this, lastRow_mul_eq_vecMul, hx, Matrix.vecMul_vecMul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  · rintro ⟨h, hh, hx⟩
    refine ⟨k⁻¹ * h * k, hh, ?_⟩
    have : g * (k⁻¹ * h * k) = g * k⁻¹ * h * k := by group
    rw [this, lastRow_mul_eq_vecMul, hx]

omit [TopologicalSpace K] in
theorem orbitSet_conj_mirabolic {p : Langlands.GeneralLinear (n + 1) K}
    (hp : p ∈ mirabolic n K) (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
    orbitSet (conj p H) (p⁻¹) = orbitSet (conj p H) 1 := by
  apply orbitSet_eq_of_lastRow_eq
  rw [← mul_one p⁻¹, lastRow_mirabolic_mul ((mirabolic n K).inv_mem hp)]

variable [IsTopologicalDivisionRing K] [T2Space K]

/-- The last-row map is open. -/
theorem isOpenMap_lastRow :
    IsOpenMap (lastRow : Langlands.GeneralLinear (n + 1) K → Fin (n + 1) → K) := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨u, hu, rfl⟩
  let U' : Set (Langlands.GeneralLinear (n + 1) K) := (fun g => g * u) ⁻¹' U
  have hU' : IsOpen U' := hU.preimage (continuous_id.mul continuous_const)
  have h1 : (1 : Langlands.GeneralLinear (n + 1) K) ∈ U' := by simpa [U'] using hu
  have hmem := lastRow_image_mem_nhds hU' h1
  have hmap : lastRow '' U = rowHomeomorph u '' (lastRow '' U') := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨lastRow (g * u⁻¹), ⟨g * u⁻¹, by simpa [U'] using hg, rfl⟩, ?_⟩
      rw [rowHomeomorph_apply, ← lastRow_mul_eq_vecMul, inv_mul_cancel_right]
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g * u, hg, by rw [rowHomeomorph_apply, lastRow_mul_eq_vecMul]⟩
  rw [hmap]
  have h := (rowHomeomorph u).isOpenMap.image_mem_nhds hmem
  simpa [rowHomeomorph_apply, ← lastRow_mul_eq_vecMul] using h

theorem isOpen_orbitSet {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hH : IsOpen (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (g : Langlands.GeneralLinear (n + 1) K) : IsOpen (orbitSet H g) := by
  have : orbitSet H g = lastRow '' ((fun h => g * h) '' (H : Set _)) := by
    rw [orbitSet, Set.image_image]
  rw [this]
  exact isOpenMap_lastRow _ ((Homeomorph.mulLeft g).isOpenMap _ hH)

omit [T2Space K] in
theorem isCompact_orbitSet {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hH : IsCompact (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (g : Langlands.GeneralLinear (n + 1) K) : IsCompact (orbitSet H g) :=
  hH.image (continuous_lastRow.comp (continuous_const.mul continuous_id))

omit [T2Space K] in
theorem isOpen_conj {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hH : IsOpen (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (k : Langlands.GeneralLinear (n + 1) K) :
    IsOpen (conj k H : Set (Langlands.GeneralLinear (n + 1) K)) := by
  have : (conj k H : Set (Langlands.GeneralLinear (n + 1) K)) =
      (fun x => k⁻¹ * x * k) ⁻¹' (H : Set _) := by
    ext x
    exact mem_conj
  rw [this]
  exact hH.preimage ((continuous_const.mul continuous_id).mul continuous_const)

omit [T2Space K] in
theorem isCompact_conj {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hH : IsCompact (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (k : Langlands.GeneralLinear (n + 1) K) :
    IsCompact (conj k H : Set (Langlands.GeneralLinear (n + 1) K)) := by
  have : (conj k H : Set (Langlands.GeneralLinear (n + 1) K)) =
      (fun x => k * x * k⁻¹) '' (H : Set _) := by
    rw [conj, Subgroup.coe_map]
    rfl
  rw [this]
  exact hH.image ((continuous_const.mul continuous_id).mul continuous_const)

end Geometry

section Indicator

/-- Row test functions vanishing at zero. -/
abbrev Splus (K : Type uF) [Field K] [TopologicalSpace K] [IsTopologicalRing K] (n : ℕ) :=
  ↥(rowVanishingAtZero (F := K) (n := n + 1)).toSubmodule

/-- The right-translation representation on row test functions vanishing at zero. -/
abbrev splusRep (K : Type uF) [Field K] [TopologicalSpace K] [IsTopologicalRing K] (n : ℕ) :
    Representation ℂ (Langlands.GeneralLinear (n + 1) K) (Splus K n) :=
  (rowVanishingAtZero (F := K) (n := n + 1)).toRepresentation

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
  {n : ℕ}

omit [T2Space K] in
@[simp] theorem splusRep_apply (g : Langlands.GeneralLinear (n + 1) K) (Φ : Splus K n)
    (x : Fin (n + 1) → K) :
    (splusRep K n g Φ).1 x = Φ.1 (x ᵥ* (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) :=
  rfl

omit [T2Space K] in
theorem splus_ext {Φ Ψ : Splus K n} (h : ∀ x, Φ.1 x = Ψ.1 x) : Φ = Ψ :=
  Subtype.ext (Hecke.TestFunction.ext h)

omit [T2Space K] in
theorem splus_sum_apply {ι : Type*} (t : Finset ι) (f : ι → Splus K n) (x : Fin (n + 1) → K) :
    (∑ i ∈ t, f i).1 x = ∑ i ∈ t, (f i).1 x := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- The value-one indicator of a compact open set avoiding zero, as a test function
vanishing at zero; it is zero for any other set. -/
def indS (O : Set (Fin (n + 1) → K)) : Splus K n := by
  classical
  exact if h : IsCompact O ∧ IsOpen O ∧ (0 : Fin (n + 1) → K) ∉ O then
    ⟨compactOpenIndicator O h.1 h.2.1, by
      change O.indicator (fun _ => (1 : ℂ)) 0 = 0
      exact Set.indicator_of_notMem h.2.2 _⟩ else 0

theorem indS_apply {O : Set (Fin (n + 1) → K)} (hc : IsCompact O) (ho : IsOpen O)
    (h0 : (0 : Fin (n + 1) → K) ∉ O) (x : Fin (n + 1) → K) :
    (indS O).1 x = O.indicator (fun _ => (1 : ℂ)) x := by
  unfold indS
  split_ifs with h
  · rfl
  · exact absurd ⟨hc, ho, h0⟩ h

/-- Compactness, openness and avoidance of zero for a row set. -/
def RowCond (O : Set (Fin (n + 1) → K)) : Prop :=
  IsCompact O ∧ IsOpen O ∧ (0 : Fin (n + 1) → K) ∉ O

theorem rowCond_orbitSet {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hHo : IsOpen (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (hHc : IsCompact (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (g : Langlands.GeneralLinear (n + 1) K) : RowCond (orbitSet H g) :=
  ⟨isCompact_orbitSet hHc g, isOpen_orbitSet hHo g, zero_notMem_orbitSet H g⟩

omit [T2Space K] in
theorem rowCond_preimage {O : Set (Fin (n + 1) → K)} (hO : RowCond O)
    (k : Langlands.GeneralLinear (n + 1) K) :
    RowCond ((fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) ⁻¹' O) := by
  refine ⟨(rowHomeomorph k).isCompact_preimage.mpr hO.1,
    hO.2.1.preimage (rowHomeomorph k).continuous, ?_⟩
  change ¬ ((0 : Fin (n + 1) → K) ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) ∈ O
  rw [Matrix.zero_vecMul]
  exact hO.2.2

/-- Right translation of an indicator is the indicator of the preimage. -/
theorem splusRep_indS {O : Set (Fin (n + 1) → K)} (hO : RowCond O)
    (k : Langlands.GeneralLinear (n + 1) K) :
    splusRep K n k (indS O) =
      indS ((fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) ⁻¹' O) := by
  have hO' := rowCond_preimage hO k
  apply splus_ext
  intro x
  rw [splusRep_apply, indS_apply hO.1 hO.2.1 hO.2.2, indS_apply hO'.1 hO'.2.1 hO'.2.2]
  rfl

/-- Translating the orbit indicator of `g` by `k` gives the orbit indicator of the
conjugate subgroup at `g * k⁻¹`. -/
theorem splusRep_indS_orbitSet {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hHo : IsOpen (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (hHc : IsCompact (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (g k : Langlands.GeneralLinear (n + 1) K) :
    splusRep K n k (indS (orbitSet H g)) = indS (orbitSet (conj k H) (g * k⁻¹)) := by
  rw [splusRep_indS (rowCond_orbitSet hHo hHc g), preimage_vecMul_orbitSet]

end Indicator

section Mass

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
  {n : ℕ}
  [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)]
  (μ : Measure (Fin (n + 1) → K)) [μ.IsAddHaarMeasure]

omit [IsTopologicalDivisionRing K] [T2Space K] in
theorem integrable_schwartz (Ψ : SchwartzBruhat (Fin (n + 1) → K)) :
    Integrable (fun x => Ψ x) μ :=
  Ψ.continuous.integrable_of_hasCompactSupport Ψ.hasCompactSupport

/-- The Haar integral of a row test function. -/
def mass : SchwartzBruhat (Fin (n + 1) → K) →ₗ[ℂ] ℂ where
  toFun Ψ := ∫ x, Ψ x ∂μ
  map_add' Ψ Ψ' := integral_add (integrable_schwartz μ Ψ) (integrable_schwartz μ Ψ')
  map_smul' c Ψ := integral_const_mul c fun x => Ψ x

omit [IsTopologicalDivisionRing K] [T2Space K] in
theorem mass_apply (Ψ : SchwartzBruhat (Fin (n + 1) → K)) :
    mass μ Ψ = ∫ x, Ψ x ∂μ := rfl

omit [T2Space K] in
/-- Right translation scales the Haar integral by the inverse determinant factor. -/
theorem mass_rowTranslate (χ : K →*₀ ℝ≥0)
    (hscale : ∀ k : Langlands.GeneralLinear (n + 1) K,
      μ.map (fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) =
        (χ (Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)))⁻¹ • μ)
    (k : Langlands.GeneralLinear (n + 1) K) (Ψ : SchwartzBruhat (Fin (n + 1) → K)) :
    mass μ (rowTranslate k Ψ) =
      (((χ (Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) : ℝ) : ℂ))⁻¹ * mass μ Ψ := by
  have h := integral_map_equiv (μ := μ) (rowHomeomorph k).toMeasurableEquiv (fun x => Ψ x)
  have hmap : Measure.map (rowHomeomorph k).toMeasurableEquiv μ =
      μ.map (fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) := rfl
  rw [hmap, hscale, integral_smul_nnreal_measure] at h
  rw [mass_apply, mass_apply]
  change ∫ x, Ψ (x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) ∂μ = _
  rw [show (fun x => Ψ (x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K))) =
    fun x => Ψ ((rowHomeomorph k).toMeasurableEquiv x) from rfl, ← h,
    NNReal.smul_def, Complex.real_smul, NNReal.coe_inv, Complex.ofReal_inv]

omit [IsTopologicalDivisionRing K] [T2Space K] in
theorem mass_indicator {O : Set (Fin (n + 1) → K)} (ho : IsOpen O)
    (Ψ : SchwartzBruhat (Fin (n + 1) → K))
    (hΨ : ∀ x, Ψ x = O.indicator (fun _ => (1 : ℂ)) x) :
    mass μ Ψ = ((μ.real O : ℝ) : ℂ) := by
  rw [mass_apply, show (fun x => Ψ x) = O.indicator (fun _ => (1 : ℂ)) from funext hΨ,
    integral_indicator_const _ ho.measurableSet, Complex.real_smul, mul_one]

omit [IsTopologicalDivisionRing K] [T2Space K] in
theorem mass_indicator_ne_zero {O : Set (Fin (n + 1) → K)} (hc : IsCompact O) (ho : IsOpen O)
    (hne : O.Nonempty) (Ψ : SchwartzBruhat (Fin (n + 1) → K))
    (hΨ : ∀ x, Ψ x = O.indicator (fun _ => (1 : ℂ)) x) : mass μ Ψ ≠ 0 := by
  rw [mass_indicator μ ho Ψ hΨ, Complex.ofReal_ne_zero, measureReal_def,
    ENNReal.toReal_ne_zero]
  exact ⟨ho.measure_ne_zero μ hne, hc.measure_lt_top.ne⟩

theorem mass_indS_orbitSet_ne_zero {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hHo : IsOpen (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (hHc : IsCompact (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (g : Langlands.GeneralLinear (n + 1) K) : mass μ (indS (orbitSet H g)).1 ≠ 0 := by
  have hO := rowCond_orbitSet hHo hHc g
  exact mass_indicator_ne_zero μ hO.1 hO.2.1 ⟨_, lastRow_mem_orbitSet H g⟩ _
    (indS_apply hO.1 hO.2.1 hO.2.2)

end Mass

section Decomposition

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
  {n : ℕ}

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem disjoint_orbitSet {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    {g g' : Langlands.GeneralLinear (n + 1) K} (hne : orbitSet H g ≠ orbitSet H g') :
    Disjoint (orbitSet H g) (orbitSet H g') :=
  Set.disjoint_left.mpr fun _ hx hx' => hne (orbitSet_eq_of_mem_inter H hx hx')

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
/-- A finite family of orbits is pairwise disjoint. -/
theorem pairwiseDisjoint_orbits {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (𝒪 : Finset (Set (Fin (n + 1) → K)))
    (h𝒪 : ∀ O ∈ 𝒪, ∃ g : Langlands.GeneralLinear (n + 1) K, O = orbitSet H g) :
    (𝒪 : Set (Set (Fin (n + 1) → K))).PairwiseDisjoint id := by
  intro O hO O' hO' hne
  obtain ⟨g, rfl⟩ := h𝒪 O hO
  obtain ⟨g', rfl⟩ := h𝒪 O' hO'
  exact disjoint_orbitSet hne

/-- A finite family of orbit indicators sums to the indicator of the union. -/
theorem sum_indS_orbits {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hHo : IsOpen (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (hHc : IsCompact (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (𝒪 : Finset (Set (Fin (n + 1) → K)))
    (h𝒪 : ∀ O ∈ 𝒪, ∃ g : Langlands.GeneralLinear (n + 1) K, O = orbitSet H g)
    (x : Fin (n + 1) → K) :
    ∑ O ∈ 𝒪, (indS O).1 x = (⋃ O ∈ 𝒪, O).indicator (fun _ => (1 : ℂ)) x := by
  have hb := Finset.indicator_biUnion_apply 𝒪 id (pairwiseDisjoint_orbits 𝒪 h𝒪)
    (f := fun _ => (1 : ℂ)) x
  simp only [id] at hb
  rw [hb]
  refine Finset.sum_congr rfl fun O hO => ?_
  obtain ⟨g, rfl⟩ := h𝒪 O hO
  have hc := rowCond_orbitSet hHo hHc g
  exact indS_apply hc.1 hc.2.1 hc.2.2 x

/-- The relative core `{c | h⁻¹ c h ∈ H ∩ N for all h ∈ H}`. -/
def core (H N : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
    Subgroup (Langlands.GeneralLinear (n + 1) K) where
  carrier := {c | ∀ h ∈ H, h⁻¹ * c * h ∈ H ∧ h⁻¹ * c * h ∈ N}
  one_mem' := fun h _ => by
    rw [mul_one, inv_mul_cancel]
    exact ⟨H.one_mem, N.one_mem⟩
  mul_mem' := fun {a b} ha hb h hh => by
    have e : h⁻¹ * (a * b) * h = (h⁻¹ * a * h) * (h⁻¹ * b * h) := by group
    rw [e]
    exact ⟨H.mul_mem (ha h hh).1 (hb h hh).1, N.mul_mem (ha h hh).2 (hb h hh).2⟩
  inv_mem' := fun {a} ha h hh => by
    have e : h⁻¹ * a⁻¹ * h = (h⁻¹ * a * h)⁻¹ := by group
    rw [e]
    exact ⟨H.inv_mem (ha h hh).1, N.inv_mem (ha h hh).2⟩

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem mem_core {H N : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    {c : Langlands.GeneralLinear (n + 1) K} :
    c ∈ core H N ↔ ∀ h ∈ H, h⁻¹ * c * h ∈ H ∧ h⁻¹ * c * h ∈ N := Iff.rfl

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem core_le_left {H N : Subgroup (Langlands.GeneralLinear (n + 1) K)} : core H N ≤ H := by
  intro c hc
  have := (mem_core.mp hc 1 H.one_mem).1
  rwa [inv_one, one_mul, mul_one] at this

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem core_le_right {H N : Subgroup (Langlands.GeneralLinear (n + 1) K)} : core H N ≤ N := by
  intro c hc
  have := (mem_core.mp hc 1 H.one_mem).2
  rwa [inv_one, one_mul, mul_one] at this

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem conj_core {H N : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    {k : Langlands.GeneralLinear (n + 1) K} (hk : k ∈ H) : conj k (core H N) = core H N := by
  ext x
  rw [mem_conj, mem_core, mem_core]
  constructor
  · intro hx h hh
    have e : h⁻¹ * x * h = (k⁻¹ * h)⁻¹ * (k⁻¹ * x * k) * (k⁻¹ * h) := by group
    rw [e]
    exact hx _ (H.mul_mem (H.inv_mem hk) hh)
  · intro hx h hh
    have e : h⁻¹ * (k⁻¹ * x * k) * h = (k * h)⁻¹ * x * (k * h) := by group
    rw [e]
    exact hx _ (H.mul_mem hk hh)

omit [T2Space K] in
/-- The relative core of a compact open subgroup with respect to an open subgroup is open. -/
theorem isOpen_core {H N : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hHo : IsOpen (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (hHc : IsCompact (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (hNo : IsOpen (N : Set (Langlands.GeneralLinear (n + 1) K))) :
    IsOpen (core H N : Set (Langlands.GeneralLinear (n + 1) K)) := by
  have hf : Continuous fun q : Langlands.GeneralLinear (n + 1) K ×
      Langlands.GeneralLinear (n + 1) K => q.1⁻¹ * q.2 * q.1 :=
    (continuous_fst.inv.mul continuous_snd).mul continuous_fst
  have hsub : (H : Set (Langlands.GeneralLinear (n + 1) K)) ×ˢ
      ({1} : Set (Langlands.GeneralLinear (n + 1) K)) ⊆
      (fun q : Langlands.GeneralLinear (n + 1) K × Langlands.GeneralLinear (n + 1) K =>
        q.1⁻¹ * q.2 * q.1) ⁻¹' ((H : Set (Langlands.GeneralLinear (n + 1) K)) ∩ N) := by
    rintro ⟨h, c⟩ ⟨-, hc⟩
    rw [Set.mem_singleton_iff] at hc
    rw [Set.mem_preimage, hc, mul_one, inv_mul_cancel]
    exact ⟨H.one_mem, N.one_mem⟩
  obtain ⟨u, v, -, hv, hHu, h1v, huv⟩ := generalized_tube_lemma hHc isCompact_singleton
    ((hHo.inter hNo).preimage hf) hsub
  apply Subgroup.isOpen_of_mem_nhds (core H N) (g := 1)
  refine Filter.mem_of_superset (hv.mem_nhds (h1v (Set.mem_singleton 1))) fun c hc => ?_
  rw [SetLike.mem_coe, mem_core]
  intro h hh
  have hm := huv (Set.mk_mem_prod (hHu hh) hc)
  rw [Set.mem_preimage, Set.mem_inter_iff] at hm
  exact hm

omit [T2Space K] in
theorem isCompact_of_le {H C : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hHc : IsCompact (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (hCo : IsOpen (C : Set (Langlands.GeneralLinear (n + 1) K))) (hCH : C ≤ H) :
    IsCompact (C : Set (Langlands.GeneralLinear (n + 1) K)) :=
  hHc.of_isClosed_subset (C.isClosed_of_isOpen hCo) hCH

/-- The indicator of the `H`-orbit of the base row is a finite sum of `C`-orbit
indicators, uniformly for all linear functionals constant on these orbits. -/
theorem exists_card_sum {H C : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hHo : IsOpen (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (hHc : IsCompact (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (hCo : IsOpen (C : Set (Langlands.GeneralLinear (n + 1) K))) (hCH : C ≤ H) :
    ∃ N : ℕ, ∀ l : Splus K n →ₗ[ℂ] ℂ,
      (∀ h ∈ H, l (indS (orbitSet C h)) = l (indS (orbitSet C 1))) →
        l (indS (orbitSet H 1)) = N * l (indS (orbitSet C 1)) := by
  classical
  have hCc := isCompact_of_le hHc hCo hCH
  obtain ⟨t, ht⟩ := (isCompact_orbitSet hHc 1).elim_finite_subcover
    (fun h : H => orbitSet C h.val) (fun h => isOpen_orbitSet hCo h.val) (by
      rintro x ⟨h, hh, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨h, hh⟩, by
        show lastRow (1 * h) ∈ orbitSet C h
        rw [one_mul]
        exact lastRow_mem_orbitSet C h⟩)
  let 𝒪 : Finset (Set (Fin (n + 1) → K)) := t.image fun h : H => orbitSet C h.val
  have h𝒪 : ∀ O ∈ 𝒪, ∃ h ∈ H, O = orbitSet C h := by
    intro O hO
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hO
    exact ⟨h.val, h.prop, rfl⟩
  have hunion : (⋃ O ∈ 𝒪, O) = orbitSet H 1 := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨O, hO, hx⟩
      obtain ⟨h, hh, rfl⟩ := h𝒪 O hO
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨h * c, H.mul_mem hh (hCH hc), by simp only [one_mul]⟩
    · intro hx
      obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht hx)
      exact ⟨_, Finset.mem_image_of_mem _ hi, hx⟩
  have hsum : indS (orbitSet H 1) = ∑ O ∈ 𝒪, indS O := by
    apply splus_ext
    intro x
    have hc := rowCond_orbitSet hHo hHc 1
    rw [splus_sum_apply, sum_indS_orbits hCo hCc 𝒪
      (fun O hO => (h𝒪 O hO).imp fun _ h => h.2) x, hunion,
      indS_apply hc.1 hc.2.1 hc.2.2]
  refine ⟨𝒪.card, fun l hl => ?_⟩
  rw [hsum, map_sum, Finset.sum_congr rfl (g := fun _ => l (indS (orbitSet C 1))),
    Finset.sum_const, nsmul_eq_mul]
  intro O hO
  obtain ⟨h, hh, rfl⟩ := h𝒪 O hO
  exact hl h hh

/-- A test function vanishing at zero and right invariant under a compact open subgroup is a
finite linear combination of orbit indicators. -/
theorem exists_eq_sum_indS {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hHo : IsOpen (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (hHc : IsCompact (H : Set (Langlands.GeneralLinear (n + 1) K)))
    (Φ : Splus K n)
    (hΦ : ∀ h ∈ H, ∀ x, Φ.1 (x ᵥ* (h : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) = Φ.1 x) :
    ∃ 𝒪 : Finset (Set (Fin (n + 1) → K)),
      (∀ O ∈ 𝒪, ∃ g : Langlands.GeneralLinear (n + 1) K, O = orbitSet H g) ∧
      ∃ c : Set (Fin (n + 1) → K) → ℂ, Φ = ∑ O ∈ 𝒪, c O • indS O := by
  classical
  have hconst : ∀ (g : Langlands.GeneralLinear (n + 1) K) y, y ∈ orbitSet H g →
      Φ.1 y = Φ.1 (lastRow g) := by
    rintro g _ ⟨h, hh, rfl⟩
    exact (congrArg Φ.1 (lastRow_mul_eq_vecMul g h)).trans (hΦ h hh _)
  have hsupp := Hecke.TestFunction.isCompact_support Φ.1
  have h0 : ∀ x ∈ Function.support Φ.1, x ≠ 0 := by
    rintro x hx rfl
    exact hx Φ.2
  obtain ⟨t, ht⟩ := hsupp.elim_finite_subcover
    (fun x : Function.support Φ.1 => orbitSet H (lift x.val))
    (fun x => isOpen_orbitSet hHo _) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by
      have hm := lastRow_mem_orbitSet H (lift x)
      rwa [lastRow_lift x (h0 x hx)] at hm⟩)
  let 𝒪 : Finset (Set (Fin (n + 1) → K)) :=
    t.image fun x : Function.support Φ.1 => orbitSet H (lift x.val)
  have h𝒪 : ∀ O ∈ 𝒪, ∃ g : Langlands.GeneralLinear (n + 1) K, O = orbitSet H g := by
    intro O hO
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hO
    exact ⟨_, rfl⟩
  let c : Set (Fin (n + 1) → K) → ℂ := fun O => Φ.1 (Classical.epsilon fun y => y ∈ O)
  have hc : ∀ O ∈ 𝒪, ∀ y ∈ O, c O = Φ.1 y := by
    intro O hO y hy
    obtain ⟨g, rfl⟩ := h𝒪 O hO
    exact (hconst g _ (Classical.epsilon_spec ⟨y, hy⟩)).trans (hconst g y hy).symm
  refine ⟨𝒪, h𝒪, c, splus_ext fun y => ?_⟩
  rw [splus_sum_apply]
  have hterm : ∀ O ∈ 𝒪, (c O • indS O).1 y = Φ.1 y * (indS O).1 y := by
    intro O hO
    obtain ⟨g, rfl⟩ := h𝒪 O hO
    have hcd := rowCond_orbitSet hHo hHc g
    change c (orbitSet H g) * (indS (orbitSet H g)).1 y = _
    rw [indS_apply hcd.1 hcd.2.1 hcd.2.2]
    by_cases hy : y ∈ orbitSet H g
    · rw [hc _ hO y hy]
    · simp [Set.indicator_of_notMem hy]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_indS_orbits hHo hHc 𝒪 h𝒪 y]
  by_cases hy : y ∈ Function.support Φ.1
  · have hy' : y ∈ ⋃ O ∈ 𝒪, O := by
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
      exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_image_of_mem _ hi, hyi⟩
    rw [Set.indicator_of_mem hy', mul_one]
  · rw [Function.notMem_support.mp hy, zero_mul]

end Decomposition

section Determinant

variable {K : Type uF} [Field K] {n : ℕ} (abv : AbsoluteValue K ℝ)

theorem det_ne_zero (g : Langlands.GeneralLinear (n + 1) K) :
    Matrix.det (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero

theorem abv_det_ne_zero (g : Langlands.GeneralLinear (n + 1) K) :
    abv (Matrix.det (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) ≠ 0 :=
  (AbsoluteValue.ne_zero_iff abv).mpr (det_ne_zero g)

theorem abv_det_inv_mul (k : Langlands.GeneralLinear (n + 1) K) :
    abv (Matrix.det ((k⁻¹ : Langlands.GeneralLinear (n + 1) K) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) K)) *
      abv (Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) = 1 := by
  rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.det_one, map_one]

theorem abv_det_conj (k h : Langlands.GeneralLinear (n + 1) K) :
    abv (Matrix.det ((k⁻¹ * h * k : Langlands.GeneralLinear (n + 1) K) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) K)) =
      abv (Matrix.det (h : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul]
  have := abv_det_inv_mul abv k
  calc _ = abv (Matrix.det (h : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) *
        (abv (Matrix.det ((k⁻¹ : Langlands.GeneralLinear (n + 1) K) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K)) *
          abv (Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K))) := by ring
    _ = _ := by rw [this, mul_one]

/-- Matrices whose determinant has absolute value one. -/
def detOne : Subgroup (Langlands.GeneralLinear (n + 1) K) where
  carrier := {g | abv (Matrix.det (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) = 1}
  one_mem' := by
    change abv (Matrix.det (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) = 1
    rw [Matrix.det_one, map_one]
  mul_mem' := fun {a b} ha hb => by
    change abv (Matrix.det ((a * b : Langlands.GeneralLinear (n + 1) K) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) K)) = 1
    rw [Units.val_mul, Matrix.det_mul, map_mul, ha, hb, mul_one]
  inv_mem' := fun {a} ha => by
    have := abv_det_inv_mul abv a
    change abv (Matrix.det (a : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) = 1 at ha
    rwa [ha, mul_one] at this

theorem mem_detOne {g : Langlands.GeneralLinear (n + 1) K} :
    g ∈ detOne abv ↔ abv (Matrix.det (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) = 1 := Iff.rfl

/-- `|det g|^t` is multiplicative in `g`. -/
theorem determinantWeight_mul' (g h : Langlands.GeneralLinear (n + 1) K) (t : ℂ) :
    determinantWeight abv (g * h) t = determinantWeight abv g t * determinantWeight abv h t := by
  simp only [determinantWeight, Units.val_mul, Matrix.det_mul, map_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (abv.nonneg _) (abv.nonneg _) t

theorem determinantWeight_add (g : Langlands.GeneralLinear (n + 1) K) (t t' : ℂ) :
    determinantWeight abv g (t + t') = determinantWeight abv g t * determinantWeight abv g t' :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (abv_det_ne_zero abv g))

theorem determinantWeight_one_sub (g : Langlands.GeneralLinear (n + 1) K) (s : ℂ) :
    determinantWeight abv g (1 - s) =
      (abv (Matrix.det (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) : ℂ) *
        determinantWeight abv g (-s) := by
  rw [sub_eq_add_neg, determinantWeight_add, determinantWeight, determinantWeight,
    Complex.cpow_one]

theorem determinantWeight_cancel (g : Langlands.GeneralLinear (n + 1) K) (s : ℂ) :
    determinantWeight abv g (1 - s) * determinantWeight abv g (s - 1) = 1 := by
  rw [← determinantWeight_add, show 1 - s + (s - 1) = 0 by ring, determinantWeight,
    Complex.cpow_zero]

theorem determinantWeight_eq_one {g : Langlands.GeneralLinear (n + 1) K}
    (hg : abv (Matrix.det (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) = 1) (t : ℂ) :
    determinantWeight abv g t = 1 := by
  rw [determinantWeight, hg, Complex.ofReal_one, Complex.one_cpow]

end Determinant

section Backward

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
  {n : ℕ} (abv : AbsoluteValue K ℝ)
  {V : Type*} {W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) W)

/-- A compact open subgroup fixing `v` and `w` on which `|det|` is one. -/
def Good (v : V) (w : W) (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) : Prop :=
  IsOpen (H : Set (Langlands.GeneralLinear (n + 1) K)) ∧
    IsCompact (H : Set (Langlands.GeneralLinear (n + 1) K)) ∧
    ∀ h ∈ H, ρ h v = v ∧ σ h w = w ∧
      abv (Matrix.det (h : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) = 1

variable {abv ρ σ}

omit [T2Space K] in
theorem Good.of_le {v : V} {w : W} {H H' : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hH : Good abv ρ σ v w H) (hle : H' ≤ H)
    (ho : IsOpen (H' : Set (Langlands.GeneralLinear (n + 1) K))) : Good abv ρ σ v w H' :=
  ⟨ho, isCompact_of_le hH.2.1 ho hle, fun h hh => hH.2.2 h (hle hh)⟩

omit [IsTopologicalDivisionRing K] [T2Space K] in
theorem Good.add_left {v v' : V} {w : W} {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (h₁ : Good abv ρ σ v w H) (h₂ : Good abv ρ σ v' w H) : Good abv ρ σ (v + v') w H :=
  ⟨h₁.1, h₁.2.1, fun h hh => ⟨by rw [map_add, (h₁.2.2 h hh).1, (h₂.2.2 h hh).1],
    (h₁.2.2 h hh).2⟩⟩

omit [IsTopologicalDivisionRing K] [T2Space K] in
theorem Good.smul_left {v : V} {w : W} {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (c : ℂ) (h₁ : Good abv ρ σ v w H) : Good abv ρ σ (c • v) w H :=
  ⟨h₁.1, h₁.2.1, fun h hh => ⟨by rw [map_smul, (h₁.2.2 h hh).1], (h₁.2.2 h hh).2⟩⟩

omit [IsTopologicalDivisionRing K] [T2Space K] in
theorem Good.add_right {v : V} {w w' : W} {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (h₁ : Good abv ρ σ v w H) (h₂ : Good abv ρ σ v w' H) : Good abv ρ σ v (w + w') H :=
  ⟨h₁.1, h₁.2.1, fun h hh => ⟨(h₁.2.2 h hh).1,
    by rw [map_add, (h₁.2.2 h hh).2.1, (h₂.2.2 h hh).2.1], (h₁.2.2 h hh).2.2⟩⟩

omit [IsTopologicalDivisionRing K] [T2Space K] in
theorem Good.smul_right {v : V} {w : W} {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (c : ℂ) (h₁ : Good abv ρ σ v w H) : Good abv ρ σ v (c • w) H :=
  ⟨h₁.1, h₁.2.1, fun h hh => ⟨(h₁.2.2 h hh).1, by rw [map_smul, (h₁.2.2 h hh).2.1],
    (h₁.2.2 h hh).2.2⟩⟩

omit [T2Space K] in
/-- Conjugating a good subgroup by `k` gives a good subgroup for the translated vectors. -/
theorem Good.conj {v : V} {w : W} {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hH : Good abv ρ σ v w H) (k : Langlands.GeneralLinear (n + 1) K) :
    Good abv ρ σ (ρ k v) (σ k w) (EqualRankFrobenius.conj k H) := by
  refine ⟨isOpen_conj hH.1 k, isCompact_conj hH.2.1 k, fun h hh => ?_⟩
  rw [mem_conj] at hh
  obtain ⟨h1, h2, h3⟩ := hH.2.2 _ hh
  have e : h * k = k * (k⁻¹ * h * k) := by group
  refine ⟨?_, ?_, ?_⟩
  · rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h1]
  · rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h2]
  · rw [← abv_det_conj abv k h]
    exact h3

omit [T2Space K] in
/-- Smoothness provides good subgroups inside any open subgroup. -/
theorem exists_good (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (hdet : IsOpen {g : Langlands.GeneralLinear (n + 1) K |
      abv (Matrix.det (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) = 1})
    (hK₀ : ∃ K₀ : Subgroup (Langlands.GeneralLinear (n + 1) K),
      IsOpen (K₀ : Set (Langlands.GeneralLinear (n + 1) K)) ∧
        IsCompact (K₀ : Set (Langlands.GeneralLinear (n + 1) K)))
    (v : V) (w : W) : ∃ H, Good abv ρ σ v w H := by
  obtain ⟨Kv, hKv⟩ := hρ v
  obtain ⟨Kw, hKw⟩ := hσ w
  obtain ⟨K₀, hK₀o, hK₀c⟩ := hK₀
  let H : Subgroup (Langlands.GeneralLinear (n + 1) K) :=
    ((Kv.toSubgroup ⊓ Kw.toSubgroup) ⊓ detOne abv) ⊓ K₀
  have hHo : IsOpen (H : Set (Langlands.GeneralLinear (n + 1) K)) :=
    ((Kv.isOpen.inter Kw.isOpen).inter hdet).inter hK₀o
  refine ⟨H, hHo, isCompact_of_le hK₀c hHo inf_le_right, fun h hh => ?_⟩
  obtain ⟨hh, -⟩ := Subgroup.mem_inf.mp hh
  obtain ⟨hh, h3⟩ := Subgroup.mem_inf.mp hh
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hh
  exact ⟨(Representation.mem_invariants _ v).mp hKv ⟨h, h1⟩,
    (Representation.mem_invariants _ w).mp hKw ⟨h, h2⟩, h3⟩

end Backward


section Value

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
  {n : ℕ} {abv : AbsoluteValue K ℝ}
  {V : Type*} {W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) W}
  [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)]
  (μ : Measure (Fin (n + 1) → K)) [μ.IsAddHaarMeasure]
  {χ : K →*₀ ℝ≥0} (hχ : ∀ a, (χ a : ℝ) = abv a)
  (hscale : ∀ k : Langlands.GeneralLinear (n + 1) K,
      μ.map (fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) =
        (χ (Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)))⁻¹ • μ)
  {s : ℂ}

/-- The normalized value of a trilinear form at the orbit indicator of a subgroup. -/
def valueAt (B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ) (v : V) (w : W)
    (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) : ℂ :=
  B v w (indS (orbitSet H 1)) / mass μ (indS (orbitSet H 1)).1

include hχ hscale in
omit [T2Space K] in
theorem mass_splusRep (k : Langlands.GeneralLinear (n + 1) K) (ψ : Splus K n) :
    mass μ (splusRep K n k ψ).1 =
      ((abv (Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) : ℂ))⁻¹ * mass μ ψ.1 := by
  rw [show (splusRep K n k ψ).1 = rowTranslate k ψ.1 from rfl,
    mass_rowTranslate μ χ hscale, hχ]

omit [T2Space K] [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)] in
theorem form_splusRep_of_good {B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ}
    (hB : Invariant (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s)) B)
    {v : V} {w : W} {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hH : Good abv ρ σ v w H) {h : Langlands.GeneralLinear (n + 1) K} (hh : h ∈ H)
    (ψ : Splus K n) : B v w (splusRep K n h ψ) = B v w ψ := by
  obtain ⟨h1, h2, h3⟩ := hH.2.2 h hh
  have := hB h v w ψ
  rw [h1, h2] at this
  rw [this]
  change determinantWeight abv h (-s) * _ = _
  rw [determinantWeight_eq_one abv h3, one_mul]

include hχ hscale in
/-- Passing to a normal open subgroup of a good subgroup does not change the value. -/
theorem valueAt_eq_of_le {B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ}
    (hB : Invariant (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s)) B)
    {v : V} {w : W} {H C : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hH : Good abv ρ σ v w H) (hCo : IsOpen (C : Set (Langlands.GeneralLinear (n + 1) K)))
    (hCH : C ≤ H) (hnorm : ∀ h ∈ H, conj h C = C) :
    valueAt μ B v w H = valueAt μ B v w C := by
  obtain ⟨N, hN⟩ := exists_card_sum hH.1 hH.2.1 hCo hCH
  have hCc := isCompact_of_le hH.2.1 hCo hCH
  have htrans : ∀ h ∈ H, indS (orbitSet C h) = splusRep K n h⁻¹ (indS (orbitSet C 1)) := by
    intro h hh
    rw [splusRep_indS_orbitSet hCo hCc, hnorm _ (H.inv_mem hh), one_mul, inv_inv]
  have h1 := hN (B v w) fun h hh => by
    rw [htrans h hh, form_splusRep_of_good hB hH (H.inv_mem hh)]
  have h2 := hN ((mass μ).comp (Submodule.subtype _)) fun h hh => by
    change mass μ (indS (orbitSet C h)).1 = mass μ (indS (orbitSet C 1)).1
    rw [htrans h hh, mass_splusRep μ hχ hscale, (hH.2.2 _ (H.inv_mem hh)).2.2,
      Complex.ofReal_one, inv_one, one_mul]
  change mass μ (indS (orbitSet H 1)).1 = N * mass μ (indS (orbitSet C 1)).1 at h2
  have hm := mass_indS_orbitSet_ne_zero μ hH.1 hH.2.1 1
  have hN0 : (N : ℂ) ≠ 0 := by
    intro h0
    apply hm
    rw [h2, h0, zero_mul]
  unfold valueAt
  rw [h1, h2, mul_div_mul_left _ _ hN0]

include hχ hscale in
/-- The normalized value does not depend on the good subgroup. -/
theorem valueAt_eq {B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ}
    (hB : Invariant (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s)) B)
    {v : V} {w : W} {H₁ H₂ : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (h₁ : Good abv ρ σ v w H₁) (h₂ : Good abv ρ σ v w H₂) :
    valueAt μ B v w H₁ = valueAt μ B v w H₂ := by
  have hCo := isOpen_core h₁.1 h₁.2.1 h₂.1
  have hC'o := isOpen_core h₂.1 h₂.2.1 hCo
  have hC : Good abv ρ σ v w (core H₁ H₂) := h₁.of_le core_le_left hCo
  rw [valueAt_eq_of_le μ hχ hscale hB h₁ hCo core_le_left (fun _ hh => conj_core hh),
    valueAt_eq_of_le μ hχ hscale hB hC hC'o core_le_right
      (fun _ hh => conj_core (core_le_right hh)),
    ← valueAt_eq_of_le μ hχ hscale hB h₂ hC'o core_le_left (fun _ hh => conj_core hh)]

theorem valueAt_add_left (B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ) (v v' : V) (w : W)
    (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
    valueAt μ B (v + v') w H = valueAt μ B v w H + valueAt μ B v' w H := by
  simp only [valueAt, map_add, LinearMap.add_apply, add_div]

theorem valueAt_smul_left (B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ) (c : ℂ) (v : V) (w : W)
    (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
    valueAt μ B (c • v) w H = c * valueAt μ B v w H := by
  simp only [valueAt, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

theorem valueAt_add_right (B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ) (v : V) (w w' : W)
    (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
    valueAt μ B v (w + w') H = valueAt μ B v w H + valueAt μ B v w' H := by
  simp only [valueAt, map_add, LinearMap.add_apply, add_div]

theorem valueAt_smul_right (B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ) (c : ℂ) (v : V) (w : W)
    (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
    valueAt μ B v (c • w) H = c * valueAt μ B v w H := by
  simp only [valueAt, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

theorem valueAt_add_form (B B' : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ) (v : V) (w : W)
    (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
    valueAt μ (B + B') v w H = valueAt μ B v w H + valueAt μ B' v w H := by
  simp only [valueAt, LinearMap.add_apply, add_div]

theorem valueAt_smul_form (B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ) (c : ℂ) (v : V) (w : W)
    (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
    valueAt μ (c • B) v w H = c * valueAt μ B v w H := by
  simp only [valueAt, LinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

theorem valueAt_sub_form (B B' : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ) (v : V) (w : W)
    (H : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
    valueAt μ (B - B') v w H = valueAt μ B v w H - valueAt μ B' v w H := by
  simp only [valueAt, LinearMap.sub_apply, sub_div]

end Value

section Choice

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
  {n : ℕ} (abv : AbsoluteValue K ℝ)
  {V : Type*} {W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) W)

/-- A chosen good subgroup for `v` and `w`, when one exists. -/
def goodChoice (v : V) (w : W) : Subgroup (Langlands.GeneralLinear (n + 1) K) := by
  classical
  exact if h : ∃ H, Good abv ρ σ v w H then h.choose else ⊤

variable {abv ρ σ}

omit [IsTopologicalDivisionRing K] [T2Space K] in
theorem good_goodChoice {v : V} {w : W} (h : ∃ H, Good abv ρ σ v w H) :
    Good abv ρ σ v w (goodChoice abv ρ σ v w) := by
  unfold goodChoice
  split_ifs
  exact h.choose_spec

end Choice

section BackwardMap

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
  {n : ℕ} (abv : AbsoluteValue K ℝ)
  {V : Type*} {W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) W)
  [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)]
  (μ : Measure (Fin (n + 1) → K)) [μ.IsAddHaarMeasure]
  {χ : K →*₀ ℝ≥0} (hχ : ∀ a, (χ a : ℝ) = abv a)
  (hscale : ∀ k : Langlands.GeneralLinear (n + 1) K,
      μ.map (fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) =
        (χ (Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)))⁻¹ • μ)
  (s : ℂ)

/-- The space of invariant trilinear forms on test functions vanishing at zero. -/
abbrev SourceSpace :=
  invariantForms (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s))

/-- The space of mirabolic covariant bilinear forms with weight `1 - s`. -/
abbrev TargetSpace :=
  InvariantBilinear.forms (ρ.comp (mirabolic n K).subtype) (σ.comp (mirabolic n K).subtype)
    (fun g => determinantWeight abv g.val (1 - s))

/-- The backward value of a trilinear form, at the chosen good subgroup. -/
def bwdFun (B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ) (v : V) (w : W) : ℂ :=
  valueAt μ B v w (goodChoice abv ρ σ v w)

variable {abv ρ σ s}

include hχ hscale in
theorem bwdFun_eq {B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ}
    (hB : Invariant (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s)) B)
    {v : V} {w : W} {H : Subgroup (Langlands.GeneralLinear (n + 1) K)}
    (hH : Good abv ρ σ v w H) : bwdFun abv ρ σ μ B v w = valueAt μ B v w H :=
  valueAt_eq μ hχ hscale hB (good_goodChoice ⟨H, hH⟩) hH

variable (hgood : ∀ (v : V) (w : W), ∃ H, Good abv ρ σ v w H)

include hχ hscale hgood in
/-- Mirabolic covariance of the backward value, with the modular shift `1 - s`. -/
theorem bwdFun_mirabolic {B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ}
    (hB : Invariant (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s)) B)
    {p : Langlands.GeneralLinear (n + 1) K} (hp : p ∈ mirabolic n K) (v : V) (w : W) :
    bwdFun abv ρ σ μ B (ρ p v) (σ p w) =
      determinantWeight abv p (1 - s) * bwdFun abv ρ σ μ B v w := by
  obtain ⟨H, hH⟩ := hgood v w
  rw [bwdFun_eq μ hχ hscale hB (hH.conj p), bwdFun_eq μ hχ hscale hB hH]
  unfold valueAt
  have hind : indS (orbitSet (conj p H) 1) = splusRep K n p (indS (orbitSet H 1)) := by
    rw [splusRep_indS_orbitSet hH.1 hH.2.1, one_mul, orbitSet_conj_mirabolic hp]
  have hm := mass_indS_orbitSet_ne_zero μ hH.1 hH.2.1 1
  have hx : (abv (Matrix.det (p : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abv_det_ne_zero abv p)
  have hBp := hB p v w (indS (orbitSet H 1))
  change _ = determinantWeight abv p (-s) * _ at hBp
  rw [hind, hBp, mass_splusRep μ hχ hscale, determinantWeight_one_sub]
  field_simp

include hχ hscale hgood in
theorem bwdFun_add_left {B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ}
    (hB : Invariant (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s)) B)
    (v v' : V) (w : W) :
    bwdFun abv ρ σ μ B (v + v') w = bwdFun abv ρ σ μ B v w + bwdFun abv ρ σ μ B v' w := by
  obtain ⟨H₁, h₁⟩ := hgood v w
  obtain ⟨H₂, h₂⟩ := hgood v' w
  have hHo : IsOpen ((H₁ ⊓ H₂ : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
      Set (Langlands.GeneralLinear (n + 1) K)) := h₁.1.inter h₂.1
  have g₁ := h₁.of_le inf_le_left hHo
  have g₂ := h₂.of_le inf_le_right hHo
  rw [bwdFun_eq μ hχ hscale hB (g₁.add_left g₂), bwdFun_eq μ hχ hscale hB g₁,
    bwdFun_eq μ hχ hscale hB g₂, valueAt_add_left]

include hχ hscale hgood in
theorem bwdFun_smul_left {B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ}
    (hB : Invariant (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s)) B)
    (c : ℂ) (v : V) (w : W) :
    bwdFun abv ρ σ μ B (c • v) w = c * bwdFun abv ρ σ μ B v w := by
  obtain ⟨H, h⟩ := hgood v w
  rw [bwdFun_eq μ hχ hscale hB (h.smul_left c), bwdFun_eq μ hχ hscale hB h, valueAt_smul_left]

include hχ hscale hgood in
theorem bwdFun_add_right {B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ}
    (hB : Invariant (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s)) B)
    (v : V) (w w' : W) :
    bwdFun abv ρ σ μ B v (w + w') = bwdFun abv ρ σ μ B v w + bwdFun abv ρ σ μ B v w' := by
  obtain ⟨H₁, h₁⟩ := hgood v w
  obtain ⟨H₂, h₂⟩ := hgood v w'
  have hHo : IsOpen ((H₁ ⊓ H₂ : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
      Set (Langlands.GeneralLinear (n + 1) K)) := h₁.1.inter h₂.1
  have g₁ := h₁.of_le inf_le_left hHo
  have g₂ := h₂.of_le inf_le_right hHo
  rw [bwdFun_eq μ hχ hscale hB (g₁.add_right g₂), bwdFun_eq μ hχ hscale hB g₁,
    bwdFun_eq μ hχ hscale hB g₂, valueAt_add_right]

include hχ hscale hgood in
theorem bwdFun_smul_right {B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ}
    (hB : Invariant (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s)) B)
    (c : ℂ) (v : V) (w : W) :
    bwdFun abv ρ σ μ B v (c • w) = c * bwdFun abv ρ σ μ B v w := by
  obtain ⟨H, h⟩ := hgood v w
  rw [bwdFun_eq μ hχ hscale hB (h.smul_right c), bwdFun_eq μ hχ hscale hB h, valueAt_smul_right]

/-- The backward bilinear form attached to an invariant trilinear form. -/
def bwdBil (B : SourceSpace abv ρ σ s) : V →ₗ[ℂ] W →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (bwdFun abv ρ σ μ B.1)
    (bwdFun_add_left μ hχ hscale hgood B.2) (bwdFun_smul_left μ hχ hscale hgood B.2)
    (bwdFun_add_right μ hχ hscale hgood B.2) (bwdFun_smul_right μ hχ hscale hgood B.2)

theorem bwdBil_apply (B : SourceSpace abv ρ σ s) (v : V) (w : W) :
    bwdBil μ hχ hscale hgood B v w = bwdFun abv ρ σ μ B.1 v w := rfl

/-- The backward linear map from invariant trilinear forms to mirabolic covariant forms. -/
def bwd : SourceSpace abv ρ σ s →ₗ[ℂ] TargetSpace abv ρ σ s where
  toFun B := ⟨bwdBil μ hχ hscale hgood B, fun p v w =>
    bwdFun_mirabolic μ hχ hscale hgood B.2 p.prop v w⟩
  map_add' B B' := Subtype.ext <| LinearMap.ext₂ fun v w => by
    change valueAt μ (B.1 + B'.1) v w _ = valueAt μ B.1 v w _ + valueAt μ B'.1 v w _
    exact valueAt_add_form μ _ _ v w _
  map_smul' c B := Subtype.ext <| LinearMap.ext₂ fun v w => by
    change valueAt μ (c • B.1) v w _ = c * valueAt μ B.1 v w _
    exact valueAt_smul_form μ _ c v w _

theorem bwd_apply (B : SourceSpace abv ρ σ s) (v : V) (w : W) :
    (bwd μ hχ hscale hgood B).1 v w = bwdFun abv ρ σ μ B.1 v w := rfl

end BackwardMap

section Forward

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
  {n : ℕ} (abv : AbsoluteValue K ℝ)
  {V : Type*} {W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) W)
  (s : ℂ)

/-- The density on nonzero rows attached to a bilinear form, through the chosen lift. -/
def dens (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (v : V) (w : W) (x : Fin (n + 1) → K) : ℂ :=
  β (ρ (lift x) v) (σ (lift x) w) * determinantWeight abv (lift x) (s - 1)

variable {abv ρ σ s}

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem covariant_of_mem {β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} (hβ : β ∈ TargetSpace abv ρ σ s)
    {p : Langlands.GeneralLinear (n + 1) K} (hp : p ∈ mirabolic n K) (v : V) (w : W) :
    β (ρ p v) (σ p w) = determinantWeight abv p (1 - s) * β v w :=
  hβ ⟨p, hp⟩ v w

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
/-- The density at the last row of `g` is computed by `g`, independently of the lift. -/
theorem dens_lastRow {β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} (hβ : β ∈ TargetSpace abv ρ σ s) (v : V) (w : W)
    (g : Langlands.GeneralLinear (n + 1) K) :
    dens abv ρ σ s β v w (lastRow g) = β (ρ g v) (σ g w) * determinantWeight abv g (s - 1) := by
  have hg' : lastRow (lift (lastRow g)) = lastRow g := lastRow_lift _ (lastRow_ne_zero g)
  obtain ⟨p, hp, e⟩ : ∃ p ∈ mirabolic n K, lift (lastRow g) = p * g :=
    ⟨_, mul_inv_mem_mirabolic_of_lastRow_eq hg', by group⟩
  unfold dens
  rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    covariant_of_mem hβ hp, determinantWeight_mul']
  linear_combination (β (ρ g v) (σ g w) * determinantWeight abv g (s - 1)) *
    determinantWeight_cancel abv p s

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
/-- Translating the vectors by `k` translates the density, up to `|det k|^(1-s)`. -/
theorem dens_translate {β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} (hβ : β ∈ TargetSpace abv ρ σ s) (v : V) (w : W)
    (k : Langlands.GeneralLinear (n + 1) K) {x : Fin (n + 1) → K} (hx : x ≠ 0) :
    dens abv ρ σ s β (ρ k v) (σ k w) x = determinantWeight abv k (1 - s) *
      dens abv ρ σ s β v w (x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) := by
  obtain ⟨g, rfl⟩ : ∃ g, lastRow g = x := ⟨lift x, lastRow_lift x hx⟩
  rw [← lastRow_mul_eq_vecMul, dens_lastRow hβ, dens_lastRow hβ, map_mul, map_mul,
    Module.End.mul_apply, Module.End.mul_apply, determinantWeight_mul']
  linear_combination (-(β (ρ g (ρ k v)) (σ g (σ k w)) * determinantWeight abv g (s - 1))) *
    determinantWeight_cancel abv k s

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem dens_add_left (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (v v' : V) (w : W) (x : Fin (n + 1) → K) :
    dens abv ρ σ s β (v + v') w x = dens abv ρ σ s β v w x + dens abv ρ σ s β v' w x := by
  simp only [dens, map_add, LinearMap.add_apply, add_mul]

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem dens_smul_left (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (c : ℂ) (v : V) (w : W) (x : Fin (n + 1) → K) :
    dens abv ρ σ s β (c • v) w x = c * dens abv ρ σ s β v w x := by
  simp only [dens, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc]

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem dens_add_right (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (v : V) (w w' : W) (x : Fin (n + 1) → K) :
    dens abv ρ σ s β v (w + w') x = dens abv ρ σ s β v w x + dens abv ρ σ s β v w' x := by
  simp only [dens, map_add, add_mul]

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem dens_smul_right (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (c : ℂ) (v : V) (w : W) (x : Fin (n + 1) → K) :
    dens abv ρ σ s β v (c • w) x = c * dens abv ρ σ s β v w x := by
  simp only [dens, map_smul, smul_eq_mul, mul_assoc]

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem dens_add_form (β β' : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (v : V) (w : W) (x : Fin (n + 1) → K) :
    dens abv ρ σ s (β + β') v w x = dens abv ρ σ s β v w x + dens abv ρ σ s β' v w x := by
  simp only [dens, LinearMap.add_apply, add_mul]

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem dens_smul_form (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (c : ℂ) (v : V) (w : W) (x : Fin (n + 1) → K) :
    dens abv ρ σ s (c • β) v w x = c * dens abv ρ σ s β v w x := by
  simp only [dens, LinearMap.smul_apply, smul_eq_mul, mul_assoc]

variable (hgood : ∀ (v : V) (w : W), ∃ H, Good abv ρ σ v w H)

include hgood in
/-- A test function vanishing at zero times the density is locally constant. -/
theorem isLocallyConstant_mul_dens {β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} (hβ : β ∈ TargetSpace abv ρ σ s)
    (v : V) (w : W) (Φ : Splus K n) :
    IsLocallyConstant fun x => Φ.1 x * dens abv ρ σ s β v w x := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : Φ.1 0 = 0 := Φ.2
    filter_upwards [Φ.1.locallyConstant.eventually_eq 0] with y hy
    rw [hy, h0, zero_mul, zero_mul]
  · obtain ⟨H, hH⟩ := hgood v w
    have hmem : orbitSet H (lift x) ∈ 𝓝 x := by
      have := (isOpen_orbitSet hH.1 (lift x)).mem_nhds (lastRow_mem_orbitSet H (lift x))
      rwa [lastRow_lift x hx] at this
    filter_upwards [Φ.1.locallyConstant.eventually_eq x, hmem] with y hy hy'
    obtain ⟨h, hh, hyh⟩ := hy'
    rw [hy, ← hyh]
    congr 1
    have hx' : dens abv ρ σ s β v w x = dens abv ρ σ s β v w (lastRow (lift x)) := by
      rw [lastRow_lift x hx]
    obtain ⟨h1, h2, h3⟩ := hH.2.2 h hh
    rw [hx', dens_lastRow hβ, dens_lastRow hβ, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, h1, h2, determinantWeight_mul', determinantWeight_eq_one abv h3,
      mul_one]

/-- The product of a test function vanishing at zero with the density, as a test function. -/
def prodS (β : TargetSpace abv ρ σ s) (v : V) (w : W) (Φ : Splus K n) :
    SchwartzBruhat (Fin (n + 1) → K) :=
  ⟨fun x => Φ.1 x * dens abv ρ σ s β.1 v w x,
    isLocallyConstant_mul_dens hgood β.2 v w Φ, Φ.1.hasCompactSupport.mul_right⟩

theorem prodS_apply (β : TargetSpace abv ρ σ s) (v : V) (w : W) (Φ : Splus K n)
    (x : Fin (n + 1) → K) :
    prodS hgood β v w Φ x = Φ.1 x * dens abv ρ σ s β.1 v w x := rfl

end Forward

section ForwardMap

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
  {n : ℕ} {abv : AbsoluteValue K ℝ}
  {V : Type*} {W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) W}
  [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)]
  (μ : Measure (Fin (n + 1) → K)) [μ.IsAddHaarMeasure]
  {χ : K →*₀ ℝ≥0} (hχ : ∀ a, (χ a : ℝ) = abv a)
  (hscale : ∀ k : Langlands.GeneralLinear (n + 1) K,
      μ.map (fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) =
        (χ (Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)))⁻¹ • μ)
  {s : ℂ}
  (hgood : ∀ (v : V) (w : W), ∃ H, Good abv ρ σ v w H)

omit [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)] in
theorem prodS_add_left (β : TargetSpace abv ρ σ s) (v v' : V) (w : W) (Φ : Splus K n) :
    prodS hgood β (v + v') w Φ = prodS hgood β v w Φ + prodS hgood β v' w Φ :=
  Hecke.TestFunction.ext fun x => by
    change Φ.1 x * dens abv ρ σ s β.1 (v + v') w x =
      Φ.1 x * dens abv ρ σ s β.1 v w x + Φ.1 x * dens abv ρ σ s β.1 v' w x
    rw [dens_add_left, mul_add]

omit [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)] in
theorem prodS_smul_left (β : TargetSpace abv ρ σ s) (c : ℂ) (v : V) (w : W) (Φ : Splus K n) :
    prodS hgood β (c • v) w Φ = c • prodS hgood β v w Φ :=
  Hecke.TestFunction.ext fun x => by
    change Φ.1 x * dens abv ρ σ s β.1 (c • v) w x = c * (Φ.1 x * dens abv ρ σ s β.1 v w x)
    rw [dens_smul_left]
    ring

omit [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)] in
theorem prodS_add_right (β : TargetSpace abv ρ σ s) (v : V) (w w' : W) (Φ : Splus K n) :
    prodS hgood β v (w + w') Φ = prodS hgood β v w Φ + prodS hgood β v w' Φ :=
  Hecke.TestFunction.ext fun x => by
    change Φ.1 x * dens abv ρ σ s β.1 v (w + w') x =
      Φ.1 x * dens abv ρ σ s β.1 v w x + Φ.1 x * dens abv ρ σ s β.1 v w' x
    rw [dens_add_right, mul_add]

omit [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)] in
theorem prodS_smul_right (β : TargetSpace abv ρ σ s) (c : ℂ) (v : V) (w : W) (Φ : Splus K n) :
    prodS hgood β v (c • w) Φ = c • prodS hgood β v w Φ :=
  Hecke.TestFunction.ext fun x => by
    change Φ.1 x * dens abv ρ σ s β.1 v (c • w) x = c * (Φ.1 x * dens abv ρ σ s β.1 v w x)
    rw [dens_smul_right]
    ring

omit [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)] in
theorem prodS_add_test (β : TargetSpace abv ρ σ s) (v : V) (w : W) (Φ Φ' : Splus K n) :
    prodS hgood β v w (Φ + Φ') = prodS hgood β v w Φ + prodS hgood β v w Φ' :=
  Hecke.TestFunction.ext fun x => by
    change (Φ.1 x + Φ'.1 x) * dens abv ρ σ s β.1 v w x =
      Φ.1 x * dens abv ρ σ s β.1 v w x + Φ'.1 x * dens abv ρ σ s β.1 v w x
    rw [add_mul]

omit [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)] in
theorem prodS_smul_test (β : TargetSpace abv ρ σ s) (c : ℂ) (v : V) (w : W) (Φ : Splus K n) :
    prodS hgood β v w (c • Φ) = c • prodS hgood β v w Φ :=
  Hecke.TestFunction.ext fun x => by
    change (c * Φ.1 x) * dens abv ρ σ s β.1 v w x = c * (Φ.1 x * dens abv ρ σ s β.1 v w x)
    rw [mul_assoc]

omit [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)] in
theorem prodS_add_form (β β' : TargetSpace abv ρ σ s) (v : V) (w : W) (Φ : Splus K n) :
    prodS hgood (β + β') v w Φ = prodS hgood β v w Φ + prodS hgood β' v w Φ :=
  Hecke.TestFunction.ext fun x => by
    change Φ.1 x * dens abv ρ σ s (β.1 + β'.1) v w x =
      Φ.1 x * dens abv ρ σ s β.1 v w x + Φ.1 x * dens abv ρ σ s β'.1 v w x
    rw [dens_add_form, mul_add]

omit [MeasurableSpace (Fin (n + 1) → K)] [BorelSpace (Fin (n + 1) → K)] in
theorem prodS_smul_form (β : TargetSpace abv ρ σ s) (c : ℂ) (v : V) (w : W) (Φ : Splus K n) :
    prodS hgood (c • β) v w Φ = c • prodS hgood β v w Φ :=
  Hecke.TestFunction.ext fun x => by
    change Φ.1 x * dens abv ρ σ s (c • β.1) v w x = c * (Φ.1 x * dens abv ρ σ s β.1 v w x)
    rw [dens_smul_form]
    ring

/-- The forward trilinear form: integrate the test function against the density. -/
def fwdForm (β : TargetSpace abv ρ σ s) : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun v w =>
    { toFun := fun Φ => mass μ (prodS hgood β v w Φ)
      map_add' := fun Φ Φ' => by rw [prodS_add_test, map_add]
      map_smul' := fun c Φ => by
        rw [prodS_smul_test, map_smul]
        rfl })
    (fun v v' w => LinearMap.ext fun Φ => by
      change mass μ (prodS hgood β (v + v') w Φ) =
        mass μ (prodS hgood β v w Φ) + mass μ (prodS hgood β v' w Φ)
      rw [prodS_add_left, map_add])
    (fun c v w => LinearMap.ext fun Φ => by
      change mass μ (prodS hgood β (c • v) w Φ) = c • mass μ (prodS hgood β v w Φ)
      rw [prodS_smul_left, map_smul])
    (fun v w w' => LinearMap.ext fun Φ => by
      change mass μ (prodS hgood β v (w + w') Φ) =
        mass μ (prodS hgood β v w Φ) + mass μ (prodS hgood β v w' Φ)
      rw [prodS_add_right, map_add])
    (fun c v w => LinearMap.ext fun Φ => by
      change mass μ (prodS hgood β v (c • w) Φ) = c • mass μ (prodS hgood β v w Φ)
      rw [prodS_smul_right, map_smul])

theorem fwdForm_apply (β : TargetSpace abv ρ σ s) (v : V) (w : W) (Φ : Splus K n) :
    fwdForm μ hgood β v w Φ = mass μ (prodS hgood β v w Φ) := rfl

include hχ hscale in
/-- The forward form is invariant with the determinant weight `-s`. -/
theorem fwdForm_invariant (β : TargetSpace abv ρ σ s) :
    Invariant (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s))
      (fwdForm μ hgood β) := by
  intro k v w Φ
  change mass μ (prodS hgood β (ρ k v) (σ k w) (splusRep K n k Φ)) =
    determinantWeight abv k (-s) * mass μ (prodS hgood β v w Φ)
  have e : prodS hgood β (ρ k v) (σ k w) (splusRep K n k Φ) =
      determinantWeight abv k (1 - s) • rowTranslate k (prodS hgood β v w Φ) := by
    refine Hecke.TestFunction.ext fun x => ?_
    change Φ.1 (x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) *
        dens abv ρ σ s β.1 (ρ k v) (σ k w) x =
      determinantWeight abv k (1 - s) * (Φ.1 (x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) *
        dens abv ρ σ s β.1 v w (x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)))
    by_cases hx : x = 0
    · subst hx
      have h0 : Φ.1 0 = 0 := Φ.2
      rw [Matrix.zero_vecMul, h0, zero_mul, zero_mul, mul_zero]
    · rw [dens_translate β.2 v w k hx]
      ring
  have hx : (abv (Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abv_det_ne_zero abv k)
  rw [e, map_smul, mass_rowTranslate μ χ hscale, hχ, determinantWeight_one_sub, smul_eq_mul]
  field_simp

/-- The forward linear map from mirabolic covariant forms to invariant trilinear forms. -/
def fwd : TargetSpace abv ρ σ s →ₗ[ℂ] SourceSpace abv ρ σ s where
  toFun β := ⟨fwdForm μ hgood β, fwdForm_invariant μ hχ hscale hgood β⟩
  map_add' β β' := Subtype.ext <| LinearMap.ext fun v => LinearMap.ext fun w =>
    LinearMap.ext fun Φ => by
      change mass μ (prodS hgood (β + β') v w Φ) =
        mass μ (prodS hgood β v w Φ) + mass μ (prodS hgood β' v w Φ)
      rw [prodS_add_form, map_add]
  map_smul' c β := Subtype.ext <| LinearMap.ext fun v => LinearMap.ext fun w =>
    LinearMap.ext fun Φ => by
      change mass μ (prodS hgood (c • β) v w Φ) = c * mass μ (prodS hgood β v w Φ)
      rw [prodS_smul_form, map_smul, smul_eq_mul]

theorem fwd_apply (β : TargetSpace abv ρ σ s) :
    (fwd μ hχ hscale hgood β).1 = fwdForm μ hgood β := rfl

/-- The backward value of the forward form recovers the bilinear form. -/
theorem bwdFun_fwdForm (β : TargetSpace abv ρ σ s) (v : V) (w : W) :
    bwdFun abv ρ σ μ (fwdForm μ hgood β) v w = β.1 v w := by
  have hH := good_goodChoice (hgood v w)
  unfold bwdFun valueAt
  set H := goodChoice abv ρ σ v w
  have hc := rowCond_orbitSet hH.1 hH.2.1 1
  have e : prodS hgood β v w (indS (orbitSet H 1)) = β.1 v w • (indS (orbitSet H 1)).1 := by
    refine Hecke.TestFunction.ext fun x => ?_
    change (indS (orbitSet H 1)).1 x * dens abv ρ σ s β.1 v w x =
      β.1 v w * (indS (orbitSet H 1)).1 x
    rw [indS_apply hc.1 hc.2.1 hc.2.2]
    by_cases hx : x ∈ orbitSet H 1
    · rw [Set.indicator_of_mem hx]
      obtain ⟨h, hh, hxh⟩ := hx
      simp only [one_mul] at hxh
      subst hxh
      obtain ⟨h1, h2, h3⟩ := hH.2.2 h hh
      rw [dens_lastRow β.2, h1, h2, determinantWeight_eq_one abv h3]
      ring
    · rw [Set.indicator_of_notMem hx, zero_mul, mul_zero]
  rw [fwdForm_apply, e, map_smul, smul_eq_mul, mul_div_assoc,
    div_self (mass_indS_orbitSet_ne_zero μ hH.1 hH.2.1 1), mul_one]

include hχ hscale hgood in
/-- An invariant form whose backward values all vanish is zero. -/
theorem eq_zero_of_bwdFun_eq_zero {B : V →ₗ[ℂ] W →ₗ[ℂ] Splus K n →ₗ[ℂ] ℂ}
    (hB : Invariant (S := Splus K n) ρ σ (splusRep K n) (fun g => determinantWeight abv g (-s)) B)
    (h0 : ∀ v w, bwdFun abv ρ σ μ B v w = 0) : B = 0 := by
  refine LinearMap.ext fun v => LinearMap.ext fun w => LinearMap.ext fun Φ => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply]
  obtain ⟨H₀, hH₀⟩ := hgood v w
  obtain ⟨U, hU⟩ := rowTestSmooth K (n + 1) Φ.1
  have hHo : IsOpen ((H₀ ⊓ U.toSubgroup : Subgroup (Langlands.GeneralLinear (n + 1) K)) :
      Set (Langlands.GeneralLinear (n + 1) K)) := hH₀.1.inter U.isOpen
  have hH := hH₀.of_le inf_le_left hHo
  obtain ⟨𝒪, h𝒪, c, hΦ⟩ := exists_eq_sum_indS hH.1 hH.2.1 Φ
    fun h hh x => hU h (Subgroup.mem_inf.mp hh).2 x
  rw [hΦ, map_sum]
  refine Finset.sum_eq_zero fun O hO => ?_
  obtain ⟨g, rfl⟩ := h𝒪 O hO
  rw [map_smul]
  have hcH := hH.conj g
  have hψ : indS (orbitSet (H₀ ⊓ U.toSubgroup) g) =
      splusRep K n g⁻¹ (indS (orbitSet (conj g (H₀ ⊓ U.toSubgroup)) 1)) := by
    rw [splusRep_indS_orbitSet hcH.1 hcH.2.1, conj_conj_inv, one_mul, inv_inv]
  have hval := h0 (ρ g v) (σ g w)
  rw [bwdFun_eq μ hχ hscale hB hcH] at hval
  unfold valueAt at hval
  have hzero := (div_eq_zero_iff.mp hval).resolve_right
    (mass_indS_orbitSet_ne_zero μ hcH.1 hcH.2.1 1)
  have hBg := hB g⁻¹ (ρ g v) (σ g w) (indS (orbitSet (conj g (H₀ ⊓ U.toSubgroup)) 1))
  have hv : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hw : σ g⁻¹ (σ g w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hv, hw, hzero, mul_zero] at hBg
  rw [hψ, hBg, smul_zero]

include hχ hscale in
/-- The forward form of the backward form is the original invariant form. -/
theorem fwdForm_bwd (B : SourceSpace abv ρ σ s) :
    fwdForm μ hgood (bwd μ hχ hscale hgood B) = B.1 := by
  set F := fwdForm μ hgood (bwd μ hχ hscale hgood B) with hF
  have h1 : Invariant (S := Splus K n) ρ σ (splusRep K n)
      (fun g => determinantWeight abv g (-s)) F :=
    fwdForm_invariant μ hχ hscale hgood (bwd μ hχ hscale hgood B)
  have h2 : Invariant (S := Splus K n) ρ σ (splusRep K n)
      (fun g => determinantWeight abv g (-s)) B.1 := B.2
  have hD : Invariant (S := Splus K n) ρ σ (splusRep K n)
      (fun g => determinantWeight abv g (-s)) (F - B.1) := by
    intro g v w φ
    have e1 : F (ρ g v) (σ g w) (splusRep K n g φ) = determinantWeight abv g (-s) * F v w φ :=
      h1 g v w φ
    have e2 : B.1 (ρ g v) (σ g w) (splusRep K n g φ) =
        determinantWeight abv g (-s) * B.1 v w φ := h2 g v w φ
    change F (ρ g v) (σ g w) (splusRep K n g φ) - B.1 (ρ g v) (σ g w) (splusRep K n g φ) =
      determinantWeight abv g (-s) * (F v w φ - B.1 v w φ)
    rw [e1, e2, mul_sub]
  have h0 : ∀ (v : V) (w : W), bwdFun abv ρ σ μ (F - B.1) v w = 0 := by
    intro v w
    unfold bwdFun
    rw [valueAt_sub_form]
    change bwdFun abv ρ σ μ F v w - bwdFun abv ρ σ μ B.1 v w = 0
    rw [hF, bwdFun_fwdForm μ hgood, bwd_apply, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_bwdFun_eq_zero μ hχ hscale hgood hD h0)

/-- The Frobenius equivalence over a Hausdorff topological field with determinant-scaled
Haar measure on row space. -/
def frobeniusEquiv : SourceSpace abv ρ σ s ≃ₗ[ℂ] TargetSpace abv ρ σ s :=
  LinearEquiv.ofLinearMap (bwd μ hχ hscale hgood) (fwd μ hχ hscale hgood)
    (LinearMap.ext fun β => Subtype.ext <| LinearMap.ext₂ fun v w =>
      bwdFun_fwdForm μ hgood β v w)
    (LinearMap.ext fun B => Subtype.ext (fwdForm_bwd μ hχ hscale hgood B))

end ForwardMap

end EqualRankFrobenius

open EqualRankFrobenius MeasureTheory
open scoped Matrix NNReal

/-- The published equal-rank Frobenius equivalence: invariant trilinear forms on row test
functions vanishing at zero, with determinant weight `-s`, are complex-linearly equivalent to
mirabolic covariant bilinear forms with weight `1 - s`. -/
theorem equalRankFrobenius {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) : EqualRankFrobeniusStatement.{uF, uV, uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro V _ _ W _ _ ρ σ hρ hσ s
  let μ : Measure (Fin (n + 1) → F.Carrier) := Measure.addHaar
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F.Carrier).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    HarmonicAnalysis.padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have hscale : ∀ k : Langlands.GeneralLinear (n + 1) F.Carrier,
      μ.map (fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) =
        (T.normalizedAbsHom (Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)))⁻¹ •
          μ := by
    intro k
    have hM : Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)ᵀ ≠ 0 := by
      rw [Matrix.det_transpose]
      exact det_ne_zero k
    have h := HarmonicAnalysis.haarMeasure_map_matrix (Measure.addHaar : Measure F.Carrier)
      T.normalizedAbsHom hχ μ hM
    rw [Matrix.det_transpose] at h
    have e : (fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) =
        ⇑(Matrix.toLin' (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)ᵀ) := by
      funext x
      rw [Matrix.toLin'_apply, Matrix.mulVec_transpose]
    rw [e, h]
  have hdet : IsOpen {g : Langlands.GeneralLinear (n + 1) F.Carrier |
      normalizedAbsoluteValue T (Matrix.det (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) =
        1} := by
    have e : {g : Langlands.GeneralLinear (n + 1) F.Carrier |
        normalizedAbsoluteValue T
          (Matrix.det (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) = 1} =
        ((T.determinantNorm (n + 1)).ker : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
      ext g
      rw [Set.mem_ofPred_eq, SetLike.mem_coe, MonoidHom.mem_ker, ← Units.val_eq_one,
        ← NNReal.coe_eq_one, T.determinantNorm_coe]
      rfl
    rw [e]
    exact T.isOpen_ker_determinantNorm (n + 1)
  have hK₀ : ∃ K₀ : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
      IsOpen (K₀ : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∧
        IsCompact (K₀ : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
    ⟨GeneralLinearGroup.integralSubgroup (Fin (n + 1)) T.Integers,
      GeneralLinearGroup.isOpen_integralSubgroup _ _ T.isOpen_integers,
      GeneralLinearGroup.isCompact_integralSubgroup _ _ T.isCompact_integers⟩
  exact ⟨frobeniusEquiv μ (abv := normalizedAbsoluteValue T) (χ := T.normalizedAbsHom)
    (fun _ => rfl) hscale (exists_good hρ hσ hdet hK₀)⟩

end Langlands.RankinSelberg
