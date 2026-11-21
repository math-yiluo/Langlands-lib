import Langlands.Group.GL.BruhatMatrixChartDifferential
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # The actual Bruhat cell in the slice of the local matrix chart -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

open Set Filter
open scoped Matrix.Norms.Operator Topology

namespace Langlands.GeneralLinear

universe u

variable {F : Type u} [RCLike F] {n : ℕ} (w : Equiv.Perm (Fin n))

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "B" => upperTriangularSubgroup n F
local notation "V" => permutationUnipotentMinus n F w
local notation "P" => permutation n F w
local notation "T" => (bruhatUpperSpace F n × bruhatInversionSpace F w)

/-- The image of the actual upper Bruhat cell in the ambient matrix space. -/
def bruhatCellMatrixSet (F : Type u) [RCLike F] {n : ℕ} (w : Equiv.Perm (Fin n)) :
    Set (Matrix (Fin n) (Fin n) F) :=
  Set.range (fun g : UpperBruhatCell n F w => g.val.val)

theorem bruhatCellMatrixSet_eq_image :
    bruhatCellMatrixSet F w =
      (Units.val : Langlands.GeneralLinear n F → M) '' upperBruhatCell n F w := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, g.property, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

private theorem exists_inversionMatrixFactor (R : bruhatInversionSpace F w) :
    ∃ v : V, (P * v.val * P⁻¹).val = 1 + R.val := by
  let A : M := 1 + R.val
  have hzero (i j : Fin n) (hij : i < j) : A i j = 0 := by
    simp [A, Matrix.one_apply_ne hij.ne, R.property i j (fun h => hij.not_gt h.1)]
  have hdiag (i : Fin n) : A i i = 1 := by
    simp [A, R.property i i (by simp)]
  have hA : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isLowerTriangular A (fun _ _ h => hzero _ _ h)]
    simp [hdiag]
  let a := hA.unit
  have ha : a.val = A := hA.unit_spec
  let v := P⁻¹ * a * P
  have hc : P * v * P⁻¹ = a := by
    dsimp only [v]
    group
  have hv : v ∈ V := by
    rw [mem_permutationUnipotentMinus_iff, hc, mem_lowerUnipotent_iff, mem_upperUnipotent_iff]
    have he (i j : Fin n) : v i j = A (w i) (w j) := by
      have e := permutation_conjugate_entry n F w.symm a i j
      have ew : permutation n F w.symm = P⁻¹ := (permutation_inv n F w).symm
      rw [ew, inv_inv] at e
      simpa only [Equiv.Perm.coe_inv, Equiv.symm_symm, ha] using e
    refine ⟨⟨fun i j hij => ?_, fun i => (he i i).trans (hdiag _)⟩, ?_⟩
    · have hne := w.injective.ne hij.ne.symm
      rw [he]
      simp [A, Matrix.one_apply_ne hne, R.property (w i) (w j)
        (fun h => hij.not_gt (by simpa using h.2))]
    · change (∀ i j : Fin n, i < j → a.val i j = 0) ∧ ∀ i, a.val i i = 1
      simpa only [ha] using And.intro hzero hdiag
  exact ⟨⟨v, hv⟩, by simpa only [hc] using ha⟩

/-- Near the tangent origin, the two-factor matrix parameterization
has values in the actual Bruhat cell. -/
theorem eventually_bruhatCellMatrixParam_mem (b : B) (v : V) :
    ∀ᶠ z : T in 𝓝 0, bruhatCellMatrixParam b (P * v.val) z ∈ bruhatCellMatrixSet F w := by
  have hu : Continuous (fun z : T => (1 : M) + z.1.val) :=
    continuous_const.add (continuous_subtype_val.comp continuous_fst)
  have h₁ : (1 : M) + (0 : T).1.val ∈ {A : M | IsUnit A} := by simp
  filter_upwards [hu.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds h₁)] with z hz
  have hupper : ((1 : M) + z.1.val).IsUpperTriangular := by
    intro i j h
    change j < i at h
    simp [Matrix.one_apply_ne h.ne.symm, z.1.property i j h.not_ge]
  have hz' : IsUnit ((1 : M) + z.1.val) := hz
  let b₀ : B := ⟨hz'.unit, by
    change hz'.unit.val.IsUpperTriangular
    rwa [hz'.unit_spec]⟩
  obtain ⟨v₀, hv₀⟩ := exists_inversionMatrixFactor w z.2
  refine ⟨upperBruhatCellMap n F w (b * b₀, v₀ * v), ?_⟩
  have hmul : ((b * b₀).val * P * (v₀ * v).val) =
      b.val * b₀.val * (P * v₀.val * P⁻¹) * (P * v.val) := by
    change b.val * b₀.val * P * (v₀.val * v.val) =
      b.val * b₀.val * (P * v₀.val * P⁻¹) * (P * v.val)
    group
  change ((b * b₀).val * P * (v₀ * v).val).val = _
  rw [hmul]
  change b.val.val * b₀.val.val * (P * v₀.val * P⁻¹).val * (P * v.val).val = _
  rw [hv₀]
  exact congrArg (fun A : M => b.val.val * A * (1 + z.2.val) * (P * v.val).val) hz'.unit_spec

private def upperDisplacement (b b' : B) : bruhatUpperSpace F n :=
  ⟨(b⁻¹ * b').val.val - 1, fun i j hij => by
    have h := (b⁻¹ * b').property (lt_of_not_ge hij)
    rw [Matrix.sub_apply, h, Matrix.one_apply_ne (lt_of_not_ge hij).ne.symm, sub_zero]⟩

private def inversionDisplacement (v v' : V) : bruhatInversionSpace F w := by
  let a := (v' * v⁻¹).val
  let c := P * a * P⁻¹
  have hm := (mem_permutationUnipotentMinus_iff n F w a).mp (v' * v⁻¹).property
  have hc := (mem_lowerUnipotent_iff n F c).mp hm.2
  refine ⟨c.val - 1, fun i j h => ?_⟩
  change c i j - (1 : M) i j = 0
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [hc.1 i j hij, Matrix.one_apply_ne hij.ne, sub_zero]
  · rw [hc.2 i, Matrix.one_apply_eq, sub_self]
  · have hji' : w.symm j < w.symm i := lt_of_le_of_ne
      (le_of_not_gt (fun k => h ⟨hji, k⟩)) (w.symm.injective.ne hji.ne)
    rw [show c i j = a (w.symm i) (w.symm j) from permutation_conjugate_entry n F w a i j,
      hm.1.1 hji', Matrix.one_apply_ne hji.ne.symm, sub_zero]

private def cellDisplacement (b : B) (v : V) (q : B × V) : T :=
  (upperDisplacement b q.1, inversionDisplacement w v q.2)

private theorem continuous_cellDisplacement (b : B) (v : V) :
    Continuous (cellDisplacement w b v) := by
  apply Continuous.prodMk
  · change Continuous (fun q : B × V => upperDisplacement b q.1)
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    exact (Units.continuous_val.comp
      (continuous_const.mul (continuous_subtype_val.comp continuous_fst))).sub continuous_const
  · change Continuous (fun q : B × V => inversionDisplacement w v q.2)
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    exact (Units.continuous_val.comp
      ((continuous_const.mul ((continuous_subtype_val.comp continuous_snd).mul continuous_const)).mul
        continuous_const)).sub continuous_const

private theorem cellDisplacement_self (b : B) (v : V) : cellDisplacement w b v (b, v) = 0 := by
  apply Prod.ext <;> apply Subtype.ext
  · change (b⁻¹ * b).val.val - 1 = 0
    simp
  · change (P * (v * v⁻¹).val * P⁻¹).val - 1 = 0
    rw [mul_inv_cancel]
    change (P * 1 * P⁻¹).val - 1 = 0
    rw [mul_one, mul_inv_cancel, Units.val_one, sub_self]

private theorem bruhatCellMatrixParam_cellDisplacement (b : B) (v : V) (q : B × V) :
    bruhatCellMatrixParam b (P * v.val) (cellDisplacement w b v q) =
      (upperBruhatCellMap n F w q).val.val := by
  change b.val.val * (1 + ((b⁻¹ * q.1).val.val - 1)) *
    (1 + ((P * (q.2 * v⁻¹).val * P⁻¹).val - 1)) * (P * v.val).val = _
  have hcancel (A : M) : 1 + (A - 1) = A := by abel
  rw [hcancel, hcancel]
  change (b.val * (b⁻¹ * q.1).val * (P * (q.2 * v⁻¹).val * P⁻¹) * (P * v.val)).val =
    (q.1.val * P * q.2.val).val
  congr 1
  change b.val * (b.val⁻¹ * q.1.val) * (P * (q.2.val * v.val⁻¹) * P⁻¹) * (P * v.val) = _
  group

/-- For any open chart with the designated forward map on the zero
normal slice, that slice locally equals the actual Bruhat cell. -/
theorem eventually_mem_bruhatCellMatrixSet_iff {Y : Type*} [TopologicalSpace Y] [Zero Y]
    (b : B) (v : V) (e : OpenPartialHomeomorph (T × Y) M)
    (h0 : (0, 0) ∈ e.source)
    (he : ∀ z : T, e (z, 0) = bruhatCellMatrixParam b (P * v.val) z) :
    ∀ᶠ z : T × Y in 𝓝 (0, 0), e z ∈ bruhatCellMatrixSet F w ↔ z.2 = 0 := by
  let c := UpperBruhatCoordinates.cellHomeomorph (K := F) w
  let p : UpperBruhatCell n F w := c (b, v)
  let val : UpperBruhatCell n F w → M := fun g => g.val.val
  let z' (g : UpperBruhatCell n F w) : T × Y := (cellDisplacement w b v (c.symm g), 0)
  have hz' : Continuous z' := ((continuous_cellDisplacement w b v).comp c.symm.continuous).prodMk
    continuous_const
  have hzp : z' p = (0, 0) := by
    change (cellDisplacement w b v (c.symm (c (b, v))), 0) = (0, 0)
    rw [c.symm_apply_apply, cellDisplacement_self]
  have hval : val p = e (0, 0) := by
    rw [he, bruhatCellMatrixParam_zero]
    change (b.val * P * v.val).val = (b.val * (P * v.val)).val
    rw [mul_assoc]
  have hind : Topology.IsInducing val :=
    Units.isOpenEmbedding_val.isEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
  have hsp : z' p ∈ e.source := by simpa only [hzp] using h0
  have hsource : ∀ᶠ g in 𝓝 p, z' g ∈ e.source :=
    hz'.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hsp)
  rw [hind.nhds_eq_comap p, eventually_comap, hval] at hsource
  filter_upwards [e.open_source.mem_nhds h0, (e.continuousAt h0).eventually hsource,
    (continuous_fst.continuousAt (x := (0, 0))).eventually
      (eventually_bruhatCellMatrixParam_mem w b v)] with z hz hrec htan
  constructor
  · rintro ⟨g, hg⟩
    have hs : z' g ∈ e.source := hrec g hg
    have hf : e (z' g) = e z := by
      calc
        e (z' g) = bruhatCellMatrixParam b (P * v.val) (cellDisplacement w b v (c.symm g)) := he _
        _ = val (c (c.symm g)) := bruhatCellMatrixParam_cellDisplacement w b v _
        _ = e z := by rw [c.apply_symm_apply]; exact hg
    exact congrArg Prod.snd (e.injOn hz hs hf.symm)
  · intro h
    have hze : z = (z.1, 0) := Prod.ext rfl h
    rw [hze, he]
    exact htan

end Langlands.GeneralLinear
