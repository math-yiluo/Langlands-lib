import Langlands.Geometry.Analytic.DrinfeldFacetStabilizerStatement
import Langlands.Geometry.Analytic.DrinfeldLevelOneBase
import Langlands.Topology.CompactNormCharacter
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Compact openness of the determinant-norm-one facet stabilizer -/

noncomputable section

universe v w

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

open Set Filter Topology
open scoped Matrix NNReal Pointwise

section VectorNormStabilizer

variable {F : Type v} [NontriviallyNormedField F] {n : Type w} [Fintype n]

local notation "GL" => Matrix.GeneralLinearGroup n F
local notation "Mat" => Matrix n n F
local notation "V" => (n → F)

private theorem continuous_vectorNorm [DecidableEq n] (ν : VectorNorm F V) :
    Continuous (ν : V → ℝ) := by
  let p : Seminorm F V := Seminorm.of ν
    (fun x y => (ν.add_le_max x y).trans (max_le_add_of_nonneg (ν.nonneg x) (ν.nonneg y)))
    ν.map_smul
  let C : ℝ≥0 := ⟨∑ i : n, ν (Pi.single i 1), Finset.sum_nonneg fun _ _ => ν.nonneg _⟩
  change Continuous p
  apply Seminorm.continuous_of_le (q := C • normSeminorm F V)
  · exact continuous_const.mul continuous_norm
  · intro x
    change ν x ≤ (C : ℝ) * ‖x‖
    have hx : (∑ i : n, x i • Pi.single i (1 : F)) = x := by
      simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single x
    calc
      ν x = p (∑ i : n, x i • Pi.single i (1 : F)) := by rw [hx]; rfl
      _ ≤ ∑ i : n, p (x i • Pi.single i (1 : F)) :=
        Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
      _ ≤ (∑ i : n, ν (Pi.single i 1)) * ‖x‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun i _ => ?_
        change ν (x i • Pi.single i (1 : F)) ≤ ν (Pi.single i 1) * ‖x‖
        rw [ν.map_smul, mul_comm ‖x i‖]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (ν.nonneg _)

private theorem exists_smul_mem_unitSphere [Nonempty n] {x : V} (hx : x ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ a • x ∈ Metric.sphere (0 : V) 1 := by
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm x).1
  change ‖x i‖ = ‖x‖ at hi
  have hi₀ : x i ≠ 0 := norm_ne_zero_iff.mp (hi.trans_ne (norm_ne_zero_iff.mpr hx))
  refine ⟨(x i)⁻¹, inv_ne_zero hi₀, mem_sphere_zero_iff_norm.mpr ?_⟩
  rw [norm_smul, norm_inv, hi, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

variable [DecidableEq n]

private theorem vectorNorm_lower_bound [ProperSpace F] [Nonempty n] (ν : VectorNorm F V) :
    ∃ m : ℝ, 0 < m ∧ ∀ x : V, m * ‖x‖ ≤ ν x := by
  let S : Set V := Metric.sphere 0 1
  have hS : S.Nonempty := ⟨fun _ => 1, mem_sphere_zero_iff_norm.mpr (by simp)⟩
  obtain ⟨y, hy, hymin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hS
    (continuous_vectorNorm ν).continuousOn
  have hy₀ : y ≠ 0 := by
    intro h
    simpa [h] using mem_sphere_zero_iff_norm.mp hy
  refine ⟨ν y, ν.pos hy₀, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨a, ha, hax⟩ := exists_smul_mem_unitSphere hx
  have hnorm : ‖a‖ * ‖x‖ = 1 := by
    simpa only [norm_smul] using mem_sphere_zero_iff_norm.mp hax
  have hle := hymin hax
  change ν y ≤ ν (a • x) at hle
  rw [ν.map_smul] at hle
  apply (mul_le_mul_iff_right₀ (norm_pos_iff.mpr ha)).mp
  calc
    ‖a‖ * (ν y * ‖x‖) = ν y := by
      rw [← mul_assoc, mul_comm ‖a‖, mul_assoc, hnorm, mul_one]
    _ ≤ ‖a‖ * ν x := hle

private theorem isCompact_vectorNorm_sublevel [ProperSpace F] [Nonempty n]
    (ν : VectorNorm F V) (r : ℝ) :
    IsCompact {x : V | ν x ≤ r} := by
  obtain ⟨m, hm, hmin⟩ := vectorNorm_lower_bound ν
  refine (isCompact_closedBall (0 : V) (r / m)).of_isClosed_subset
    (isClosed_le (continuous_vectorNorm ν) continuous_const) fun x hx => ?_
  apply mem_closedBall_zero_iff.mpr
  rw [le_div_iff₀ hm, mul_comm]
  exact (hmin x).trans hx

private def nonexpandingMatrices (ν : VectorNorm F V) : Submonoid Mat where
  carrier := {A | ∀ x : V, ν (x ᵥ* A) ≤ ν x}
  one_mem' := fun x => (congrArg ν (Matrix.vecMul_one x)).le
  mul_mem' := fun {A B} hA hB x => by
    rw [← Matrix.vecMul_vecMul]
    exact (hB (x ᵥ* A)).trans (hA x)

private theorem isCompact_nonexpandingMatrices [ProperSpace F] [Nonempty n] (ν : VectorNorm F V) :
    IsCompact (nonexpandingMatrices ν : Set Mat) := by
  let R : n → Set V := fun i => {x | ν x ≤ ν (Pi.single i 1)}
  have hR : IsCompact (Set.pi univ R) := isCompact_univ_pi fun i =>
    isCompact_vectorNorm_sublevel ν _
  refine hR.of_isClosed_subset ?_ ?_
  · change IsClosed {A : Mat | ∀ x : V, ν (x ᵥ* A) ≤ ν x}
    simp_rw [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_le
      ((continuous_vectorNorm ν).comp (continuous_const.matrix_vecMul continuous_id))
      continuous_const
  · intro A hA
    change Mat at A
    refine mem_pi.mpr fun i _ => ?_
    change ν (A i) ≤ ν (Pi.single i 1)
    have hi := hA (Pi.single i (1 : F))
    change ν (Pi.single i (1 : F) ᵥ* A) ≤ ν (Pi.single i 1) at hi
    rwa [Matrix.single_one_vecMul] at hi

private theorem stabilizer_eq_nonexpandingUnits (ν : VectorNorm F V) :
    MulAction.stabilizer GL ν = (nonexpandingMatrices ν).units := by
  ext g
  constructor
  · intro hg
    have hgi := (MulAction.stabilizer GL ν).inv_mem hg
    exact ⟨fun x => (congrArg (fun p : VectorNorm F V => p x) hg).le,
      fun x => (congrArg (fun p : VectorNorm F V => p x) hgi).le⟩
  · rintro ⟨hg, hgi⟩
    apply VectorNorm.ext
    intro x
    refine le_antisymm (hg x) ?_
    have h := hgi (x ᵥ* (g : Mat))
    change ν ((x ᵥ* (g : Mat)) ᵥ* ((g⁻¹ : GL) : Mat)) ≤ ν (x ᵥ* (g : Mat)) at h
    rwa [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at h

private theorem eventually_nonexpandingMatrices [ProperSpace F] [Nonempty n] (ν : VectorNorm F V) :
    ∀ᶠ A : Mat in 𝓝 1, A ∈ nonexpandingMatrices ν := by
  have hnear : ∀ᶠ A : Mat in 𝓝 1, ∀ x ∈ Metric.sphere (0 : V) 1, ν (x ᵥ* A - x) < ν x := by
    apply (isCompact_sphere (0 : V) 1).eventually_forall_of_forall_eventually
    intro x hx
    have hν := continuous_vectorNorm ν
    have hopen : IsOpen {z : Mat × V | ν (z.2 ᵥ* z.1 - z.2) < ν z.2} :=
      isOpen_lt (hν.comp ((continuous_snd.matrix_vecMul continuous_fst).sub continuous_snd))
        (hν.comp continuous_snd)
    refine hopen.mem_nhds ?_
    have hx₀ : x ≠ 0 := norm_ne_zero_iff.mp
      ((mem_sphere_zero_iff_norm.mp hx).trans_ne one_ne_zero)
    simpa only [mem_ofPred_eq, Matrix.vecMul_one, sub_self, ν.map_zero] using ν.pos hx₀
  filter_upwards [hnear] with A hA
  intro x
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨a, ha, hax⟩ := exists_smul_mem_unitSphere hx
  have h := hA _ hax
  rw [Matrix.smul_vecMul, ← smul_sub, ν.map_smul, ν.map_smul,
    mul_lt_mul_iff_right₀ (norm_pos_iff.mpr ha)] at h
  calc
    ν (x ᵥ* A) = ν ((x ᵥ* A - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (ν (x ᵥ* A - x)) (ν x) := ν.add_le_max _ _
    _ = ν x := max_eq_right h.le

private theorem isCompactOpen_normStabilizer [ProperSpace F] [Nonempty n] (ν : VectorNorm F V) :
    IsCompact (MulAction.stabilizer GL ν : Set GL) ∧
      IsOpen (MulAction.stabilizer GL ν : Set GL) := by
  rw [stabilizer_eq_nonexpandingUnits]
  refine ⟨Submonoid.units_isCompact (isCompact_nonexpandingMatrices ν), ?_⟩
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have h := eventually_nonexpandingMatrices ν
  have hval : Tendsto (fun g : GL => (g : Mat)) (𝓝 1) (𝓝 1) := Units.continuous_val.continuousAt
  have hinv : Tendsto (fun g : GL => ((g⁻¹ : GL) : Mat)) (𝓝 1) (𝓝 1) :=
    Units.continuous_coe_inv.continuousAt
  filter_upwards [hval.eventually h, hinv.eventually h] with g hg hgi
  exact ⟨hg, hgi⟩

end VectorNormStabilizer

section VertexTransport

variable {F : Type v} [NontriviallyNormedField F] {d : ℕ}

local notation "GL" => Matrix.GeneralLinearGroup (Fin (d + 1)) F
local notation "Mat" => Matrix (Fin (d + 1)) (Fin (d + 1)) F
local notation "V" => (Fin (d + 1) → F)

private theorem mem_detNormOne_of_stabilizes_norm {ν : VectorNorm F V}
    (hcompact : IsCompact (MulAction.stabilizer GL ν : Set GL))
    {g : GL} (hg : g ∈ MulAction.stabilizer GL ν) : g ∈ detNormOne F d := by
  let χ : GL →* ℝ≥0ˣ :=
    (Units.map (nnnormHom : F →*₀ ℝ≥0).toMonoidHom).comp Matrix.GeneralLinearGroup.det
  have hχ : Continuous χ :=
    (continuous_nnnorm.units_map _).comp Matrix.GeneralLinearGroup.continuous_det
  exact mem_detNormOne.mpr (congrArg (fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ))
    (Langlands.RankinSelberg.LastRowReduction.eq_one_of_isCompact χ hχ _ hcompact hg))

private theorem stabilizes_norm_of_stabilizes_class {ν : VectorNorm F V}
    (hν : ν.IsLatticeNorm) (hcompact : IsCompact (MulAction.stabilizer GL ν : Set GL))
    {g : GL} (hg : g ∈ detNormOne F d) (hclass : g • (⟦ν⟧ : NormClass F V) = ⟦ν⟧) :
    g ∈ MulAction.stabilizer GL ν := by
  rw [NormClass.smul_mk] at hclass
  have hhom : VectorNorm.Homothetic ν (g • ν) := Quotient.exact hclass.symm
  obtain ⟨c, hc, hscale⟩ := hhom
  let e : V := fun _ => 1
  have he : e ≠ 0 := fun h => one_ne_zero (congrFun h (0 : Fin (d + 1)))
  obtain ⟨b, hb⟩ := hν e
  obtain ⟨a, ha⟩ := hν (e ᵥ* (g : Mat))
  have hb₀ : ‖b‖ ≠ 0 := (hb ▸ ν.pos he).ne'
  have hnorm : ‖a / b‖ = c := by
    rw [norm_div, ← ha, ← VectorNorm.smul_apply, hscale e, hb, mul_div_cancel_right₀ _ hb₀]
  let u : Fˣ := Units.mk0 (a / b) (norm_ne_zero_iff.mp (hnorm ▸ hc.ne'))
  have hu : ‖(↑(u⁻¹) : F)‖ = c⁻¹ := by
    rw [Units.val_inv_eq_inv_val, norm_inv, show ‖(u : F)‖ = c from hnorm]
  have hscaled : g * Matrix.GeneralLinearGroup.scalar _ u⁻¹ ∈ MulAction.stabilizer GL ν := by
    apply VectorNorm.ext
    intro x
    rw [VectorNorm.smul_apply, Units.val_mul, ← Matrix.vecMul_vecMul,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.vecMul_diagonal_const,
      op_smul_eq_smul, ν.map_smul, hu, ← VectorNorm.smul_apply, hscale x, ← mul_assoc,
      inv_mul_cancel₀ hc.ne', one_mul]
  have hdet := mem_detNormOne.mp (mem_detNormOne_of_stabilizes_norm hcompact hscaled)
  rw [map_mul, Units.val_mul, norm_mul, mem_detNormOne.mp hg, one_mul,
    Matrix.GeneralLinearGroup.det_scalar, Units.val_pow_eq_pow_val, norm_pow, hu] at hdet
  have hc' : c⁻¹ = 1 := (pow_eq_one_iff_of_nonneg (inv_nonneg.mpr hc.le)
    Fintype.card_ne_zero).mp hdet
  exact VectorNorm.ext fun x => by rw [hscale x, inv_eq_one.mp hc', one_mul]

private theorem isCompactOpen_vertexFiber [ProperSpace F] (ν : VectorNorm F V) (hν : ν.IsLatticeNorm)
    (y : NormClass F V) :
    IsCompact {g : GL | g • (⟦ν⟧ : NormClass F V) = y ∧ g ∈ detNormOne F d} ∧
      IsOpen {g : GL | g • (⟦ν⟧ : NormClass F V) = y ∧ g ∈ detNormOne F d} := by
  let B : Set GL := {g | g • (⟦ν⟧ : NormClass F V) = y ∧ g ∈ detNormOne F d}
  change IsCompact B ∧ IsOpen B
  by_cases hB : B.Nonempty
  · obtain ⟨g, hg, hgdet⟩ := hB
    have hP := isCompactOpen_normStabilizer ν
    have htranslate : B = (g * ·) '' (MulAction.stabilizer GL ν : Set GL) := by
      ext a
      constructor
      · rintro ⟨ha, hadet⟩
        refine ⟨g⁻¹ * a, stabilizes_norm_of_stabilizes_class hν hP.1
          ((detNormOne F d).mul_mem ((detNormOne F d).inv_mem hgdet) hadet) ?_, by simp⟩
        rw [mul_smul, ha, ← hg, inv_smul_smul]
      · rintro ⟨b, hb, rfl⟩
        refine ⟨?_, (detNormOne F d).mul_mem hgdet (mem_detNormOne_of_stabilizes_norm hP.1 hb)⟩
        rw [mul_smul, NormClass.smul_mk, MulAction.mem_stabilizer_iff.mp hb, hg]
    rw [htranslate]
    exact ⟨hP.1.image (continuous_const.mul continuous_id), isOpenMap_mul_left g _ hP.2⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hB]
    exact ⟨isCompact_empty, isOpen_empty⟩

end VertexTransport

/-- The determinant-norm-one elements of the setwise stabilizer of a facet form a compact open
subset of the matrix general linear group. -/
theorem facetStabilizerCompactOpen : FacetStabilizerCompactOpenStatement.{v} := by
  classical
  intro F _ _ d S hS
  obtain ⟨k, ν, hν, rfl⟩ := hS
  let vertex (i : Fin (k + 1)) : NormClass F (Fin (d + 1) → F) := ⟦ν i⟧
  let U (i j : Fin (k + 1)) : Set (Matrix.GeneralLinearGroup (Fin (d + 1)) F) :=
    {g | g • vertex i = vertex j ∧ g ∈ detNormOne F d}
  have hU (i j : Fin (k + 1)) : IsCompact (U i j) ∧ IsOpen (U i j) :=
    isCompactOpen_vertexFiber (ν i) (hν.isLatticeNorm i) (vertex j)
  have hset : {g : Matrix.GeneralLinearGroup (Fin (d + 1)) F |
      g ∈ facetStabilizer (range vertex) ∧ ‖(Matrix.GeneralLinearGroup.det g : F)‖ = 1} =
      ⋂ i, ⋃ j, U i j := by
    ext g
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, U, ← mem_detNormOne]
    constructor
    · rintro ⟨hg, hdet⟩ i
      change g • range vertex = range vertex at hg
      have hi : g • vertex i ∈ range vertex := by
        rw [← hg]
        exact smul_mem_smul_set (mem_range_self i)
      obtain ⟨j, hj⟩ := hi
      exact ⟨j, hj.symm, hdet⟩
    · intro hg
      refine ⟨?_, (hg 0).elim fun _ hj => hj.2⟩
      change (MulAction.toPerm g).toEmbedding '' range vertex = range vertex
      apply Set.map_eq_of_subset _ (finite_range vertex)
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      obtain ⟨j, hj, _⟩ := hg i
      exact ⟨j, hj.symm⟩
  change IsCompact _ ∧ IsOpen _
  rw [hset]
  have hcompact (i : Fin (k + 1)) : IsCompact (⋃ j, U i j) := isCompact_iUnion fun j => (hU i j).1
  exact ⟨(hcompact 0).of_isClosed_subset (isClosed_iInter fun i => (hcompact i).isClosed)
    (iInter_subset _ 0), isOpen_iInter_of_finite fun i => isOpen_iUnion fun j => (hU i j).2⟩

end Langlands.Analytic.DrinfeldUpperHalfSpace
