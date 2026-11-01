import Langlands.Group.GL.MirabolicMixedProductSubgroups
import Langlands.Group.GL.Maps
import Langlands.Group.GL.RankReindex
import Langlands.Group.GL.Padic
import Langlands.Representation.Geometric.ClosedSubgroupDefinitions

/-!
# Concrete group data for the mixed mirabolic orbit comparisons

Bernstein–Zelevinsky (1977), §7.2, cases 4.13(b),(c) with source rank `r + 2`:
inside `P_(k+r+3)`, the mixed subgroups are compared with the plus subgroup
`P_(k+r+2) V_(k+r+3)` at the identity and at the source's cyclic permutation
matrices. This file constructs the representatives, stabilizers, coefficient
maps, section and stages subgroups and radical intersections, together with
their continuity and closedness. It proves no orbit enumeration or comparison.
See the paired Markdown for the conventions.
-/

namespace Langlands.GeneralLinear.Mirabolic.MixedOrbit

open Langlands.Geometric
open Langlands.GeneralLinear.Mirabolic.MixedProduct

universe u

/-! ### Rank transport -/

section RankCast

variable {R : Type u} [CommRing R] {m n : ℕ}

private theorem reindex_mem_mirabolic (h : m = n) (g : mirabolic m R) :
    reindex (R := R) (finCongr (congrArg (· + 1) h)) g.val ∈ mirabolic n R := by
  subst h
  intro j
  simpa only [reindex_finCongr_rfl, MulEquiv.refl_apply] using g.property j

private theorem reindex_symm_mem_mirabolic (h : m = n) (g : mirabolic n R) :
    (reindex (R := R) (finCongr (congrArg (· + 1) h))).symm g.val ∈ mirabolic m R := by
  subst h
  intro j
  simpa only [reindex_finCongr_rfl, MulEquiv.refl_symm, MulEquiv.refl_apply] using g.property j

/-- The mirabolic groups of equal ranks, identified entrywise along `Fin.cast`. -/
def rankCast (h : m = n) : mirabolic m R ≃* mirabolic n R where
  toFun g := ⟨reindex (R := R) (finCongr (congrArg (· + 1) h)) g.val,
    reindex_mem_mirabolic h g⟩
  invFun g := ⟨(reindex (R := R) (finCongr (congrArg (· + 1) h))).symm g.val,
    reindex_symm_mem_mirabolic h g⟩
  left_inv g := Subtype.ext ((reindex (R := R) _).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((reindex (R := R) _).apply_symm_apply g.val)
  map_mul' g g' := Subtype.ext (map_mul (reindex (R := R) _) g.val g'.val)

@[simp] theorem rankCast_apply (h : m = n) (g : mirabolic m R) (i j : Fin (n + 1)) :
    (rankCast h g).val.val i j =
      g.val.val (Fin.cast (congrArg (· + 1) h).symm i)
        (Fin.cast (congrArg (· + 1) h).symm j) := rfl

@[simp] theorem rankCast_symm_apply (h : m = n) (g : mirabolic n R) (i j : Fin (m + 1)) :
    ((rankCast h).symm g).val.val i j =
      g.val.val (Fin.cast (congrArg (· + 1) h) i) (Fin.cast (congrArg (· + 1) h) j) := rfl

variable [TopologicalSpace R]

theorem continuous_rankCast (h : m = n) : Continuous (rankCast (R := R) h) :=
  ((continuous_reindex_finCongr (R := R) _).comp continuous_subtype_val).subtype_mk _

theorem continuous_rankCast_symm (h : m = n) : Continuous (rankCast (R := R) h).symm :=
  ((continuous_reindex_finCongr_symm (R := R) _).comp continuous_subtype_val).subtype_mk _

end RankCast

/-- The arithmetic rank equality `(k+1)+(r+1) = k+r+2` of the mirabolic indices. -/
theorem totalRank_eq (k r : ℕ) : k + 1 + (r + 1) = k + r + 2 := by omega

/-! ### Descending cycles and their permutation matrices -/

section Cycle

variable (t a : ℕ) (ha : a ≤ t)

/-- The zero-based cycle on `Fin (t + 2)` sending `a ↦ t` and `j ↦ j - 1` for
`a < j ≤ t`, fixing all other indices, in particular the final index `t + 1`. -/
def descendingCycle : Equiv.Perm (Fin (t + 2)) where
  toFun j := ⟨if j.val = a then t else if a < j.val ∧ j.val ≤ t then j.val - 1 else j.val, by
    split_ifs <;> omega⟩
  invFun i := ⟨if i.val = t then a else if a ≤ i.val ∧ i.val < t then i.val + 1 else i.val, by
    split_ifs <;> omega⟩
  left_inv j := by
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv i := by
    apply Fin.ext
    simp only
    split_ifs <;> omega

theorem descendingCycle_apply_val (j : Fin (t + 2)) :
    (descendingCycle t a ha j).val =
      if j.val = a then t else if a < j.val ∧ j.val ≤ t then j.val - 1 else j.val := rfl

theorem descendingCycle_symm_apply_val (i : Fin (t + 2)) :
    ((descendingCycle t a ha).symm i).val =
      if i.val = t then a else if a ≤ i.val ∧ i.val < t then i.val + 1 else i.val := rfl

theorem descendingCycle_eq_last_iff (j : Fin (t + 2)) :
    descendingCycle t a ha j = Fin.last (t + 1) ↔ j = Fin.last (t + 1) := by
  rw [Fin.ext_iff, Fin.ext_iff, descendingCycle_apply_val, Fin.val_last]
  have := j.isLt
  split_ifs <;> omega

@[simp] theorem descendingCycle_last :
    descendingCycle t a ha (Fin.last (t + 1)) = Fin.last (t + 1) :=
  (descendingCycle_eq_last_iff t a ha _).mpr rfl

/-- The same permutation is the inverse of Mathlib's `Fin.cycleIcc a t`, the
cycle `(a a+1 ... t)`. -/
theorem descendingCycle_eq_inv_cycleIcc :
    descendingCycle t a ha = (Fin.cycleIcc ⟨a, by omega⟩ ⟨t, by omega⟩)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  refine Equiv.ext fun j => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, descendingCycle_apply_val]
  rcases Nat.lt_or_ge j.val a with hja | hja
  · rw [Fin.cycleIcc_of_lt (show j < ⟨a, by omega⟩ from hja)]
    split_ifs <;> omega
  rcases Nat.lt_or_ge t j.val with hjt | hjt
  · rw [Fin.cycleIcc_of_gt (show (⟨t, by omega⟩ : Fin (t + 2)) < j from hjt)]
    split_ifs <;> omega
  rw [Fin.cycleIcc_of_le_of_le (show (⟨a, by omega⟩ : Fin (t + 2)) ≤ j from hja)
    (show j ≤ ⟨t, by omega⟩ from hjt)]
  by_cases hjt' : j = ⟨t, by omega⟩
  · simp only [hjt', ↓reduceIte]
  · have hjt'' : j.val ≠ t := fun h => hjt' (Fin.ext h)
    simp only [hjt', ↓reduceIte]
    rw [Fin.val_add_one_of_lt (show j < Fin.last (t + 1) from by
        rw [Fin.lt_def, Fin.val_last]; omega)]
    split_ifs <;> omega

variable (R : Type u) [CommRing R]

/-- The actual permutation matrix of `descendingCycle`, an element of the
mirabolic group because the final index is fixed. -/
def cycleElement : mirabolic (t + 1) R :=
  ⟨permutation (t + 2) R (descendingCycle t a ha), by
    intro j
    rw [permutation_entry]
    simp only [descendingCycle_eq_last_iff]⟩

/-- Column `j` is the standard basis vector at `descendingCycle j`. -/
theorem cycleElement_entry (i j : Fin (t + 2)) :
    (cycleElement t a ha R).val.val i j = if descendingCycle t a ha j = i then 1 else 0 :=
  permutation_entry _ _ _ _ _

theorem cycleElement_last_row (j : Fin (t + 2)) :
    (cycleElement t a ha R).val.val (Fin.last (t + 1)) j =
      if j = Fin.last (t + 1) then 1 else 0 :=
  (cycleElement t a ha R).property j

theorem cycleElement_last_column (i : Fin (t + 2)) :
    (cycleElement t a ha R).val.val i (Fin.last (t + 1)) =
      if i = Fin.last (t + 1) then 1 else 0 := by
  rw [cycleElement_entry, descendingCycle_last]
  simp only [eq_comm]

end Cycle

/-! ### Stabilizers in the plus subgroup -/

section Orbit

variable {R : Type u} [CommRing R] {t : ℕ} (H : Subgroup (mirabolic (t + 1) R))
  (w : mirabolic (t + 1) R)

theorem mem_orbitStabilizer_iff (q : plusSubgroup t R) :
    q ∈ orbitStabilizer H (plusSubgroup t R) w ↔ w⁻¹ * q.val * w ∈ H := by
  change (MulAut.conj w⁻¹) q.val ∈ H ↔ _
  rw [MulAut.conj_apply, inv_inv]

/-- The stabilizer pulled back along the successor section
`P_(t+1) → P_(t+1) V_(t+2)`. -/
def sectionSubgroup : Subgroup (mirabolic t R) :=
  (orbitStabilizer H (plusSubgroup t R) w).comap plusSuccessor

theorem mem_sectionSubgroup_iff (g : mirabolic t R) :
    g ∈ sectionSubgroup H w ↔ w⁻¹ * successor g * w ∈ H :=
  mem_orbitStabilizer_iff H w (plusSuccessor g)

/-- The section subgroup pulled back along `plusProjection`; it contains the
whole radical of `Q`. -/
def stagesSubgroup : Subgroup (plusSubgroup t R) :=
  (sectionSubgroup H w).comap plusProjection

theorem mem_stagesSubgroup_iff (q : plusSubgroup t R) :
    q ∈ stagesSubgroup H w ↔ w⁻¹ * successor (plusProjection q) * w ∈ H :=
  mem_sectionSubgroup_iff H w (plusProjection q)

/-- The stabilizer's intersection with the radical `V_(t+2)`, as a subgroup of
the actual radical. -/
def radicalIntersection : Subgroup (radical (t + 1) R) :=
  (orbitStabilizer H (plusSubgroup t R) w).comap plusRadical

theorem mem_radicalIntersection_iff (u : radical (t + 1) R) :
    u ∈ radicalIntersection H w ↔ w⁻¹ * u.val * w ∈ H :=
  mem_orbitStabilizer_iff H w (plusRadical u)

/-- The inclusion of the radical intersection into the stabilizer. -/
def radicalInclusion :
    radicalIntersection H w →* orbitStabilizer H (plusSubgroup t R) w :=
  plusRadical.subgroupComap _

@[simp] theorem radicalInclusion_val (u : radicalIntersection H w) :
    ((radicalInclusion H w u).val : mirabolic (t + 1) R) = u.val.val := rfl

section Topology

variable [TopologicalSpace R]

theorem continuous_plusSuccessor : Continuous (plusSuccessor (n := t) (F := R)) :=
  continuous_induced_rng.mpr continuous_successor

theorem continuous_plusRadical : Continuous (plusRadical (n := t) (F := R)) :=
  continuous_induced_rng.mpr continuous_subtype_val

theorem continuous_radicalInclusion : Continuous (radicalInclusion H w) :=
  continuous_induced_rng.mpr (continuous_plusRadical.comp continuous_subtype_val)

variable [IsTopologicalRing R]

theorem continuous_stabilizerToInducing :
    Continuous (stabilizerToInducing H (plusSubgroup t R) w) := by
  refine continuous_induced_rng.mpr ?_
  have hf : ((↑) ∘ stabilizerToInducing H (plusSubgroup t R) w) =
      fun q => w⁻¹ * (q.val : mirabolic (t + 1) R) * w :=
    funext (stabilizerToInducing_apply H (plusSubgroup t R) w)
  rw [hf]
  exact (continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
    continuous_const

variable {H}

theorem orbitStabilizer_isClosed (hH : IsClosed (H : Set (mirabolic (t + 1) R))) :
    IsClosed (orbitStabilizer H (plusSubgroup t R) w : Set (plusSubgroup t R)) := by
  have hset : (orbitStabilizer H (plusSubgroup t R) w : Set (plusSubgroup t R)) =
      (fun q : plusSubgroup t R => w⁻¹ * q.val * w) ⁻¹' H :=
    Set.ext (mem_orbitStabilizer_iff H w)
  rw [hset]
  exact hH.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem sectionSubgroup_isClosed (hH : IsClosed (H : Set (mirabolic (t + 1) R))) :
    IsClosed (sectionSubgroup H w : Set (mirabolic t R)) :=
  (orbitStabilizer_isClosed w hH).preimage continuous_plusSuccessor

theorem stagesSubgroup_isClosed (hH : IsClosed (H : Set (mirabolic (t + 1) R))) :
    IsClosed (stagesSubgroup H w : Set (plusSubgroup t R)) :=
  (sectionSubgroup_isClosed w hH).preimage continuous_plusProjection

theorem radicalIntersection_isClosed (hH : IsClosed (H : Set (mirabolic (t + 1) R))) :
    IsClosed (radicalIntersection H w : Set (radical (t + 1) R)) :=
  (orbitStabilizer_isClosed w hH).preimage continuous_plusRadical

end Topology

end Orbit

/-! ### Case (II): the left mixed subgroup `P_(K, m)` -/

section Left

variable (k r : ℕ) (R : Type u) [CommRing R]

/-- `leftSubgroup (k+1) (r+1)` transported to `G = P_(k+r+3)` along the rank
equality `(k+1)+(r+1) = k+r+2`. -/
def leftInducing : Subgroup (mirabolic (k + r + 2) R) :=
  (leftSubgroup (k + 1) (r + 1) R).comap (rankCast (R := R) (totalRank_eq k r)).symm.toMonoidHom

theorem mem_leftInducing_iff (g : mirabolic (k + r + 2) R) :
    g ∈ leftInducing k r R ↔
      (rankCast (totalRank_eq k r)).symm g ∈ leftSubgroup (k + 1) (r + 1) R :=
  Iff.rfl

/-- The transported subgroup back in the published coordinates. -/
def leftInducingHom : leftInducing k r R →* leftSubgroup (k + 1) (r + 1) R :=
  (rankCast (R := R) (totalRank_eq k r)).symm.toMonoidHom.subgroupComap _

@[simp] theorem leftInducingHom_val (g : leftInducing k r R) :
    (leftInducingHom k r R g).val = (rankCast (totalRank_eq k r)).symm g.val := rfl

/-- The source's case (b) cycle `(K ↦ n-1 ↦ n-2 ↦ ... ↦ K)`, zero-based `k ↦ k+r+1`. -/
def leftCycleElement : mirabolic (k + r + 2) R :=
  cycleElement (k + r + 1) k (by omega) R

theorem leftCycleElement_entry (i j : Fin (k + r + 3)) :
    (leftCycleElement k r R).val.val i j =
      if descendingCycle (k + r + 1) k (by omega) j = i then 1 else 0 :=
  cycleElement_entry _ _ _ R i j

theorem leftCycleElement_last_row (j : Fin (k + r + 3)) :
    (leftCycleElement k r R).val.val (Fin.last (k + r + 2)) j =
      if j = Fin.last (k + r + 2) then 1 else 0 :=
  (leftCycleElement k r R).property j

/-- The cyclic representative first and the identity second. -/
def leftRepresentative : Fin 2 → mirabolic (k + r + 2) R :=
  ![leftCycleElement k r R, 1]

@[simp] theorem leftRepresentative_zero : leftRepresentative k r R 0 = leftCycleElement k r R :=
  rfl

@[simp] theorem leftRepresentative_one : leftRepresentative k r R 1 = 1 := rfl

/-- The stabilizer `Q ∩ w H w⁻¹` of the representative `w`. -/
abbrev leftStabilizer (i : Fin 2) : Subgroup (plusSubgroup (k + r + 1) R) :=
  orbitStabilizer (leftInducing k r R) (plusSubgroup (k + r + 1) R) (leftRepresentative k r R i)

/-- Inverse conjugation into `H`, transported to `leftSubgroup (k+1) (r+1)` and
projected to the coefficient group `GL_(k+1) × P_(r+2)`. -/
def leftCoefficient (i : Fin 2) :
    leftStabilizer k r R i →* GeneralLinear (k + 1) R × mirabolic (r + 1) R :=
  leftProjection.comp ((leftInducingHom k r R).comp
    (stabilizerToInducing (leftInducing k r R) (plusSubgroup (k + r + 1) R)
      (leftRepresentative k r R i)))

theorem leftCoefficient_fst_apply (i : Fin 2) (q : leftStabilizer k r R i) (a b : Fin (k + 1)) :
    (leftCoefficient k r R i q).1.val a b =
      ((leftRepresentative k r R i)⁻¹ * q.val.val * leftRepresentative k r R i).val.val
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (leftIndex (k + 1) (r + 1) (Sum.inl a)))
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (leftIndex (k + 1) (r + 1) (Sum.inl b))) := by
  rw [← stabilizerToInducing_apply (leftInducing k r R) (plusSubgroup (k + r + 1) R)]
  rfl

theorem leftCoefficient_snd_apply (i : Fin 2) (q : leftStabilizer k r R i)
    (a b : Fin (r + 1 + 1)) :
    (leftCoefficient k r R i q).2.val.val a b =
      ((leftRepresentative k r R i)⁻¹ * q.val.val * leftRepresentative k r R i).val.val
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (leftIndex (k + 1) (r + 1) (Sum.inr a)))
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (leftIndex (k + 1) (r + 1) (Sum.inr b))) := by
  rw [← stabilizerToInducing_apply (leftInducing k r R) (plusSubgroup (k + r + 1) R)]
  rfl

/-- The stabilizer pulled back to `P_(k+r+2)` along `plusSuccessor`. -/
abbrev leftSection (i : Fin 2) : Subgroup (mirabolic (k + r + 1) R) :=
  sectionSubgroup (leftInducing k r R) (leftRepresentative k r R i)

/-- The stages subgroup of `Q`, pulled back along `plusProjection`. -/
abbrev leftStages (i : Fin 2) : Subgroup (plusSubgroup (k + r + 1) R) :=
  stagesSubgroup (leftInducing k r R) (leftRepresentative k r R i)

/-- The stabilizer's intersection with the radical `V_(k+r+3)`. -/
abbrev leftRadicalIntersection (i : Fin 2) : Subgroup (radical (k + r + 2) R) :=
  radicalIntersection (leftInducing k r R) (leftRepresentative k r R i)

/-- The inclusion of the radical intersection into the stabilizer. -/
abbrev leftRadicalInclusion (i : Fin 2) :
    leftRadicalIntersection k r R i →* leftStabilizer k r R i :=
  radicalInclusion (leftInducing k r R) (leftRepresentative k r R i)

/-- The radical intersection's map to the coefficient group. -/
def leftRadicalCoefficient (i : Fin 2) :
    leftRadicalIntersection k r R i →* GeneralLinear (k + 1) R × mirabolic (r + 1) R :=
  (leftCoefficient k r R i).comp (leftRadicalInclusion k r R i)

section Topology

variable [TopologicalSpace R]

theorem continuous_leftInducingHom : Continuous (leftInducingHom k r R) :=
  continuous_induced_rng.mpr ((continuous_rankCast_symm _).comp continuous_subtype_val)

theorem continuous_leftRadicalInclusion (i : Fin 2) : Continuous (leftRadicalInclusion k r R i) :=
  continuous_radicalInclusion _ _

variable [IsTopologicalRing R]

theorem continuous_leftCoefficient (i : Fin 2) : Continuous (leftCoefficient k r R i) :=
  continuous_leftProjection.comp
    ((continuous_leftInducingHom k r R).comp (continuous_stabilizerToInducing _ _))

theorem continuous_leftRadicalCoefficient (i : Fin 2) :
    Continuous (leftRadicalCoefficient k r R i) :=
  (continuous_leftCoefficient k r R i).comp (continuous_leftRadicalInclusion k r R i)

variable [T2Space R]

omit [IsTopologicalRing R] in
theorem leftInducing_isClosed : IsClosed (leftInducing k r R : Set (mirabolic (k + r + 2) R)) :=
  leftSubgroup_isClosed.preimage (continuous_rankCast_symm _)

theorem leftStabilizer_isClosed (i : Fin 2) :
    IsClosed (leftStabilizer k r R i : Set (plusSubgroup (k + r + 1) R)) :=
  orbitStabilizer_isClosed _ (leftInducing_isClosed k r R)

theorem leftSection_isClosed (i : Fin 2) :
    IsClosed (leftSection k r R i : Set (mirabolic (k + r + 1) R)) :=
  sectionSubgroup_isClosed _ (leftInducing_isClosed k r R)

theorem leftStages_isClosed (i : Fin 2) :
    IsClosed (leftStages k r R i : Set (plusSubgroup (k + r + 1) R)) :=
  stagesSubgroup_isClosed _ (leftInducing_isClosed k r R)

theorem leftRadicalIntersection_isClosed (i : Fin 2) :
    IsClosed (leftRadicalIntersection k r R i : Set (radical (k + r + 2) R)) :=
  radicalIntersection_isClosed _ (leftInducing_isClosed k r R)

end Topology

end Left

/-! ### Case (III): the right mixed subgroup `P_(m, K)` -/

section Right

variable (k r : ℕ) (R : Type u) [CommRing R]

/-- `rightSubgroup (k+1) (r+1)` transported to `G = P_(k+r+3)` along the rank
equality `(k+1)+(r+1) = k+r+2`. -/
def rightInducing : Subgroup (mirabolic (k + r + 2) R) :=
  (rightSubgroup (k + 1) (r + 1) R).comap (rankCast (R := R) (totalRank_eq k r)).symm.toMonoidHom

theorem mem_rightInducing_iff (g : mirabolic (k + r + 2) R) :
    g ∈ rightInducing k r R ↔
      (rankCast (totalRank_eq k r)).symm g ∈ rightSubgroup (k + 1) (r + 1) R :=
  Iff.rfl

/-- The transported subgroup back in the published coordinates. -/
def rightInducingHom : rightInducing k r R →* rightSubgroup (k + 1) (r + 1) R :=
  (rankCast (R := R) (totalRank_eq k r)).symm.toMonoidHom.subgroupComap _

@[simp] theorem rightInducingHom_val (g : rightInducing k r R) :
    (rightInducingHom k r R g).val = (rankCast (totalRank_eq k r)).symm g.val := rfl

/-- The source's case (c) cycle `(m-1 ↦ n-1 ↦ n-2 ↦ ... ↦ m-1)`, zero-based `r ↦ k+r+1`. -/
def rightCycleElement : mirabolic (k + r + 2) R :=
  cycleElement (k + r + 1) r (by omega) R

theorem rightCycleElement_entry (i j : Fin (k + r + 3)) :
    (rightCycleElement k r R).val.val i j =
      if descendingCycle (k + r + 1) r (by omega) j = i then 1 else 0 :=
  cycleElement_entry _ _ _ R i j

theorem rightCycleElement_last_row (j : Fin (k + r + 3)) :
    (rightCycleElement k r R).val.val (Fin.last (k + r + 2)) j =
      if j = Fin.last (k + r + 2) then 1 else 0 :=
  (rightCycleElement k r R).property j

/-- The cyclic representative first and the identity second. -/
def rightRepresentative : Fin 2 → mirabolic (k + r + 2) R :=
  ![rightCycleElement k r R, 1]

@[simp] theorem rightRepresentative_zero : rightRepresentative k r R 0 = rightCycleElement k r R :=
  rfl

@[simp] theorem rightRepresentative_one : rightRepresentative k r R 1 = 1 := rfl

/-- The stabilizer `Q ∩ w H w⁻¹` of the representative `w`. -/
abbrev rightStabilizer (i : Fin 2) : Subgroup (plusSubgroup (k + r + 1) R) :=
  orbitStabilizer (rightInducing k r R) (plusSubgroup (k + r + 1) R) (rightRepresentative k r R i)

/-- Inverse conjugation into `H`, transported to `rightSubgroup (k+1) (r+1)` and
projected to the coefficient group `P_(r+2) × GL_(k+1)`. -/
def rightCoefficient (i : Fin 2) :
    rightStabilizer k r R i →* mirabolic (r + 1) R × GeneralLinear (k + 1) R :=
  rightProjection.comp ((rightInducingHom k r R).comp
    (stabilizerToInducing (rightInducing k r R) (plusSubgroup (k + r + 1) R)
      (rightRepresentative k r R i)))

theorem rightCoefficient_fst_apply (i : Fin 2) (q : rightStabilizer k r R i)
    (a b : Fin (r + 1 + 1)) :
    (rightCoefficient k r R i q).1.val.val a b =
      ((rightRepresentative k r R i)⁻¹ * q.val.val * rightRepresentative k r R i).val.val
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (rightIndex (k + 1) (r + 1) (Sum.inl a)))
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (rightIndex (k + 1) (r + 1) (Sum.inl b))) := by
  rw [← stabilizerToInducing_apply (rightInducing k r R) (plusSubgroup (k + r + 1) R)]
  rfl

theorem rightCoefficient_snd_apply (i : Fin 2) (q : rightStabilizer k r R i) (a b : Fin (k + 1)) :
    (rightCoefficient k r R i q).2.val a b =
      ((rightRepresentative k r R i)⁻¹ * q.val.val * rightRepresentative k r R i).val.val
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (rightIndex (k + 1) (r + 1) (Sum.inr a)))
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (rightIndex (k + 1) (r + 1) (Sum.inr b))) := by
  rw [← stabilizerToInducing_apply (rightInducing k r R) (plusSubgroup (k + r + 1) R)]
  rfl

/-- The stabilizer pulled back to `P_(k+r+2)` along `plusSuccessor`. -/
abbrev rightSection (i : Fin 2) : Subgroup (mirabolic (k + r + 1) R) :=
  sectionSubgroup (rightInducing k r R) (rightRepresentative k r R i)

/-- The stages subgroup of `Q`, pulled back along `plusProjection`. -/
abbrev rightStages (i : Fin 2) : Subgroup (plusSubgroup (k + r + 1) R) :=
  stagesSubgroup (rightInducing k r R) (rightRepresentative k r R i)

/-- The stabilizer's intersection with the radical `V_(k+r+3)`. -/
abbrev rightRadicalIntersection (i : Fin 2) : Subgroup (radical (k + r + 2) R) :=
  radicalIntersection (rightInducing k r R) (rightRepresentative k r R i)

/-- The inclusion of the radical intersection into the stabilizer. -/
abbrev rightRadicalInclusion (i : Fin 2) :
    rightRadicalIntersection k r R i →* rightStabilizer k r R i :=
  radicalInclusion (rightInducing k r R) (rightRepresentative k r R i)

/-- The radical intersection's map to the coefficient group. -/
def rightRadicalCoefficient (i : Fin 2) :
    rightRadicalIntersection k r R i →* mirabolic (r + 1) R × GeneralLinear (k + 1) R :=
  (rightCoefficient k r R i).comp (rightRadicalInclusion k r R i)

section Topology

variable [TopologicalSpace R]

theorem continuous_rightInducingHom : Continuous (rightInducingHom k r R) :=
  continuous_induced_rng.mpr ((continuous_rankCast_symm _).comp continuous_subtype_val)

theorem continuous_rightRadicalInclusion (i : Fin 2) : Continuous (rightRadicalInclusion k r R i) :=
  continuous_radicalInclusion _ _

variable [IsTopologicalRing R]

theorem continuous_rightCoefficient (i : Fin 2) : Continuous (rightCoefficient k r R i) :=
  continuous_rightProjection.comp
    ((continuous_rightInducingHom k r R).comp (continuous_stabilizerToInducing _ _))

theorem continuous_rightRadicalCoefficient (i : Fin 2) :
    Continuous (rightRadicalCoefficient k r R i) :=
  (continuous_rightCoefficient k r R i).comp (continuous_rightRadicalInclusion k r R i)

variable [T2Space R]

omit [IsTopologicalRing R] in
theorem rightInducing_isClosed : IsClosed (rightInducing k r R : Set (mirabolic (k + r + 2) R)) :=
  rightSubgroup_isClosed.preimage (continuous_rankCast_symm _)

theorem rightStabilizer_isClosed (i : Fin 2) :
    IsClosed (rightStabilizer k r R i : Set (plusSubgroup (k + r + 1) R)) :=
  orbitStabilizer_isClosed _ (rightInducing_isClosed k r R)

theorem rightSection_isClosed (i : Fin 2) :
    IsClosed (rightSection k r R i : Set (mirabolic (k + r + 1) R)) :=
  sectionSubgroup_isClosed _ (rightInducing_isClosed k r R)

theorem rightStages_isClosed (i : Fin 2) :
    IsClosed (rightStages k r R i : Set (plusSubgroup (k + r + 1) R)) :=
  stagesSubgroup_isClosed _ (rightInducing_isClosed k r R)

theorem rightRadicalIntersection_isClosed (i : Fin 2) :
    IsClosed (rightRadicalIntersection k r R i : Set (radical (k + r + 2) R)) :=
  radicalIntersection_isClosed _ (rightInducing_isClosed k r R)

end Topology

end Right

/-! ### The supplied p-adic topology -/

section Padic

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (k r : ℕ)

/-- The supplied topology on `F.Carrier` is a ring topology. -/
theorem isTopologicalRing_of_topologicalData :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  infer_instance

theorem padic_continuous_leftCoefficient (i : Fin 2) :
    letI := T.topology
    Continuous (leftCoefficient k r F.Carrier i) := by
  let := T.topology
  have := isTopologicalRing_of_topologicalData F T
  exact continuous_leftCoefficient k r F.Carrier i

theorem padic_continuous_leftRadicalCoefficient (i : Fin 2) :
    letI := T.topology
    Continuous (leftRadicalCoefficient k r F.Carrier i) := by
  let := T.topology
  have := isTopologicalRing_of_topologicalData F T
  exact continuous_leftRadicalCoefficient k r F.Carrier i

theorem padic_continuous_leftRadicalInclusion (i : Fin 2) :
    letI := T.topology
    Continuous (leftRadicalInclusion k r F.Carrier i) := by
  let := T.topology
  exact continuous_leftRadicalInclusion k r F.Carrier i

theorem padic_leftStabilizer_isClosed (i : Fin 2) :
    letI := T.topology
    IsClosed (leftStabilizer k r F.Carrier i : Set (plusSubgroup (k + r + 1) F.Carrier)) := by
  let := T.topology
  have := T.fieldT2
  have := isTopologicalRing_of_topologicalData F T
  exact leftStabilizer_isClosed k r F.Carrier i

theorem padic_leftSection_isClosed (i : Fin 2) :
    letI := T.topology
    IsClosed (leftSection k r F.Carrier i : Set (mirabolic (k + r + 1) F.Carrier)) := by
  let := T.topology
  have := T.fieldT2
  have := isTopologicalRing_of_topologicalData F T
  exact leftSection_isClosed k r F.Carrier i

theorem padic_leftStages_isClosed (i : Fin 2) :
    letI := T.topology
    IsClosed (leftStages k r F.Carrier i : Set (plusSubgroup (k + r + 1) F.Carrier)) := by
  let := T.topology
  have := T.fieldT2
  have := isTopologicalRing_of_topologicalData F T
  exact leftStages_isClosed k r F.Carrier i

theorem padic_leftRadicalIntersection_isClosed (i : Fin 2) :
    letI := T.topology
    IsClosed (leftRadicalIntersection k r F.Carrier i : Set (radical (k + r + 2) F.Carrier)) := by
  let := T.topology
  have := T.fieldT2
  have := isTopologicalRing_of_topologicalData F T
  exact leftRadicalIntersection_isClosed k r F.Carrier i

theorem padic_continuous_rightCoefficient (i : Fin 2) :
    letI := T.topology
    Continuous (rightCoefficient k r F.Carrier i) := by
  let := T.topology
  have := isTopologicalRing_of_topologicalData F T
  exact continuous_rightCoefficient k r F.Carrier i

theorem padic_continuous_rightRadicalCoefficient (i : Fin 2) :
    letI := T.topology
    Continuous (rightRadicalCoefficient k r F.Carrier i) := by
  let := T.topology
  have := isTopologicalRing_of_topologicalData F T
  exact continuous_rightRadicalCoefficient k r F.Carrier i

theorem padic_continuous_rightRadicalInclusion (i : Fin 2) :
    letI := T.topology
    Continuous (rightRadicalInclusion k r F.Carrier i) := by
  let := T.topology
  exact continuous_rightRadicalInclusion k r F.Carrier i

theorem padic_rightStabilizer_isClosed (i : Fin 2) :
    letI := T.topology
    IsClosed (rightStabilizer k r F.Carrier i : Set (plusSubgroup (k + r + 1) F.Carrier)) := by
  let := T.topology
  have := T.fieldT2
  have := isTopologicalRing_of_topologicalData F T
  exact rightStabilizer_isClosed k r F.Carrier i

theorem padic_rightSection_isClosed (i : Fin 2) :
    letI := T.topology
    IsClosed (rightSection k r F.Carrier i : Set (mirabolic (k + r + 1) F.Carrier)) := by
  let := T.topology
  have := T.fieldT2
  have := isTopologicalRing_of_topologicalData F T
  exact rightSection_isClosed k r F.Carrier i

theorem padic_rightStages_isClosed (i : Fin 2) :
    letI := T.topology
    IsClosed (rightStages k r F.Carrier i : Set (plusSubgroup (k + r + 1) F.Carrier)) := by
  let := T.topology
  have := T.fieldT2
  have := isTopologicalRing_of_topologicalData F T
  exact rightStages_isClosed k r F.Carrier i

theorem padic_rightRadicalIntersection_isClosed (i : Fin 2) :
    letI := T.topology
    IsClosed (rightRadicalIntersection k r F.Carrier i : Set (radical (k + r + 2) F.Carrier)) := by
  let := T.topology
  have := T.fieldT2
  have := isTopologicalRing_of_topologicalData F T
  exact rightRadicalIntersection_isClosed k r F.Carrier i

end Padic

end Langlands.GeneralLinear.Mirabolic.MixedOrbit
