import Langlands.Representation.LevelZero.Admissible
import Langlands.Representation.Unramified.MinusculeCosets

/-!
# The pro-unipotent radical of the standard Iwahori subgroup of `GL_{m+1}`

Let `F` have valuation ring `𝒪`, maximal ideal `𝔭` and residue field `k`. The standard
Iwahori order `𝔄 ⊆ M_{m+1}(𝒪)` consists of integral matrices whose entries strictly below
the diagonal lie in `𝔭`. Its Jacobson radical `𝔓` consists of integral matrices whose
entries on and below the diagonal lie in `𝔭`. The pro-unipotent radical of the standard
Iwahori subgroup is `I⁺ = 1 + 𝔓` (see `Subgroup`).

For `ϖ : Fˣ` and `ρ = finRotate (m + 1)`, the cyclic coordinate `a_i(Y) = coord ϖ Y i` applies
`resOf` to `Y i (ρ i)` at `i ≠ last` and to `ϖ⁻¹ Y last 0` at `i = last`. The function `resOf`
takes the residue of an integral argument and gives `0` on nonintegral arguments.

When `ϖ` is a uniformizer (`Iwasawa.IsUniformizingElement`), the weighted entries are
integral on `𝔓`, and the coordinates satisfy `a_i(M Y N) = M̄_{ii} a_i(Y) N̄_{ρ i, ρ i}`
for `M, N ∈ 𝔄` and `Y ∈ 𝔓`. They are additive on `𝔓` and vanish on products of two
elements of `𝔓`. Thus `g ↦ (a_i(g - 1))_i` is a homomorphism from `I⁺` to the additive
group of `k^{m+1}`.

For this uniformizer and `m ≥ 1`, the coordinates on `𝔓` are the affine simple coordinates,
at positions `(i, i + 1)` for `i < m` and `(m, 0)`. Knightly–Li (Section 2, (2.1)–(2.2))
use this matrix formula for `GL_n`. Gross–Reeder (Section 9.2) define affine generic
characters through the simple affine root quotients for split simply connected almost
simple groups. For `m = 0` the root system of `GL_1` is empty and the only index is fixed
by `ρ`. The coordinate on `I⁺ = 1 + 𝔭` is the principal-unit map
`g ↦ a_0(g - 1) = res(ϖ⁻¹ (g - 1))` to `k`, with kernel `1 + 𝔭²`.
-/

noncomputable section

open Filter Topology

namespace Langlands.AffineGeneric

open ValuativeRel Matrix LevelZero

universe u

variable {F : Type u} [Field F] [ValuativeRel F]

/-- The residue field of `F`. -/
abbrev Residue (F : Type u) [Field F] [ValuativeRel F] : Type u :=
  IsLocalRing.ResidueField (integers F)

/-! ### Valuation helpers -/

theorem val_mul_le_one {x y : F} (hx : valuation F x ≤ 1) (hy : valuation F y ≤ 1) :
    valuation F (x * y) ≤ 1 := by
  rw [map_mul]
  exact mul_le_one' hx hy

theorem val_mul_lt_one_left {x y : F} (hx : valuation F x < 1) (hy : valuation F y ≤ 1) :
    valuation F (x * y) < 1 := by
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hx

theorem val_mul_lt_one_right {x y : F} (hx : valuation F x ≤ 1) (hy : valuation F y < 1) :
    valuation F (x * y) < 1 := by
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) hy

/-! ### Residues of elements of `F` -/

/-- The residue class of an integral element of `F`, and `0` for a nonintegral element. -/
def resOf (x : F) : Residue F :=
  if h : valuation F x ≤ 1 then
    IsLocalRing.residue (integers F) ⟨x, (Valuation.mem_integer_iff _ _).mpr h⟩
  else 0

theorem resOf_of_le_one {x : F} (h : valuation F x ≤ 1) :
    resOf x = IsLocalRing.residue (integers F) ⟨x, (Valuation.mem_integer_iff _ _).mpr h⟩ := by
  simp only [resOf, h, ↓reduceDIte]

theorem resOf_of_not_le_one {x : F} (h : ¬ valuation F x ≤ 1) : resOf x = 0 := by
  simp only [resOf, h, ↓reduceDIte]

theorem resOf_coe (a : integers F) : resOf (a : F) = IsLocalRing.residue (integers F) a := by
  rw [resOf_of_le_one ((Valuation.mem_integer_iff _ _).mp a.2)]

theorem resOf_add {x y : F} (hx : valuation F x ≤ 1) (hy : valuation F y ≤ 1) :
    resOf (x + y) = resOf x + resOf y := by
  rw [resOf_of_le_one hx, resOf_of_le_one hy,
    resOf_of_le_one ((valuation F).map_add_le hx hy), ← map_add]
  rfl

theorem resOf_mul {x y : F} (hx : valuation F x ≤ 1) (hy : valuation F y ≤ 1) :
    resOf (x * y) = resOf x * resOf y := by
  rw [resOf_of_le_one hx, resOf_of_le_one hy, resOf_of_le_one (val_mul_le_one hx hy),
    ← map_mul]
  rfl

theorem resOf_eq_zero_iff {x : F} (hx : valuation F x ≤ 1) :
    resOf x = 0 ↔ valuation F x < 1 := by
  rw [resOf_of_le_one hx, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]

theorem resOf_of_lt_one {x : F} (hx : valuation F x < 1) : resOf x = 0 :=
  (resOf_eq_zero_iff hx.le).mpr hx

theorem resOf_add_of_lt_one {x y : F} (hx : valuation F x ≤ 1) (hy : valuation F y < 1) :
    resOf (x + y) = resOf x := by
  rw [resOf_add hx hy.le, resOf_of_lt_one hy, add_zero]

@[simp] theorem resOf_zero : resOf (0 : F) = 0 :=
  resOf_of_lt_one (by simp)

@[simp] theorem resOf_one : resOf (1 : F) = 1 := by
  simpa using resOf_coe (1 : integers F)

theorem resOf_neg {x : F} (hx : valuation F x ≤ 1) : resOf (-x) = -resOf x := by
  have hnx : valuation F (-x) ≤ 1 := by rwa [Valuation.map_neg]
  have h := resOf_add hx hnx
  rw [add_neg_cancel, resOf_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem resOf_sum {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, valuation F (f i) ≤ 1) :
    resOf (∑ i ∈ s, f i) = ∑ i ∈ s, resOf (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      resOf_add (hf a (Finset.mem_insert_self a s))
        ((valuation F).map_sum_le fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem exists_resOf_eq (t : Residue F) : ∃ x : F, valuation F x ≤ 1 ∧ resOf x = t := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective t
  exact ⟨a, (Valuation.mem_integer_iff _ _).mp a.2, resOf_coe a⟩

/-- An integral element with nonzero residue has valuation one. -/
theorem val_eq_one_of_resOf_ne_zero {x : F} (hx : valuation F x ≤ 1) (h : resOf x ≠ 0) :
    valuation F x = 1 :=
  le_antisymm hx (not_lt.mp fun hlt => h (resOf_of_lt_one hlt))

section Topology

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem setOf_val_sub_lt_one_mem_nhds (x : F) :
    {y : F | valuation F (y - x) < 1} ∈ 𝓝 x := by
  have hB : {z : F | valuation F z < 1} ∈ 𝓝 (0 : F) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun z hz => by simpa using hz⟩
  have hc : Continuous fun y : F => y - x := continuous_id.sub continuous_const
  have h := hc.continuousAt (x := x)
  rw [ContinuousAt, sub_self] at h
  exact h hB

/-- The residue map is locally constant on `F`. -/
theorem resOf_eventuallyEq (x : F) : ∀ᶠ y in 𝓝 x, resOf y = resOf x := by
  filter_upwards [setOf_val_sub_lt_one_mem_nhds x] with y hy
  have hy' : y = x + (y - x) := by ring
  by_cases hx : valuation F x ≤ 1
  · rw [hy', resOf_add_of_lt_one hx hy]
  · have hlt : valuation F (y - x) < valuation F x := lt_of_lt_of_le hy (not_le.mp hx).le
    have hval : valuation F y = valuation F x := by
      rw [hy']
      exact Valuation.map_add_eq_of_lt_left _ hlt
    rw [resOf_of_not_le_one hx, resOf_of_not_le_one (by rwa [hval])]

end Topology

/-! ### The Iwahori order and its radical -/

variable {m : ℕ}

/-- The standard Iwahori order: integral matrices whose entries strictly below the diagonal
lie in the maximal ideal. -/
def IsIwahoriOrder (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) : Prop :=
  ∀ i j, valuation F (M i j) ≤ 1 ∧ (j < i → valuation F (M i j) < 1)

/-- The Jacobson radical of the standard Iwahori order: integral matrices whose entries on and
below the diagonal lie in the maximal ideal. -/
def IsIwahoriRadical (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) : Prop :=
  ∀ i j, valuation F (M i j) ≤ 1 ∧ (j ≤ i → valuation F (M i j) < 1)

theorem IsIwahoriRadical.isIwahoriOrder {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) : IsIwahoriOrder Y :=
  fun i j => ⟨(hY i j).1, fun h => (hY i j).2 h.le⟩

theorem isIwahoriOrder_one : IsIwahoriOrder (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  intro i j
  refine ⟨?_, fun h => ?_⟩
  · rw [Matrix.one_apply]
    split_ifs <;> simp
  · rw [Matrix.one_apply_ne (ne_of_gt h)]
    simp

theorem isIwahoriRadical_zero : IsIwahoriRadical (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
  fun i j => ⟨by simp, fun _ => by simp⟩

theorem IsIwahoriRadical.add {Y Z : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) (hZ : IsIwahoriRadical Z) : IsIwahoriRadical (Y + Z) :=
  fun i j => ⟨(valuation F).map_add_le (hY i j).1 (hZ i j).1,
    fun h => (valuation F).map_add_lt ((hY i j).2 h) ((hZ i j).2 h)⟩

theorem IsIwahoriRadical.neg {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) : IsIwahoriRadical (-Y) :=
  fun i j => ⟨by simpa using (hY i j).1, fun h => by simpa using (hY i j).2 h⟩

theorem IsIwahoriRadical.smul {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) {c : F} (hc : valuation F c ≤ 1) : IsIwahoriRadical (c • Y) :=
  fun i j => ⟨by simpa using val_mul_le_one hc (hY i j).1,
    fun h => by simpa using val_mul_lt_one_right hc ((hY i j).2 h)⟩

theorem IsIwahoriOrder.mul {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hM : IsIwahoriOrder M) (hN : IsIwahoriOrder N) : IsIwahoriOrder (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  refine ⟨(valuation F).map_sum_le fun p _ => val_mul_le_one (hM i p).1 (hN p j).1,
    fun hji => (valuation F).map_sum_lt one_ne_zero fun p _ => ?_⟩
  rcases lt_or_ge p i with hp | hp
  · exact val_mul_lt_one_left ((hM i p).2 hp) (hN p j).1
  · exact val_mul_lt_one_right (hM i p).1 ((hN p j).2 (lt_of_lt_of_le hji hp))

theorem IsIwahoriOrder.mul_radical {M Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hM : IsIwahoriOrder M) (hY : IsIwahoriRadical Y) : IsIwahoriRadical (M * Y) := by
  intro i j
  rw [Matrix.mul_apply]
  refine ⟨(valuation F).map_sum_le fun p _ => val_mul_le_one (hM i p).1 (hY p j).1,
    fun hji => (valuation F).map_sum_lt one_ne_zero fun p _ => ?_⟩
  rcases lt_or_ge p i with hp | hp
  · exact val_mul_lt_one_left ((hM i p).2 hp) (hY p j).1
  · exact val_mul_lt_one_right (hM i p).1 ((hY p j).2 (le_trans hji hp))

theorem IsIwahoriRadical.mul_order {Y N : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) (hN : IsIwahoriOrder N) : IsIwahoriRadical (Y * N) := by
  intro i j
  rw [Matrix.mul_apply]
  refine ⟨(valuation F).map_sum_le fun p _ => val_mul_le_one (hY i p).1 (hN p j).1,
    fun hji => (valuation F).map_sum_lt one_ne_zero fun p _ => ?_⟩
  rcases le_or_gt p i with hp | hp
  · exact val_mul_lt_one_left ((hY i p).2 hp) (hN p j).1
  · exact val_mul_lt_one_right (hY i p).1 ((hN p j).2 (lt_of_le_of_lt hji hp))

/-- The residues of the diagonal entries are multiplicative on the Iwahori order. -/
theorem IsIwahoriOrder.resOf_mul_diag {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hM : IsIwahoriOrder M) (hN : IsIwahoriOrder N) (i : Fin (m + 1)) :
    resOf ((M * N) i i) = resOf (M i i) * resOf (N i i) := by
  classical
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  rw [resOf_add_of_lt_one (val_mul_le_one (hM i i).1 (hN i i).1), resOf_mul (hM i i).1 (hN i i).1]
  refine (valuation F).map_sum_lt one_ne_zero fun p hp => ?_
  have hpi : p ≠ i := Finset.ne_of_mem_erase hp
  rcases lt_or_gt_of_ne hpi with h | h
  · exact val_mul_lt_one_left ((hM i p).2 h) (hN p i).1
  · exact val_mul_lt_one_right (hM i p).1 ((hN p i).2 h)

/-! ### Cyclic coordinates -/

variable (ϖ : Fˣ)

/-- The weight of the `i`-th cyclic coordinate: `ϖ⁻¹` at the last index, `1` elsewhere. -/
def weight (i : Fin (m + 1)) : F :=
  if i = Fin.last m then (ϖ : F)⁻¹ else 1

/-- The cyclic coordinate `a_i(Y)` applies `resOf` to `Y i (i + 1)` for `i ≠ last` and to
`ϖ⁻¹ Y last 0` for `i = last`. For a uniformizer `ϖ` and `m ≥ 1` these are the affine simple
coordinates on `𝔓`. For `m = 0` the formula is `resOf (ϖ⁻¹ Y 0 0)`. -/
def coord (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (i : Fin (m + 1)) : Residue F :=
  resOf (weight ϖ i * Y i (finRotate (m + 1) i))

variable {ϖ}

theorem finRotate_val_of_ne_last {i : Fin (m + 1)} (h : i ≠ Fin.last m) :
    (finRotate (m + 1) i : ℕ) = i + 1 :=
  coe_finRotate_of_ne_last h

theorem lt_finRotate_of_ne_last {i : Fin (m + 1)} (h : i ≠ Fin.last m) :
    i < finRotate (m + 1) i := by
  rw [Fin.lt_def, finRotate_val_of_ne_last h]
  omega

variable (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement (valuation F) ϖ)
include hϖ

theorem val_le_uniformizer {x : F} (hx : valuation F x < 1) : valuation F x ≤ valuation F (ϖ : F) :=
  Unramified.MinusculeCosets.le_of_lt_one hϖ hx

theorem val_inv_mul_le_one {x : F} (hx : valuation F x < 1) :
    valuation F ((ϖ : F)⁻¹ * x) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp (Unramified.MinusculeCosets.inv_mul_mem_of_lt_one hϖ hx)

theorem val_inv_mul_mul_lt_one {x y : F} (hx : valuation F x < 1) (hy : valuation F y < 1) :
    valuation F ((ϖ : F)⁻¹ * (x * y)) < 1 := by
  rw [← mul_assoc]
  exact val_mul_lt_one_right (val_inv_mul_le_one hϖ hx) hy

/-- For a uniformizer `ϖ`, the weighted entry defining a coordinate is integral on `𝔓`. -/
theorem val_weight_mul_le_one {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) (i : Fin (m + 1)) :
    valuation F (weight ϖ i * Y i (finRotate (m + 1) i)) ≤ 1 := by
  unfold weight
  split_ifs with h
  · subst h
    exact val_inv_mul_le_one hϖ ((hY _ _).2 (Fin.le_last _))
  · rw [one_mul]
    exact (hY _ _).1

theorem coord_add {Y Z : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) (hZ : IsIwahoriRadical Z) (i : Fin (m + 1)) :
    coord ϖ (Y + Z) i = coord ϖ Y i + coord ϖ Z i := by
  unfold coord
  rw [Matrix.add_apply, mul_add]
  exact resOf_add (val_weight_mul_le_one hϖ hY i) (val_weight_mul_le_one hϖ hZ i)

theorem coord_smul {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) {c : F} (hc : valuation F c ≤ 1) (i : Fin (m + 1)) :
    coord ϖ (c • Y) i = resOf c * coord ϖ Y i := by
  unfold coord
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm]
  exact resOf_mul hc (val_weight_mul_le_one hϖ hY i)

/-- For a uniformizer `ϖ`, left multiplication by the Iwahori order scales a coordinate
on `𝔓` by a diagonal residue. -/
theorem coord_order_mul {M Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hM : IsIwahoriOrder M) (hY : IsIwahoriRadical Y) (i : Fin (m + 1)) :
    coord ϖ (M * Y) i = resOf (M i i) * coord ϖ Y i := by
  classical
  unfold coord
  set j := finRotate (m + 1) i
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), mul_add,
    mul_left_comm]
  rw [resOf_add_of_lt_one (val_mul_le_one (hM i i).1 (val_weight_mul_le_one hϖ hY i)),
    resOf_mul (hM i i).1 (val_weight_mul_le_one hϖ hY i)]
  rw [Finset.mul_sum]
  refine (valuation F).map_sum_lt one_ne_zero fun p hp => ?_
  have hpi : p ≠ i := Finset.ne_of_mem_erase hp
  unfold weight
  split_ifs with hi
  · -- the corner coordinate: both factors lie in the maximal ideal
    subst hi
    have hj : j = 0 := finRotate_last
    have hMp : valuation F (M (Fin.last m) p) < 1 :=
      (hM _ _).2 (lt_of_le_of_ne (Fin.le_last p) hpi)
    have hYp : valuation F (Y p j) < 1 := (hY _ _).2 (by rw [hj]; exact Fin.zero_le _)
    exact val_inv_mul_mul_lt_one hϖ hMp hYp
  · rw [one_mul]
    rcases lt_or_gt_of_ne hpi with h | h
    · exact val_mul_lt_one_left ((hM i p).2 h) (hY p j).1
    · have hjp : j ≤ p := by
        rw [Fin.le_def, finRotate_val_of_ne_last hi]
        exact h
      exact val_mul_lt_one_right (hM i p).1 ((hY p j).2 hjp)

/-- For a uniformizer `ϖ`, right multiplication by the Iwahori order scales a coordinate
on `𝔓` by a diagonal residue. -/
theorem coord_mul_order {Y N : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) (hN : IsIwahoriOrder N) (i : Fin (m + 1)) :
    coord ϖ (Y * N) i = coord ϖ Y i * resOf (N (finRotate (m + 1) i) (finRotate (m + 1) i)) := by
  classical
  unfold coord
  set j := finRotate (m + 1) i
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), mul_add, ← mul_assoc]
  rw [resOf_add_of_lt_one (val_mul_le_one (val_weight_mul_le_one hϖ hY i) (hN j j).1),
    resOf_mul (val_weight_mul_le_one hϖ hY i) (hN j j).1]
  rw [Finset.mul_sum]
  refine (valuation F).map_sum_lt one_ne_zero fun q hq => ?_
  have hqj : q ≠ j := Finset.ne_of_mem_erase hq
  unfold weight
  split_ifs with hi
  · subst hi
    have hj : j = 0 := finRotate_last
    have hYq : valuation F (Y (Fin.last m) q) < 1 := (hY _ _).2 (Fin.le_last q)
    have hNq : valuation F (N q j) < 1 := (hN _ _).2 (by
      rw [hj] at hqj ⊢
      exact lt_of_le_of_ne (Fin.zero_le q) (Ne.symm hqj))
    exact val_inv_mul_mul_lt_one hϖ hYq hNq
  · rw [one_mul]
    have hj : (j : ℕ) = i + 1 := finRotate_val_of_ne_last hi
    rcases lt_or_gt_of_ne hqj with h | h
    · have hqi : q ≤ i := by
        rw [Fin.le_def]
        rw [Fin.lt_def, hj] at h
        omega
      exact val_mul_lt_one_left ((hY i q).2 hqi) (hN q j).1
    · exact val_mul_lt_one_right (hY i q).1 ((hN q j).2 h)

/-- For a uniformizer `ϖ`, the coordinates vanish on products of two radical matrices. -/
theorem coord_mul_radical {Y Z : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) (hZ : IsIwahoriRadical Z) (i : Fin (m + 1)) :
    coord ϖ (Y * Z) i = 0 := by
  rw [coord_mul_order hϖ hY hZ.isIwahoriOrder i,
    resOf_of_lt_one ((hZ _ _).2 le_rfl), mul_zero]

end Langlands.AffineGeneric
