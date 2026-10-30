import Langlands.Representation.RankinSelberg.RankOneQuotient
import Langlands.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonSupport
import Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.Representation.RankinSelberg.CharacterChange
import Langlands.Representation.Unramified.MinusculeCosets
import Langlands.Representation.Conductor.SphericalIntegrals
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.LocalField.Normalization.Continuity
import Langlands.Representation.GodementJacquet.Zeta

/-!
# Every reduced rank-one value is a matrix–Whittaker value

For `σ` smooth on `GL_(m+2)` over a p-adic field and a model function `W` of a
standard functional, the indicator `Φ₀` of an explicit compact open box of
matrices gives `Z(Φ₀, s + (m+1)/2, W) = C · Ψ(s, W)` with a constant `C > 0`
independent of `s`, whenever the `GL₁` integral
`Ψ(s, W) = ∫ W(diag(det g, 1, …, 1)) |det g|^(s - (m+1)/2) dg` converges
absolutely; the matrix integral then converges absolutely as well.
-/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg.RankOneBox

open GeneralLinear HarmonicAnalysis Whittaker Conductor RankOneIwasawa
open UnequalRankMirabolicUnitTest

universe uF uV

section Algebra

variable {E : Type*} [Field E]

theorem parameter_mul_comm {n : ℕ} (b c : Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) :
    b * c = c * b :=
  Prod.ext (rankOne_mul_comm b.1 c.1) (funext fun i => mul_comm (b.2 i) (c.2 i))

/-- Right translation in the parameters: `point (rshift x₀ x) = point x * point x₀`. -/
def rshift {n : ℕ}
    (x₀ x : (Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) × upperUnipotent (n + 1) E) :
    (Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) × upperUnipotent (n + 1) E :=
  (x.1 * x₀.1, x.2 * diagonalConj (torusCoord n x.1) x₀.2)

theorem point_rshift {n : ℕ}
    (x₀ x : (Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) × upperUnipotent (n + 1) E) :
    point (rshift x₀ x) = point x * point x₀ := by
  simp only [point, rshift, diagonalConj_val, map_mul, Subgroup.coe_mul]
  group

/-- Every upper triangular invertible matrix is a parametrization point. -/
theorem exists_point_eq {n : ℕ} (b : Langlands.GeneralLinear (n + 1) E)
    (hb : b.val.IsUpperTriangular) :
    ∃ x : (Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) × upperUnipotent (n + 1) E,
      point x = b := by
  have hd : ∀ i, b i i ≠ 0 := by
    intro i h0
    apply Matrix.GeneralLinearGroup.det_ne_zero b
    rw [Matrix.det_of_isUpperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  set d : Fin (n + 1) → Eˣ := fun i => Units.mk0 (b i i) (hd i) with hdd
  have hval : (b * (Iwasawa.diagonalUnits d)⁻¹).val =
      b.val * Matrix.diagonal fun i => (b i i)⁻¹ := by
    rw [Units.val_mul, ← map_inv, Iwasawa.diagonalUnits_val]
    congr 1
  have hu : b * (Iwasawa.diagonalUnits d)⁻¹ ∈ upperUnipotent (n + 1) E := by
    refine ⟨?_, fun i => ?_⟩
    · rw [hval]
      exact hb.mul (Matrix.blockTriangular_diagonal _)
    · change (b * (Iwasawa.diagonalUnits d)⁻¹).val i i = 1
      rw [hval, Matrix.mul_diagonal, mul_inv_cancel₀ (hd i)]
  refine ⟨(torusSection d, ⟨_, hu⟩), ?_⟩
  simp only [point, torusCoord_torusSection, inv_mul_cancel_right]

/-- The inverse of a parametrization point is upper triangular. -/
theorem point_inv_isUpperTriangular {n : ℕ}
    (x : (Langlands.GeneralLinear (0 + 1) E × (Fin n → Eˣ)) × upperUnipotent (n + 1) E) :
    ((point x)⁻¹).val.IsUpperTriangular := by
  rw [point, mul_inv_rev, Units.val_mul, ← map_inv, Iwasawa.diagonalUnits_val]
  exact (Matrix.blockTriangular_diagonal _).mul (inv_mem x.2.property).1

/-- The torus coordinate splits as the rank-one part times `diag((∏ t)⁻¹, t)`. -/
theorem diagonalUnits_torusCoord {n : ℕ} (g : Langlands.GeneralLinear (0 + 1) E)
    (t : Fin n → Eˣ) :
    Iwasawa.diagonalUnits (torusCoord n (g, t)) =
      Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det g) 1) *
        Iwasawa.diagonalUnits (Fin.cons (∏ i, t i)⁻¹ t) := by
  rw [← map_mul]
  congr 1
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ i => simp

end Algebra

section Box

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2

local notation "𝓛" => F.canonicalTopologicalData.additiveLattice

variable {n : ℕ}

/-- The entry sets of the box: `𝓛 A` at `(0,0)`, `𝓛 q` in the rest of row `0`, and
`δᵢⱼ + 𝔪ᵃ` in the other rows. -/
def boxEntry (A q : ℤ) (a : ℕ) (i j : Fin (n + 1)) : Set F.Carrier :=
  if i = 0 then (if j = 0 then (𝓛 A : Set F.Carrier) else (𝓛 q : Set F.Carrier))
  else {z | z - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j ∈ levelSet F.Carrier a}

/-- The compact open box of matrices. -/
def box (A q : ℤ) (a : ℕ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
  {X | ∀ i j, X i j ∈ boxEntry F A q a i j}

theorem mem_box_iff {A q : ℤ} {a : ℕ} (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    X ∈ box F A q a ↔ X 0 0 ∈ 𝓛 A ∧ (∀ j, j ≠ 0 → X 0 j ∈ 𝓛 q) ∧
      ∀ i, i ≠ 0 → ∀ j,
        X i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j ∈ levelSet F.Carrier a := by
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_, fun i hi j => ?_⟩
    · have h00 := h 0 0
      rw [boxEntry, ite_eq_left rfl, ite_eq_left rfl] at h00
      exact h00
    · have h0j := h 0 j
      rw [boxEntry, ite_eq_left rfl, ite_eq_right hj] at h0j
      exact h0j
    · have hij := h i j
      rw [boxEntry, ite_eq_right hi] at hij
      exact hij
  · rintro ⟨h0, h1, h2⟩ i j
    rw [boxEntry]
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · subst hj
        rw [ite_eq_left rfl, ite_eq_left rfl]
        exact h0
      · rw [ite_eq_left rfl, ite_eq_right hj]
        exact h1 j hj
    · rw [ite_eq_right hi]
      exact h2 i hi j

theorem isOpen_boxEntry (A q : ℤ) (a : ℕ) (i j : Fin (n + 1)) :
    IsOpen (boxEntry F A q a i j) := by
  unfold boxEntry
  split_ifs
  · exact isOpen_lattice F A
  · exact isOpen_lattice F q
  · exact (isOpen_levelSet a).preimage (continuous_id.sub continuous_const)

theorem isCompact_boxEntry (A q : ℤ) (a : ℕ) (i j : Fin (n + 1)) :
    IsCompact (boxEntry F A q a i j) := by
  unfold boxEntry
  split_ifs
  · exact isCompact_lattice F A
  · exact isCompact_lattice F q
  · exact (Homeomorph.subRight ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j)).isCompact_preimage.2
      (isCompact_levelSet a)

theorem box_eq_pi (A q : ℤ) (a : ℕ) :
    box F A q a = Set.univ.pi fun i => Set.univ.pi fun j => boxEntry F (n := n) A q a i j := by
  ext X
  constructor
  · intro h i _ j _
    exact h i j
  · intro h i j
    exact h i (Set.mem_univ _) j (Set.mem_univ _)

theorem isOpen_box (A q : ℤ) (a : ℕ) : IsOpen (box F (n := n) A q a) := by
  rw [box_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun i _ =>
    isOpen_set_pi Set.finite_univ fun j _ => isOpen_boxEntry F A q a i j

theorem isCompact_box (A q : ℤ) (a : ℕ) : IsCompact (box F (n := n) A q a) := by
  rw [box_eq_pi]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_boxEntry F A q a i j

theorem one_mem_box {A q : ℤ} {a : ℕ} (hA : 0 ≤ A) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) ∈ box F A q a := by
  rw [mem_box_iff]
  refine ⟨?_, fun j hj => ?_, fun i _ j => ?_⟩
  · rw [Matrix.one_apply_eq]
    exact lattice_mono F hA (one_mem_lattice_zero F)
  · rw [Matrix.one_apply_ne (Ne.symm hj)]
    exact zero_mem _
  · rw [sub_self]
    exact zero_mem_levelSet a

theorem integer_of_mem_principalLevel {a : ℕ} {y : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hy : y ∈ principalLevelSubgroup F.Carrier n a) (i j : Fin (n + 1)) :
    y.val i j ∈ (ValuativeRel.valuation F.Carrier).integer :=
  mem_integer_of_sub_one_mem_levelSet (((mem_principalLevelSubgroup_iff y).1 hy).1 i j)

theorem principalLevel_le_integral (a : ℕ) :
    principalLevelSubgroup F.Carrier n a ≤
      integralSubgroup (ValuativeRel.valuation F.Carrier).integer n := by
  intro y hy
  rw [Conductor.mem_integralSubgroup]
  exact ⟨integer_of_mem_principalLevel F hy, integer_of_mem_principalLevel F (inv_mem hy)⟩

/-- Right multiplication by the principal level keeps the box, when the first row of
the level is small enough. -/
theorem mul_mem_box {A q : ℤ} {a : ℕ} (hA : 0 ≤ A) (hq : q ≤ 0)
    {X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier} (hX : X ∈ box F A q a)
    {y : Langlands.GeneralLinear (n + 1) F.Carrier} (hy : y ∈ principalLevelSubgroup F.Carrier n a)
    (hy0 : ∀ j, j ≠ 0 → y.val 0 j ∈ 𝓛 (q - A)) : X * y.val ∈ box F A q a := by
  obtain ⟨h0, h1, h2⟩ := (mem_box_iff F X).1 hX
  have hyO : ∀ i j, y.val i j ∈ 𝓛 0 := fun i j =>
    (mem_lattice_zero_iff F _).2 (integer_of_mem_principalLevel F hy i j)
  rw [mem_box_iff]
  refine ⟨?_, fun j hj => ?_, fun i hi j => ?_⟩
  · rw [Matrix.mul_apply]
    refine AddSubgroup.sum_mem _ fun l _ => ?_
    by_cases hl : l = 0
    · subst hl
      have h := lattice_mul F h0 (hyO 0 0)
      rwa [add_zero] at h
    · exact lattice_mono F (by omega) (lattice_mul F (h1 l hl) (hyO l 0))
  · rw [Matrix.mul_apply]
    refine AddSubgroup.sum_mem _ fun l _ => ?_
    by_cases hl : l = 0
    · subst hl
      have h := lattice_mul F h0 (hy0 j hj)
      rwa [add_sub_cancel] at h
    · have h := lattice_mul F (h1 l hl) (hyO l j)
      rwa [add_zero] at h
  · have hXy : X * y.val = (X - 1) * y.val + y.val := by
      rw [Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]
    rw [hXy, Matrix.add_apply, add_sub_assoc]
    refine add_mem_levelSet ?_ (((mem_principalLevelSubgroup_iff y).1 hy).1 i j)
    rw [Matrix.mul_apply]
    exact sum_mem_levelSet _ fun l _ =>
      mul_mem_levelSet (by rw [Matrix.sub_apply]; exact h2 i hi l)
        (integer_of_mem_principalLevel F hy l j)

theorem mul_mem_box_iff {A q : ℤ} {a : ℕ} (hA : 0 ≤ A) (hq : q ≤ 0)
    (hL : ∀ y ∈ principalLevelSubgroup F.Carrier n a, ∀ j, j ≠ 0 → y.val 0 j ∈ 𝓛 (q - A))
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)
    {y : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hy : y ∈ principalLevelSubgroup F.Carrier n a) :
    X * y.val ∈ box F A q a ↔ X ∈ box F A q a := by
  refine ⟨fun h => ?_, fun h => mul_mem_box F hA hq h hy (hL y hy)⟩
  have h' := mul_mem_box F hA hq h (inv_mem hy) (hL _ (inv_mem hy))
  rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h'

/-- An invertible matrix of the box is upper triangular after removing a principal
level element on the right. -/
theorem exists_mem_principalLevel_mul_inv_upper {A q : ℤ} {a : ℕ} (ha : 0 < a)
    {g : Langlands.GeneralLinear (n + 1) F.Carrier} (hg : g.val ∈ box F A q a) :
    ∃ y ∈ principalLevelSubgroup F.Carrier n a, (g * y⁻¹).val.IsUpperTriangular := by
  classical
  set Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier := fun i j =>
    if i = 0 then (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j else g.val i j with hY
  have hYl : ∀ i l, Y i l - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i l ∈
      levelSet F.Carrier a := by
    intro i l
    by_cases hi : i = 0
    · simp only [hY, ite_eq_left hi, sub_self]
      exact zero_mem_levelSet a
    · simp only [hY, ite_eq_right hi]
      exact ((mem_box_iff F _).1 hg).2.2 i hi l
  obtain ⟨y, hy, hyY⟩ := exists_mem_principalLevelSubgroup ha Y hYl
  refine ⟨y, hy, ?_⟩
  intro i j hij
  change j < i at hij
  have hi : i ≠ 0 := by
    intro h
    rw [h] at hij
    exact Fin.not_lt_zero _ hij
  have hrow : ∀ l, g.val i l = (y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i l := by
    intro l
    rw [hyY]
    simp only [hY, ite_eq_right hi]
  have he : (g * y⁻¹).val i j = (y * y⁻¹).val i j := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [hrow l]
  rw [he, mul_inv_cancel, Units.val_one, Matrix.one_apply_ne hij.ne']

/-- Elements `x` with `x - 1 ∈ 𝔪ᵃ` form a group. -/
theorem mul_sub_one_mem_levelSet {a : ℕ} {x y : F.Carrier}
    (hx : x - 1 ∈ levelSet F.Carrier a) (hy : y - 1 ∈ levelSet F.Carrier a) :
    x * y - 1 ∈ levelSet F.Carrier a := by
  have h : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  rw [h]
  exact add_mem_levelSet (add_mem_levelSet
    (mul_mem_levelSet hx (mem_integer_of_mem_levelSet hy)) hx) hy

theorem inv_sub_one_mem_levelSet {a : ℕ} (ha : 0 < a) {t : F.Carrierˣ}
    (ht : (t : F.Carrier) - 1 ∈ levelSet F.Carrier a) :
    ((t⁻¹ : F.Carrierˣ) : F.Carrier) - 1 ∈ levelSet F.Carrier a := by
  obtain ⟨E, hE, hEv⟩ := exists_mem_principalLevelSubgroup (m := 0) ha
    ((Iwasawa.diagonalUnits fun _ : Fin (0 + 1) => t).val) (by
      intro i l
      obtain rfl : i = 0 := Fin.ext (by have := i.isLt; omega)
      obtain rfl : l = 0 := Fin.ext (by have := l.isLt; omega)
      rw [Iwasawa.diagonalUnits_val, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact ht)
  have hE' : E = Iwasawa.diagonalUnits fun _ : Fin (0 + 1) => t := Units.ext hEv
  have h := ((mem_principalLevelSubgroup_iff E).1 hE).2 0 0
  rw [hE', ← map_inv] at h
  change (Iwasawa.diagonalUnits fun _ : Fin (0 + 1) => t)⁻¹.val 0 0 - _ ∈ _ at h
  rw [← map_inv, Iwasawa.diagonalUnits_val, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
  exact h

/-- The units congruent to one modulo `𝔪ᵃ`, with their inverses. -/
def unitLevel (a : ℕ) : Subgroup F.Carrierˣ where
  carrier := {t | (t : F.Carrier) - 1 ∈ levelSet F.Carrier a ∧
    ((t⁻¹ : F.Carrierˣ) : F.Carrier) - 1 ∈ levelSet F.Carrier a}
  one_mem' := ⟨by rw [Units.val_one, sub_self]; exact zero_mem_levelSet a,
    by rw [inv_one, Units.val_one, sub_self]; exact zero_mem_levelSet a⟩
  mul_mem' {s t} hs ht := ⟨by rw [Units.val_mul]; exact mul_sub_one_mem_levelSet F hs.1 ht.1,
    by rw [mul_inv, Units.val_mul]; exact mul_sub_one_mem_levelSet F hs.2 ht.2⟩
  inv_mem' {t} ht := ⟨ht.2, by rw [inv_inv]; exact ht.1⟩

theorem mem_unitLevel_iff {a : ℕ} (ha : 0 < a) (t : F.Carrierˣ) :
    t ∈ unitLevel F a ↔ (t : F.Carrier) - 1 ∈ levelSet F.Carrier a :=
  ⟨And.left, fun h => ⟨h, inv_sub_one_mem_levelSet F ha h⟩⟩

theorem unitLevel_le_integralUnits (a : ℕ) :
    unitLevel F a ≤ integralUnits (ValuativeRel.valuation F.Carrier).integer := by
  intro t ht
  rw [mem_integralUnits]
  have h1 := add_mem (mem_integer_of_mem_levelSet ht.1)
    (one_mem (ValuativeRel.valuation F.Carrier).integer)
  have h2 := add_mem (mem_integer_of_mem_levelSet ht.2)
    (one_mem (ValuativeRel.valuation F.Carrier).integer)
  rw [sub_add_cancel] at h1 h2
  exact ⟨h1, h2⟩

theorem diagonalUnits_mem_principalLevel {a : ℕ} (ha : 0 < a) {d : Fin (n + 1) → F.Carrierˣ}
    (hd : ∀ i, d i ∈ unitLevel F a) :
    Iwasawa.diagonalUnits d ∈ principalLevelSubgroup F.Carrier n a := by
  obtain ⟨E, hE, hEv⟩ := exists_mem_principalLevelSubgroup ha (Iwasawa.diagonalUnits d).val (by
    intro i l
    rw [Iwasawa.diagonalUnits_val]
    by_cases hil : i = l
    · subst hil
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact (hd i).1
    · rw [Matrix.diagonal_apply_ne _ hil, Matrix.one_apply_ne hil, sub_zero]
      exact zero_mem_levelSet a)
  rwa [show Iwasawa.diagonalUnits d = E from Units.ext hEv.symm]

/-- The torus coordinates congruent to one modulo `𝔪ᵃ`. -/
def torusBox (a : ℕ) : Set (Fin n → F.Carrierˣ) :=
  {t | ∀ i, ((t i : F.Carrierˣ) : F.Carrier) - 1 ∈ levelSet F.Carrier a}

theorem torusFactor_mem {a : ℕ} (ha : 0 < a) {t : Fin n → F.Carrierˣ} (ht : t ∈ torusBox F a) :
    Iwasawa.diagonalUnits (Fin.cons (∏ i, t i)⁻¹ t : Fin (n + 1) → F.Carrierˣ) ∈
      principalLevelSubgroup F.Carrier n a := by
  have hU : ∀ i, t i ∈ unitLevel F a := fun i => (mem_unitLevel_iff F ha _).2 (ht i)
  apply diagonalUnits_mem_principalLevel F ha
  intro i
  induction i using Fin.cases with
  | zero =>
    rw [Fin.cons_zero]
    exact inv_mem (Subgroup.prod_mem _ fun i _ => hU i)
  | succ i =>
    rw [Fin.cons_succ]
    exact hU i

/-- The upper unipotent matrices whose first row is in `𝓛 q` off the corner and whose
other rows are congruent to the identity modulo `𝔪ᵃ`. -/
def unipotentBox (q : ℤ) (a : ℕ) : Set (upperUnipotent (n + 1) F.Carrier) :=
  {u | (∀ j, j ≠ 0 → (u : Langlands.GeneralLinear (n + 1) F.Carrier).val 0 j ∈ 𝓛 q) ∧
    ∀ i, i ≠ 0 → ∀ j, (u : Langlands.GeneralLinear (n + 1) F.Carrier).val i j -
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j ∈ levelSet F.Carrier a}

/-- The standard character is trivial on the unipotent box. -/
theorem standardCharacter_eq_one (ψ : UnitaryAdditiveCharacter F.Carrier) {q : ℤ} {a : ℕ}
    (hψ : ∀ z ∈ 𝓛 q, ψ z = 1) (hlev : ∀ z ∈ levelSet F.Carrier a, z ∈ 𝓛 q)
    {u : upperUnipotent (n + 1) F.Carrier} (hu : u ∈ unipotentBox F q a) :
    (standardCharacter ψ n u : ℂ) = 1 := by
  rw [standardCharacter_apply, UnitaryAdditiveCharacter.complex_apply]
  have hsum : (∑ i : Fin n, u.val i.castSucc i.succ) ∈ 𝓛 q := by
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    by_cases hi : i.castSucc = 0
    · have h := hu.1 i.succ (Fin.succ_ne_zero i)
      rw [← hi] at h
      exact h
    · have h := hu.2 _ hi i.succ
      rw [Matrix.one_apply_ne Fin.castSucc_lt_succ.ne, sub_zero] at h
      exact hlev _ h
  rw [hψ _ hsum]
  simp

theorem unipotent_mul_rankOne_apply_zero (u : upperUnipotent (n + 1) F.Carrier)
    (g : Langlands.GeneralLinear (0 + 1) F.Carrier) :
    ((u : Langlands.GeneralLinear (n + 1) F.Carrier) *
      Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det g) 1)).val 0 0 =
      ((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) := by
  rw [Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, Fin.cons_zero]
  change u.val 0 0 * _ = _
  rw [UpperUnipotent.entry_diag, one_mul]

theorem unipotent_mul_rankOne_apply (u : upperUnipotent (n + 1) F.Carrier)
    (g : Langlands.GeneralLinear (0 + 1) F.Carrier) {i j : Fin (n + 1)} (hij : i ≠ 0 ∨ j ≠ 0) :
    ((u : Langlands.GeneralLinear (n + 1) F.Carrier) *
      Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det g) 1)).val i j =
      (u : Langlands.GeneralLinear (n + 1) F.Carrier).val i j := by
  rw [Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.mul_diagonal]
  by_cases hj : j = 0
  · subst hj
    have hi : i ≠ 0 := hij.resolve_right (fun h => h rfl)
    have h0 : (u : Langlands.GeneralLinear (n + 1) F.Carrier).val i 0 = 0 :=
      UpperUnipotent.entry_eq_zero u (Fin.pos_of_ne_zero hi)
    rw [h0, zero_mul]
  · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
    rw [Fin.cons_succ, Pi.one_apply, Units.val_one, mul_one]

theorem mem_box_unipotent_mul_iff {A q : ℤ} {a : ℕ} (u : upperUnipotent (n + 1) F.Carrier)
    (g : Langlands.GeneralLinear (0 + 1) F.Carrier) :
    ((u : Langlands.GeneralLinear (n + 1) F.Carrier) *
      Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det g) 1)).val ∈ box F A q a ↔
      ((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) ∈ 𝓛 A ∧
        u ∈ unipotentBox F q a := by
  rw [mem_box_iff, unipotent_mul_rankOne_apply_zero]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, fun j hj => ?_, fun i hi j => ?_⟩
    · rw [← unipotent_mul_rankOne_apply F u g (Or.inr hj)]
      exact h1 j hj
    · rw [← unipotent_mul_rankOne_apply F u g (Or.inl hi)]
      exact h2 i hi j
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, fun j hj => ?_, fun i hi j => ?_⟩
    · rw [unipotent_mul_rankOne_apply F u g (Or.inr hj)]
      exact h1 j hj
    · rw [unipotent_mul_rankOne_apply F u g (Or.inl hi)]
      exact h2 i hi j

/-- A parametrization point splits as `u · diag(det g, 1, …, 1) · diag((∏ t)⁻¹, t)`. -/
theorem point_eq_mul (g : Langlands.GeneralLinear (0 + 1) F.Carrier) (t : Fin n → F.Carrierˣ)
    (u : upperUnipotent (n + 1) F.Carrier) :
    point ((g, t), u) = (u : Langlands.GeneralLinear (n + 1) F.Carrier) *
      Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det g) 1) *
        Iwasawa.diagonalUnits (Fin.cons (∏ i, t i)⁻¹ t) := by
  rw [point, diagonalUnits_torusCoord, mul_assoc]

theorem mem_torusBox_of_mem_box {A q : ℤ} {a : ℕ}
    {x : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
      upperUnipotent (n + 1) F.Carrier} (hx : (point x).val ∈ box F A q a) :
    x.1.2 ∈ torusBox F a := by
  intro i
  have h := ((mem_box_iff F _).1 hx).2.2 i.succ (Fin.succ_ne_zero i) i.succ
  have he : (point x).val i.succ i.succ = ((x.1.2 i : F.Carrierˣ) : F.Carrier) := by
    change ((x.2 : Langlands.GeneralLinear (n + 1) F.Carrier).val *
      (Iwasawa.diagonalUnits (torusCoord n x.1)).val) i.succ i.succ = _
    rw [Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, UpperUnipotent.entry_diag, one_mul,
      torusCoord_succ]
  rwa [he, Matrix.one_apply_eq] at h

/-- Every element of the integral group meeting the box on the left of a point is a
point with integral torus coordinate times a principal level element. -/
theorem exists_point_mul_of_mem_box {A q : ℤ} {a : ℕ} (ha : 0 < a)
    {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n)
    {x₀ : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
      upperUnipotent (n + 1) F.Carrier} (hx₀ : (point x₀ * k).val ∈ box F A q a) :
    ∃ xβ : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
        upperUnipotent (n + 1) F.Carrier,
      (∀ i, ValuativeRel.valuation F.Carrier (torusCoord n xβ.1 i : F.Carrier) = 1) ∧
        ∃ y ∈ principalLevelSubgroup F.Carrier n a, k = point xβ * y := by
  obtain ⟨y, hy, hup⟩ := exists_mem_principalLevel_mul_inv_upper F ha hx₀
  have hβ : k * y⁻¹ = (point x₀)⁻¹ * (point x₀ * k * y⁻¹) := by group
  have hup' : (k * y⁻¹).val.IsUpperTriangular := by
    rw [hβ, Units.val_mul]
    exact (point_inv_isUpperTriangular x₀).mul hup
  obtain ⟨xβ, hxβ⟩ := exists_point_eq (k * y⁻¹) hup'
  have hK : point xβ ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n := by
    rw [hxβ]
    exact mul_mem hk (inv_mem (principalLevel_le_integral F a hy))
  refine ⟨xβ, ((point_mem_integralSubgroup_iff _ xβ).1 hK).1, y, hy, ?_⟩
  rw [hxβ, inv_mul_cancel_right]

end Box

section Measure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance (m : ℕ) : MeasurableSpace (Langlands.GeneralLinear (m + 1) F.Carrier) := borel _
local instance (m : ℕ) : BorelSpace (Langlands.GeneralLinear (m + 1) F.Carrier) := ⟨rfl⟩
local instance (m : ℕ) : MeasurableSpace (upperUnipotent (m + 1) F.Carrier) := borel _
local instance (m : ℕ) : BorelSpace (upperUnipotent (m + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace F.Carrierˣ := borel _
local instance : BorelSpace F.Carrierˣ := ⟨rfl⟩

local instance matrixLocallyCompact (m : ℕ) :
    LocallyCompactSpace (Matrix (Fin m) (Fin m) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → F.Carrier))

local instance glLocallyCompact (m : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear m F.Carrier) :=
  inferInstance

local instance glSecondCountable (m : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear m F.Carrier) := by
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → F.Carrier))
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F.Carrier)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

local instance unipotentSecondCountable (m : ℕ) :
    SecondCountableTopology (upperUnipotent m F.Carrier) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (upperUnipotent m F.Carrier : Set (Langlands.GeneralLinear m F.Carrier))

local instance unipotentLocallyCompact (m : ℕ) :
    LocallyCompactSpace (upperUnipotent m F.Carrier) :=
  UpperUnipotent.locallyCompactSpace

local instance unitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

local instance unitsLocallyCompact : LocallyCompactSpace F.Carrierˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := F.Carrier)).locallyCompactSpace

local instance parameterBase_isMulLeftInvariant (n : ℕ) :
    ((generalLinearHaar F.Carrier 0).prod
      (Measure.pi fun _ : Fin n => localMultiplicativeHaar F.Carrier)).IsMulLeftInvariant :=
  Measure.prod.instIsMulLeftInvariant

local notation "𝓛" => F.canonicalTopologicalData.additiveLattice

/-- Right translation by a point with integral torus coordinate preserves the parameter
measure. -/
theorem measurePreserving_rshift (n : ℕ)
    (x₀ : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
      upperUnipotent (n + 1) F.Carrier)
    (h₀ : ∀ i, ValuativeRel.valuation F.Carrier (torusCoord n x₀.1 i : F.Carrier) = 1) :
    MeasurePreserving (rshift x₀) (iwasawaMeasure F n) (iwasawaMeasure F n) := by
  have hw : weight F n x₀.1 = 1 := by
    rw [weight_apply, torusModulus_eq_one F _ h₀, inv_one, Units.val_one]
  have hbase : MeasurePreserving
      (fun b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ) => b * x₀.1)
      (parameterMeasure F n) (parameterMeasure F n) := by
    have hm : Measurable
        fun b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ) => b * x₀.1 :=
      (continuous_id.mul continuous_const).measurable
    refine ⟨hm, ?_⟩
    have hfun : (fun b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ) =>
        b * x₀.1) = (x₀.1 * ·) := funext fun b => parameter_mul_comm b x₀.1
    rw [hfun]
    have h := map_mul_left_withDensity ((generalLinearHaar F.Carrier 0).prod
      (Measure.pi fun _ : Fin n => localMultiplicativeHaar F.Carrier)) (weight F n)
      (continuous_weight F n).measurable x₀.1
    rw [map_inv, hw, inv_one, ENNReal.coe_one, one_smul] at h
    exact h
  have hc : Continuous fun b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ) =>
      diagonalConj (torusCoord n b) x₀.2 := by
    have h : Continuous fun b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ) =>
        ((diagonalConj (torusCoord n b) x₀.2 : upperUnipotent (n + 1) F.Carrier) :
          Langlands.GeneralLinear (n + 1) F.Carrier) := by
      simp_rw [diagonalConj_val]
      exact ((continuous_diagonalUnits'.comp (continuous_torusCoord F n)).mul continuous_const).mul
        (continuous_diagonalUnits'.comp (continuous_torusCoord F n)).inv
    exact h.subtype_mk _
  have hgm : Measurable (Function.uncurry
      fun (b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ))
        (u : upperUnipotent (n + 1) F.Carrier) => u * diagonalConj (torusCoord n b) x₀.2) :=
    (continuous_snd.mul (hc.comp continuous_fst)).measurable
  have hfib : ∀ᵐ b ∂parameterMeasure F n,
      Measure.map (fun u : upperUnipotent (n + 1) F.Carrier =>
        u * diagonalConj (torusCoord n b) x₀.2) (unipotentHaar F.Carrier n) =
          unipotentHaar F.Carrier n :=
    Filter.Eventually.of_forall fun b => map_mul_right_eq_self _ _
  exact hbase.skew_product hgm hfib

theorem measurableSet_integralSubgroup (n : ℕ) :
    MeasurableSet (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
  rw [← levelSubgroup_zero]
  exact (levelOpenSubgroup F.Carrier n 0).isOpen.measurableSet

/-- **Integration over the integral group, with a support set.** If on a measurable
`S` every right translate by `k ∈ K` is a measure-preserving reparametrization and
outside `S` the translate vanishes, the integral over `GL_(n+1)` is `dk(S)` times the
parameter integral. Lebesgue version. -/
theorem lintegral_enorm_eq_of_support {n : ℕ}
    (H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (hH : Continuous H)
    (S : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) (hS : MeasurableSet S)
    (hin : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n, k ∈ S →
      ∃ r : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
          upperUnipotent (n + 1) F.Carrier →
        (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
          upperUnipotent (n + 1) F.Carrier,
        MeasurePreserving r (iwasawaMeasure F n) (iwasawaMeasure F n) ∧
          ∀ x, H (point x * k) = H (point (r x)))
    (hout : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n, k ∉ S →
      ∀ x, H (point x * k) = 0) :
    ∫⁻ g, ‖H g‖ₑ ∂generalLinearHaar F.Carrier n =
      (generalLinearHaar F.Carrier n).restrict
          (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
            Set (Langlands.GeneralLinear (n + 1) F.Carrier)) S *
        ∫⁻ x, ‖H (point x)‖ₑ ∂iwasawaMeasure F n := by
  have hK := measurableSet_integralSubgroup F n
  have hπ : Measurable (fun x : ((Langlands.GeneralLinear (0 + 1) F.Carrier ×
      (Fin n → F.Carrierˣ)) × upperUnipotent (n + 1) F.Carrier) ×
        Langlands.GeneralLinear (n + 1) F.Carrier => point x.1 * x.2) :=
    ((measurable_point F n).comp measurable_fst).mul measurable_snd
  have hHm : Measurable fun g => ‖H g‖ₑ := hH.enorm.measurable
  have hHp : Measurable fun x => ‖H (point x)‖ₑ :=
    (hH.comp (continuous_point F n)).enorm.measurable
  calc ∫⁻ g, ‖H g‖ₑ ∂generalLinearHaar F.Carrier n
      = ∫⁻ g, ‖H g‖ₑ ∂Measure.map (fun x : ((Langlands.GeneralLinear (0 + 1) F.Carrier ×
          (Fin n → F.Carrierˣ)) × upperUnipotent (n + 1) F.Carrier) ×
            Langlands.GeneralLinear (n + 1) F.Carrier => point x.1 * x.2)
          ((iwasawaMeasure F n).prod ((generalLinearHaar F.Carrier n).restrict
            (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
              Set (Langlands.GeneralLinear (n + 1) F.Carrier)))) := by
        rw [map_iwasawaMeasure_prod]
    _ = ∫⁻ z, ‖H (point z.1 * z.2)‖ₑ ∂((iwasawaMeasure F n).prod
          ((generalLinearHaar F.Carrier n).restrict
            (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
              Set (Langlands.GeneralLinear (n + 1) F.Carrier)))) := lintegral_map hHm hπ
    _ = ∫⁻ k, ∫⁻ x, ‖H (point x * k)‖ₑ ∂iwasawaMeasure F n ∂(generalLinearHaar F.Carrier n).restrict
            (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
              Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
        lintegral_prod_symm _ (hHm.comp hπ).aemeasurable
    _ = ∫⁻ k, S.indicator (fun _ => ∫⁻ x, ‖H (point x)‖ₑ ∂iwasawaMeasure F n) k
          ∂(generalLinearHaar F.Carrier n).restrict
            (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
              Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hK] with k hk
        by_cases hkS : k ∈ S
        · obtain ⟨r, hr, hrH⟩ := hin k hk hkS
          rw [Set.indicator_of_mem hkS]
          simp_rw [hrH]
          exact hr.lintegral_comp hHp
        · rw [Set.indicator_of_notMem hkS]
          simp [hout k hk hkS]
    _ = _ := by rw [lintegral_indicator_const hS, mul_comm]

/-- Bochner version of `lintegral_enorm_eq_of_support`. -/
theorem integral_eq_of_support {n : ℕ}
    (H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (hH : Continuous H)
    (S : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) (hS : MeasurableSet S)
    (hin : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n, k ∈ S →
      ∃ r : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
          upperUnipotent (n + 1) F.Carrier →
        (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
          upperUnipotent (n + 1) F.Carrier,
        MeasurePreserving r (iwasawaMeasure F n) (iwasawaMeasure F n) ∧
          ∀ x, H (point x * k) = H (point (r x)))
    (hout : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n, k ∉ S →
      ∀ x, H (point x * k) = 0)
    (hint : Integrable H (generalLinearHaar F.Carrier n)) :
    ∫ g, H g ∂generalLinearHaar F.Carrier n =
      ((generalLinearHaar F.Carrier n).restrict
          (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
            Set (Langlands.GeneralLinear (n + 1) F.Carrier))).real S •
        ∫ x, H (point x) ∂iwasawaMeasure F n := by
  have hK := measurableSet_integralSubgroup F n
  have hπ : Measurable (fun x : ((Langlands.GeneralLinear (0 + 1) F.Carrier ×
      (Fin n → F.Carrierˣ)) × upperUnipotent (n + 1) F.Carrier) ×
        Langlands.GeneralLinear (n + 1) F.Carrier => point x.1 * x.2) :=
    ((measurable_point F n).comp measurable_fst).mul measurable_snd
  have hHp : Continuous fun x => H (point x) := hH.comp (continuous_point F n)
  have hmap := map_iwasawaMeasure_prod F n
  have hint' : Integrable (fun x : ((Langlands.GeneralLinear (0 + 1) F.Carrier ×
      (Fin n → F.Carrierˣ)) × upperUnipotent (n + 1) F.Carrier) ×
        Langlands.GeneralLinear (n + 1) F.Carrier => H (point x.1 * x.2))
      ((iwasawaMeasure F n).prod ((generalLinearHaar F.Carrier n).restrict
        (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
          Set (Langlands.GeneralLinear (n + 1) F.Carrier)))) := by
    rw [← hmap] at hint
    exact (integrable_map_measure hH.aestronglyMeasurable hπ.aemeasurable).1 hint
  calc ∫ g, H g ∂generalLinearHaar F.Carrier n
      = ∫ g, H g ∂Measure.map (fun x : ((Langlands.GeneralLinear (0 + 1) F.Carrier ×
          (Fin n → F.Carrierˣ)) × upperUnipotent (n + 1) F.Carrier) ×
            Langlands.GeneralLinear (n + 1) F.Carrier => point x.1 * x.2)
          ((iwasawaMeasure F n).prod ((generalLinearHaar F.Carrier n).restrict
            (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
              Set (Langlands.GeneralLinear (n + 1) F.Carrier)))) := by
        rw [hmap]
    _ = ∫ z, H (point z.1 * z.2) ∂((iwasawaMeasure F n).prod
          ((generalLinearHaar F.Carrier n).restrict
            (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
              Set (Langlands.GeneralLinear (n + 1) F.Carrier)))) :=
        integral_map hπ.aemeasurable hH.aestronglyMeasurable
    _ = ∫ k, ∫ x, H (point x * k) ∂iwasawaMeasure F n ∂(generalLinearHaar F.Carrier n).restrict
            (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
              Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
        integral_prod_symm _ hint'
    _ = ∫ k, S.indicator (fun _ => ∫ x, H (point x) ∂iwasawaMeasure F n) k
          ∂(generalLinearHaar F.Carrier n).restrict
            (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
              Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hK] with k hk
        by_cases hkS : k ∈ S
        · obtain ⟨r, hr, hrH⟩ := hin k hk hkS
          rw [Set.indicator_of_mem hkS]
          simp_rw [hrH]
          have h := integral_map hr.measurable.aemeasurable hHp.aestronglyMeasurable
            (μ := iwasawaMeasure F n)
          rw [hr.map_eq] at h
          exact h.symm
        · rw [Set.indicator_of_notMem hkS]
          simp [hout k hk hkS]
    _ = _ := integral_indicator_const _ hS


theorem coe_unitLevel {a : ℕ} (ha : 0 < a) :
    (unitLevel F a : Set F.Carrierˣ) =
      (fun s : F.Carrierˣ => (s : F.Carrier) - 1) ⁻¹' levelSet F.Carrier a := by
  ext s
  exact mem_unitLevel_iff F ha s

theorem isOpen_unitLevel {a : ℕ} (ha : 0 < a) : IsOpen (unitLevel F a : Set F.Carrierˣ) := by
  rw [coe_unitLevel F ha]
  exact (isOpen_levelSet a).preimage (Units.continuous_val.sub continuous_const)

theorem torusBox_eq_pi {a : ℕ} (ha : 0 < a) (n : ℕ) :
    torusBox F (n := n) a = Set.univ.pi fun _ => (unitLevel F a : Set F.Carrierˣ) := by
  ext t
  simp only [torusBox, Set.mem_ofPred_eq, Set.mem_univ_pi, SetLike.mem_coe, mem_unitLevel_iff F ha]

theorem isOpen_torusBox {a : ℕ} (ha : 0 < a) (n : ℕ) : IsOpen (torusBox F (n := n) a) := by
  rw [torusBox_eq_pi F ha]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_unitLevel F ha

theorem unitLevel_measure_pos {a : ℕ} (ha : 0 < a) :
    0 < localMultiplicativeHaar F.Carrier (unitLevel F a : Set F.Carrierˣ) :=
  (isOpen_unitLevel F ha).measure_pos _ ⟨1, (unitLevel F a).one_mem⟩

theorem unitLevel_measure_le (a : ℕ) :
    localMultiplicativeHaar F.Carrier (unitLevel F a : Set F.Carrierˣ) ≤ 1 := by
  calc localMultiplicativeHaar F.Carrier (unitLevel F a : Set F.Carrierˣ)
      ≤ localMultiplicativeHaar F.Carrier
          (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ) :=
        measure_mono (unitLevel_le_integralUnits F a)
    _ = 1 := localMultiplicativeHaar_integerUnits F.Carrier

theorem tailMeasure_torusBox {a : ℕ} (ha : 0 < a) (n : ℕ) :
    tailMeasure F n (torusBox F a) =
      localMultiplicativeHaar F.Carrier (unitLevel F a : Set F.Carrierˣ) ^ n := by
  have hm : MeasurableSet (torusBox F (n := n) a) := (isOpen_torusBox F ha n).measurableSet
  rw [tailMeasure, withDensity_apply _ hm]
  have hone : ∀ t ∈ torusBox F (n := n) a, ((weight F n (1, t) : ℝ≥0) : ℝ≥0∞) = 1 := by
    intro t ht
    have h1 : ∀ i, ValuativeRel.valuation F.Carrier
        (torusCoord n ((1 : Langlands.GeneralLinear (0 + 1) F.Carrier), t) i : F.Carrier) = 1 := by
      rw [torusCoord_valuation_iff]
      exact ⟨one_mem _, fun i => valuation_eq_one_of_mem_integralUnits _
        (unitLevel_le_integralUnits F a ((mem_unitLevel_iff F ha _).2 (ht i)))⟩
    rw [weight_apply, torusModulus_eq_one F _ h1, inv_one, Units.val_one, ENNReal.coe_one]
  rw [setLIntegral_congr_fun hm hone, setLIntegral_const, one_mul, torusBox_eq_pi F ha,
    Measure.pi_pi]
  simp

theorem tailMeasure_torusBox_pos {a : ℕ} (ha : 0 < a) (n : ℕ) :
    0 < tailMeasure F n (torusBox F a) := by
  rw [tailMeasure_torusBox F ha]
  exact ENNReal.pow_pos (unitLevel_measure_pos F ha) n

theorem tailMeasure_torusBox_lt_top {a : ℕ} (ha : 0 < a) (n : ℕ) :
    tailMeasure F n (torusBox F a) < ⊤ := by
  rw [tailMeasure_torusBox F ha]
  exact (pow_le_one₀ zero_le (unitLevel_measure_le F a)).trans_lt ENNReal.one_lt_top

theorem continuous_unipotent_entry {n : ℕ} (i j : Fin (n + 1)) :
    Continuous fun u : upperUnipotent (n + 1) F.Carrier =>
      (u : Langlands.GeneralLinear (n + 1) F.Carrier).val i j :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j

theorem isOpen_unipotentBox {n : ℕ} (q : ℤ) (a : ℕ) : IsOpen (unipotentBox F (n := n) q a) := by
  have h : unipotentBox F (n := n) q a =
      (⋂ j, ⋂ (_ : j ≠ 0), (fun u : upperUnipotent (n + 1) F.Carrier =>
        (u : Langlands.GeneralLinear (n + 1) F.Carrier).val 0 j) ⁻¹' (𝓛 q : Set F.Carrier)) ∩
      ⋂ i, ⋂ (_ : i ≠ 0), ⋂ j, (fun u : upperUnipotent (n + 1) F.Carrier =>
        (u : Langlands.GeneralLinear (n + 1) F.Carrier).val i j -
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j) ⁻¹' levelSet F.Carrier a := by
    ext u
    simp only [unipotentBox, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, SetLike.mem_coe]
  rw [h]
  exact (isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
      (isOpen_lattice F q).preimage (continuous_unipotent_entry F 0 j)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun _ =>
      isOpen_iInter_of_finite fun j =>
        (isOpen_levelSet a).preimage ((continuous_unipotent_entry F i j).sub continuous_const))

theorem one_mem_unipotentBox {n : ℕ} (q : ℤ) (a : ℕ) :
    (1 : upperUnipotent (n + 1) F.Carrier) ∈ unipotentBox F q a := by
  refine ⟨fun j hj => ?_, fun i _ j => ?_⟩
  · change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) 0 j ∈ 𝓛 q
    rw [Matrix.one_apply_ne (Ne.symm hj)]
    exact zero_mem _
  · change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j -
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j ∈ _
    rw [sub_self]
    exact zero_mem_levelSet a

theorem unipotentBox_subset {n : ℕ} {q : ℤ} (hq : q ≤ 0) (a : ℕ) :
    unipotentBox F (n := n) q a ⊆
      (unipotentIntegralOpen F.Carrier n : Set (upperUnipotent (n + 1) F.Carrier)) := by
  intro u hu
  change (u : Langlands.GeneralLinear (n + 1) F.Carrier) ∈ levelSubgroup F.Carrier n 0
  rw [levelSubgroup_zero]
  apply Unramified.MinusculeCosets.unipotent_mem_integralSubgroup u.property
  intro i j
  by_cases hi : i = 0
  · subst hi
    by_cases hj : j = 0
    · subst hj
      convert one_mem (ValuativeRel.valuation F.Carrier).integer using 1
      exact UpperUnipotent.entry_diag u 0
    · exact (mem_lattice_zero_iff F _).1 (lattice_mono F hq (hu.1 j hj))
  · exact mem_integer_of_sub_one_mem_levelSet (hu.2 i hi j)

theorem unipotentHaar_unipotentBox_pos {n : ℕ} (q : ℤ) (a : ℕ) :
    0 < unipotentHaar F.Carrier n (unipotentBox F q a) :=
  (isOpen_unipotentBox F q a).measure_pos _ ⟨1, one_mem_unipotentBox F q a⟩

theorem unipotentHaar_unipotentBox_lt_top {n : ℕ} {q : ℤ} (hq : q ≤ 0) (a : ℕ) :
    unipotentHaar F.Carrier n (unipotentBox F q a) < ⊤ := by
  calc unipotentHaar F.Carrier n (unipotentBox F q a)
      ≤ unipotentHaar F.Carrier n
          (unipotentIntegralOpen F.Carrier n : Set (upperUnipotent (n + 1) F.Carrier)) :=
        measure_mono (unipotentBox_subset F hq a)
    _ = 1 := unipotentHaar_integral F.Carrier n
    _ < ⊤ := ENNReal.one_lt_top

/-- The integral elements `k` such that `point x₀ * k` lies in the box for some `x₀`. -/
def boxSupport {n : ℕ} (A q : ℤ) (a : ℕ) : Set (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  {k | k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n ∧
    ∃ x₀ : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
      upperUnipotent (n + 1) F.Carrier, (point x₀ * k).val ∈ box F A q a}

theorem isOpen_boxSupport {n : ℕ} (A q : ℤ) (a : ℕ) : IsOpen (boxSupport F (n := n) A q a) := by
  have h : boxSupport F (n := n) A q a =
      (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
        Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∩
      ⋃ x₀ : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
          upperUnipotent (n + 1) F.Carrier,
        (fun k => (point x₀ * k).val) ⁻¹' box F A q a := by
    ext k
    simp only [boxSupport, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion,
      Set.mem_preimage, SetLike.mem_coe]
  rw [h]
  refine IsOpen.inter ?_ (isOpen_iUnion fun x₀ => (isOpen_box F A q a).preimage
    (Units.continuous_val.comp (continuous_const.mul continuous_id)))
  rw [← levelSubgroup_zero]
  exact (levelOpenSubgroup F.Carrier n 0).isOpen

theorem one_mem_boxSupport {n : ℕ} {A q : ℤ} {a : ℕ} (hA : 0 ≤ A) :
    (1 : Langlands.GeneralLinear (n + 1) F.Carrier) ∈ boxSupport F A q a := by
  refine ⟨one_mem _, 1, ?_⟩
  have h1 : point (1 : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
      upperUnipotent (n + 1) F.Carrier) = 1 := by
    simp [point]
  rw [h1, mul_one, Units.val_one]
  exact one_mem_box F hA

theorem restrict_boxSupport_pos {n : ℕ} {A q : ℤ} {a : ℕ} (hA : 0 ≤ A) :
    0 < (generalLinearHaar F.Carrier n).restrict
      (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
        Set (Langlands.GeneralLinear (n + 1) F.Carrier)) (boxSupport F A q a) := by
  rw [Measure.restrict_apply (isOpen_boxSupport F A q a).measurableSet,
    Set.inter_eq_left.2 fun k hk => hk.1]
  exact (isOpen_boxSupport F A q a).measure_pos _ ⟨1, one_mem_boxSupport F hA⟩

theorem restrict_boxSupport_lt_top {n : ℕ} (A q : ℤ) (a : ℕ) :
    (generalLinearHaar F.Carrier n).restrict
      (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
        Set (Langlands.GeneralLinear (n + 1) F.Carrier)) (boxSupport F A q a) < ⊤ := by
  calc (generalLinearHaar F.Carrier n).restrict
        (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
          Set (Langlands.GeneralLinear (n + 1) F.Carrier)) (boxSupport F A q a)
      ≤ (generalLinearHaar F.Carrier n).restrict
        (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
          Set (Langlands.GeneralLinear (n + 1) F.Carrier)) Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := by rw [Measure.restrict_apply_univ, generalLinearHaar_integralSubgroup]
    _ < ⊤ := ENNReal.one_lt_top

theorem continuous_determinantWeight (m : ℕ) (s : ℂ) :
    Continuous fun g : Langlands.GeneralLinear m F.Carrier =>
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s := by
  unfold determinantWeight
  have hc : Continuous fun g : Langlands.GeneralLinear m F.Carrier =>
      ((normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det g.val) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((F.canonicalTopologicalData.continuous_normalizedAbs).comp
      Units.continuous_val.matrix_det)
  refine hc.cpow continuous_const fun g => ?_
  rw [Complex.ofReal_mem_slitPlane]
  exact (normalizedAbsoluteValue F.canonicalTopologicalData).pos g.det_ne_zero

theorem continuous_glModelFunction (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) V) (hσ : IsSmooth σ)
    (ℓ : glFunctionals ψ m σ) (w : (glCoefficientModel ψ m σ ℓ).toSubmodule) :
    Continuous (glModelFunction ψ m σ ℓ w) := by
  obtain ⟨K, hK⟩ := glModel_isSmooth ψ m σ hσ ℓ w
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hopen : IsOpen ((fun g => g₀⁻¹ * g) ⁻¹' (K : Set (Langlands.GeneralLinear (m + 1) F.Carrier))) :=
    K.isOpen.preimage (continuous_const.mul continuous_id)
  have hmem : g₀ ∈ (fun g => g₀⁻¹ * g) ⁻¹' (K : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) := by
    simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact K.one_mem
  have hev : ∀ᶠ g in 𝓝 g₀, glModelFunction ψ m σ ℓ w g₀ = glModelFunction ψ m σ ℓ w g := by
    filter_upwards [hopen.mem_nhds hmem] with g hg
    have hfix : glModelRepresentation ψ m σ ℓ (g₀⁻¹ * g) w = w := hK ⟨_, hg⟩
    calc glModelFunction ψ m σ ℓ w g₀
        = glModelFunction ψ m σ ℓ (glModelRepresentation ψ m σ ℓ (g₀⁻¹ * g) w) g₀ := by
          rw [hfix]
      _ = glModelFunction ψ m σ ℓ w g := by
          rw [glModelFunction_translate, mul_inv_cancel_left]
  exact continuousAt_const.congr hev


/-- The rank-one embedding is the parametrization point with trivial torus tail and
unipotent coordinate. -/
theorem rankOneEmbedding_eq_point {m : ℕ} (g : Langlands.GeneralLinear (0 + 1) F.Carrier) :
    rankOneEmbedding m g =
      point ((g, (1 : Fin (m + 1) → F.Carrierˣ)), (1 : upperUnipotent (m + 1 + 1) F.Carrier)) := by
  have ht : torusCoord (m + 1) (g, (1 : Fin (m + 1) → F.Carrierˣ)) =
      Fin.cons (Matrix.GeneralLinearGroup.det g) 1 := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp
  rw [point, ht, Subgroup.coe_one, one_mul]
  rfl

theorem continuous_rankOneEmbedding (m : ℕ) :
    Continuous fun g : Langlands.GeneralLinear (0 + 1) F.Carrier => rankOneEmbedding m g := by
  have h : (fun g : Langlands.GeneralLinear (0 + 1) F.Carrier => rankOneEmbedding m g) =
      fun g => point ((g, (1 : Fin (m + 1) → F.Carrierˣ)),
        (1 : upperUnipotent (m + 1 + 1) F.Carrier)) :=
    funext (rankOneEmbedding_eq_point F)
  rw [h]
  exact (continuous_point F (m + 1)).comp
    ((continuous_id.prodMk continuous_const).prodMk continuous_const)

/-- The parameter integral of a function of product form. Bochner version. -/
theorem integral_param_of_eq {n : ℕ} (H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (Fg : Langlands.GeneralLinear (0 + 1) F.Carrier → ℂ) (T : Set (Fin n → F.Carrierˣ))
    (U : Set (upperUnipotent (n + 1) F.Carrier)) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hpoint : ∀ x, H (point x) =
      (Fg x.1.1 * T.indicator (fun _ => (1 : ℂ)) x.1.2) * U.indicator (fun _ => (1 : ℂ)) x.2) :
    ∫ x, H (point x) ∂iwasawaMeasure F n =
      (∫ g, Fg g ∂glOneMeasure F n) *
        (((tailMeasure F n).real T * (unipotentHaar F.Carrier n).real U : ℝ) : ℂ) := by
  calc ∫ x, H (point x) ∂iwasawaMeasure F n
      = ∫ x, (Fg x.1.1 * T.indicator (fun _ => (1 : ℂ)) x.1.2) *
          U.indicator (fun _ => (1 : ℂ)) x.2
          ∂((parameterMeasure F n).prod (unipotentHaar F.Carrier n)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (∫ b, Fg b.1 * T.indicator (fun _ => (1 : ℂ)) b.2 ∂parameterMeasure F n) *
          ∫ u, U.indicator (fun _ => (1 : ℂ)) u ∂unipotentHaar F.Carrier n :=
        integral_prod_mul (L := ℂ)
          (fun b : Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ) =>
            Fg b.1 * T.indicator (fun _ => (1 : ℂ)) b.2)
          (fun u : upperUnipotent (n + 1) F.Carrier => U.indicator (fun _ => (1 : ℂ)) u)
    _ = ((∫ g, Fg g ∂glOneMeasure F n) *
          ∫ t, T.indicator (fun _ => (1 : ℂ)) t ∂tailMeasure F n) *
          ∫ u, U.indicator (fun _ => (1 : ℂ)) u ∂unipotentHaar F.Carrier n := by
        rw [parameterMeasure_eq_prod]
        congr 1
        exact integral_prod_mul (L := ℂ) Fg (fun t => T.indicator (fun _ => (1 : ℂ)) t)
    _ = _ := by
        rw [integral_indicator_const _ hT, integral_indicator_const _ hU]
        simp only [Complex.real_smul, mul_one]
        push_cast
        ring

/-- The parameter integral of a function of product form. Lebesgue version. -/
theorem lintegral_param_of_eq {n : ℕ} (H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (Fg : Langlands.GeneralLinear (0 + 1) F.Carrier → ℂ) (T : Set (Fin n → F.Carrierˣ))
    (U : Set (upperUnipotent (n + 1) F.Carrier)) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hpoint : ∀ x, H (point x) =
      (Fg x.1.1 * T.indicator (fun _ => (1 : ℂ)) x.1.2) * U.indicator (fun _ => (1 : ℂ)) x.2)
    (hFg : Measurable Fg) :
    ∫⁻ x, ‖H (point x)‖ₑ ∂iwasawaMeasure F n =
      (∫⁻ g, ‖Fg g‖ₑ ∂glOneMeasure F n) * (tailMeasure F n T * unipotentHaar F.Carrier n U) := by
  have hnorm : ∀ x : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
      upperUnipotent (n + 1) F.Carrier, ‖H (point x)‖ₑ =
        (‖Fg x.1.1‖ₑ * T.indicator (fun _ => (1 : ℝ≥0∞)) x.1.2) *
          U.indicator (fun _ => (1 : ℝ≥0∞)) x.2 := by
    intro x
    rw [hpoint, enorm_mul, enorm_mul, enorm_indicator_eq_indicator_enorm,
      enorm_indicator_eq_indicator_enorm]
    simp
  have hTi : Measurable (T.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hT
  calc ∫⁻ x, ‖H (point x)‖ₑ ∂iwasawaMeasure F n
      = ∫⁻ x, (‖Fg x.1.1‖ₑ * T.indicator (fun _ => (1 : ℝ≥0∞)) x.1.2) *
          U.indicator (fun _ => (1 : ℝ≥0∞)) x.2
          ∂((parameterMeasure F n).prod (unipotentHaar F.Carrier n)) := lintegral_congr hnorm
    _ = (∫⁻ b, ‖Fg b.1‖ₑ * T.indicator (fun _ => (1 : ℝ≥0∞)) b.2 ∂parameterMeasure F n) *
          ∫⁻ u, U.indicator (fun _ => (1 : ℝ≥0∞)) u ∂unipotentHaar F.Carrier n :=
        lintegral_prod_mul ((hFg.enorm.comp measurable_fst).mul (hTi.comp measurable_snd)).aemeasurable
          (measurable_const.indicator hU).aemeasurable
    _ = ((∫⁻ g, ‖Fg g‖ₑ ∂glOneMeasure F n) *
          ∫⁻ t, T.indicator (fun _ => (1 : ℝ≥0∞)) t ∂tailMeasure F n) *
          ∫⁻ u, U.indicator (fun _ => (1 : ℝ≥0∞)) u ∂unipotentHaar F.Carrier n := by
        rw [parameterMeasure_eq_prod]
        congr 1
        exact lintegral_prod_mul hFg.enorm.aemeasurable hTi.aemeasurable
    _ = _ := by
        rw [lintegral_indicator_const hT, lintegral_indicator_const hU, one_mul, one_mul, mul_assoc]

section Comparison

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ} {V : Type uV} [AddCommGroup V]
  [Module ℂ V] (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)

/-- The box integrand is right invariant under the principal level. -/
theorem matrixIntegrand_mul_principalLevel {A q : ℤ} {a : ℕ} (hA : 0 ≤ A) (hq : q ≤ 0)
    (hL : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ j, j ≠ 0 → y.val 0 j ∈ 𝓛 (q - A))
    (hstab : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g)
    (s : ℂ) (g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier)
    {y : Langlands.GeneralLinear (m + 1 + 1) F.Carrier}
    (hy : y ∈ principalLevelSubgroup F.Carrier (m + 1) a) :
    GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
        (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a)) s
        (glModelFunction ψ (m + 1) σ ℓ w) (g * y) =
      GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
        (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a)) s
        (glModelFunction ψ (m + 1) σ ℓ w) g := by
  have habv : ∀ x : F.Carrier, ValuativeRel.valuation F.Carrier x = 1 →
      normalizedAbsoluteValue F.canonicalTopologicalData x = 1 :=
    fun x hx => (F.canonicalTopologicalData.normalizedAbs_eq_one_iff_valuation_eq_one x).2 hx
  simp only [GodementJacquet.matrixIntegrand, coe_compactOpenIndicator]
  rw [hstab y hy g, Conductor.determinantWeight_mul_integral habv g y
    (principalLevel_le_integral F a hy) s]
  have hb := mul_mem_box_iff F hA hq hL g.val hy
  rw [Units.val_mul]
  by_cases h : g.val ∈ box F A q a
  · rw [Set.indicator_of_mem (hb.2 h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun h' => h (hb.1 h')), Set.indicator_of_notMem h]

/-- The box integrand at a parametrization point. -/
theorem matrixIntegrand_point {A q : ℤ} {a : ℕ} (ha : 0 < a) (hA : 0 ≤ A) (hq : q ≤ 0)
    (hL : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ j, j ≠ 0 → y.val 0 j ∈ 𝓛 (q - A))
    (hψ : ∀ z ∈ 𝓛 q, ψ z = 1) (hlev : ∀ z ∈ levelSet F.Carrier a, z ∈ 𝓛 q)
    (hstab : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g)
    (hsupp : ∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier,
      glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) ≠ 0 →
        ((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) ∈ 𝓛 A)
    (s : ℂ) (g : Langlands.GeneralLinear (0 + 1) F.Carrier) (t : Fin (m + 1) → F.Carrierˣ)
    (u : upperUnipotent (m + 1 + 1) F.Carrier) :
    GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
        (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a)) s
        (glModelFunction ψ (m + 1) σ ℓ w) (point ((g, t), u)) =
      (glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) *
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s *
        (torusBox F a).indicator (fun _ => (1 : ℂ)) t) *
        (unipotentBox F q a).indicator (fun _ => (1 : ℂ)) u := by
  have hdw : determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
      (point ((g, t), u)) s =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s := by
    unfold determinantWeight
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_point,
      Matrix.GeneralLinearGroup.val_det_apply]
  simp only [GodementJacquet.matrixIntegrand, coe_compactOpenIndicator]
  rw [hdw]
  by_cases ht : t ∈ torusBox F a
  · have hδ := torusFactor_mem F ha ht
    have hbox : (point ((g, t), u)).val ∈ box F A q a ↔
        ((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) ∈ 𝓛 A ∧
          u ∈ unipotentBox F q a := by
      rw [point_eq_mul F g t u, Units.val_mul, mul_mem_box_iff F hA hq hL _ hδ,
        mem_box_unipotent_mul_iff]
    have hW : glModelFunction ψ (m + 1) σ ℓ w (point ((g, t), u)) =
        (standardCharacter ψ (m + 1) u : ℂ) *
          glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) := by
      rw [point_eq_mul F g t u, hstab _ hδ]
      exact glModelFunction_equivariance ψ (m + 1) σ ℓ w u (rankOneEmbedding m g)
    rw [Set.indicator_of_mem ht, mul_one, hW]
    by_cases hu : u ∈ unipotentBox F q a
    · rw [Set.indicator_of_mem hu, mul_one, standardCharacter_eq_one F ψ hψ hlev hu, one_mul]
      by_cases hg : ((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) ∈ 𝓛 A
      · rw [Set.indicator_of_mem (hbox.2 ⟨hg, hu⟩), one_mul]
      · rw [Set.indicator_of_notMem (fun h => hg (hbox.1 h).1)]
        have h0 : glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) = 0 := by
          by_contra h
          exact hg (hsupp g h)
        rw [h0]
        simp
    · rw [Set.indicator_of_notMem (fun h => hu (hbox.1 h).2), Set.indicator_of_notMem hu]
      simp
  · rw [Set.indicator_of_notMem (fun h => ht (mem_torusBox_of_mem_box F h)),
      Set.indicator_of_notMem ht]
    simp

/-- The `GL₁` density turns the shifted exponent into the rank-one exponent. -/
theorem weight_smul_integrand (s : ℂ) (g : Langlands.GeneralLinear (0 + 1) F.Carrier) :
    weight F (m + 1) (g, 1) • (glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (s + GodementJacquet.jpssShift (m + 1))) =
      rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData) σ ℓ w s g := by
  set r : ℝ := normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det g.val) with hr_def
  have hr : 0 < r := (normalizedAbsoluteValue F.canonicalTopologicalData).pos g.det_ne_zero
  have hw : ((weight F (m + 1) (g, 1) : ℝ≥0) : ℝ) = (r ^ (m + 1))⁻¹ := by
    rw [weight_glOne, NNReal.coe_inv, NNReal.coe_pow,
      F.canonicalTopologicalData.normalizedAbsUnits_coe, Matrix.GeneralLinearGroup.val_det_apply]
    rfl
  rw [rankOneModelIntegrand, NNReal.smul_def, hw, Complex.real_smul]
  unfold determinantWeight
  rw [← hr_def]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hexp : s - ((m + 1 : ℕ) : ℂ) / 2 =
      (s + GodementJacquet.jpssShift (m + 1)) - ((m + 1 : ℕ) : ℂ) := by
    unfold GodementJacquet.jpssShift
    push_cast
    ring
  rw [hexp, Complex.cpow_sub _ _ hr', Complex.cpow_natCast]
  push_cast
  ring

/-- **The box computation.** For a smooth `σ` and a model function `W`, one compact
open box `Φ₀` and one constant `C > 0` give `Z(Φ₀, s + (m+1)/2, W) = C · Ψ(s, W)`
together with absolute convergence, whenever `Ψ(s, W)` converges absolutely. -/
theorem exists_box_constant (hσ : IsSmooth σ) :
    ∃ Φ : GodementJacquet.MatrixTestFunction (m + 1) F.Carrier, ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, Integrable
          (rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData) σ ℓ w s)
          (generalLinearHaar F.Carrier 0) →
        Integrable (GodementJacquet.matrixIntegrand
            (normalizedAbsoluteValue F.canonicalTopologicalData) Φ
            (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w))
          (generalLinearHaar F.Carrier (m + 1)) ∧
        ∫ g, GodementJacquet.matrixIntegrand
            (normalizedAbsoluteValue F.canonicalTopologicalData) Φ
            (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) g
            ∂generalLinearHaar F.Carrier (m + 1) =
          (C : ℂ) * ∫ g, rankOneModelIntegrand ψ
            (normalizedAbsoluteValue F.canonicalTopologicalData) σ ℓ w s g
            ∂generalLinearHaar F.Carrier 0 := by
  obtain ⟨A₀, hA₀⟩ := exists_rankOneEmbedding_support F.canonicalTopologicalData ψ σ hσ ℓ w
  have hA : 0 ≤ max A₀ 0 := le_max_right _ _
  have hsupp : ∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier,
      glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) ≠ 0 →
        ((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) ∈ 𝓛 (max A₀ 0) :=
    fun g h => lattice_mono F (le_max_left _ _) (hA₀ g h)
  have hq : min (F.canonicalTopologicalData.additiveConductor ψ) 0 ≤ 0 := min_le_right _ _
  have hψ : ∀ z ∈ 𝓛 (min (F.canonicalTopologicalData.additiveConductor ψ) 0), ψ z = 1 :=
    (F.canonicalTopologicalData.additiveTrivialAt_iff_le_conductor ψ _).2 (min_le_left _ _)
  set A : ℤ := max A₀ 0 with hAdef
  set q : ℤ := min (F.canonicalTopologicalData.additiveConductor ψ) 0 with hqdef
  obtain ⟨Kw, hKw⟩ := glModel_isSmooth ψ (m + 1) σ hσ ℓ w
  have hrow : IsOpen {g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier |
      ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} := by
    have h : {g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier |
        ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} =
        ⋂ j, ⋂ (_ : j ≠ 0), (fun g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier =>
          g.val 0 j) ⁻¹' (𝓛 (q - A) : Set F.Carrier) := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rw [h]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
      (isOpen_lattice F _).preimage (Units.continuous_val.matrix_elem 0 j)
  have hU : (Kw : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)) ∩
      {g | ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} ∈
        𝓝 (1 : Langlands.GeneralLinear (m + 1 + 1) F.Carrier) := by
    refine Filter.inter_mem (Kw.isOpen.mem_nhds Kw.one_mem) (hrow.mem_nhds fun j hj => ?_)
    change (1 : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F.Carrier) 0 j ∈ 𝓛 (q - A)
    rw [Matrix.one_apply_ne (Ne.symm hj)]
    exact zero_mem _
  obtain ⟨a, ha, haU⟩ := exists_pos_principalLevelOpenSubgroup_subset F.Carrier (m + 1) hU
  have hmemU : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a,
      y ∈ (Kw : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)) ∩
        {g | ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} := fun y hy => haU hy
  have hL : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ j, j ≠ 0 →
      y.val 0 j ∈ 𝓛 (q - A) := fun y hy => (hmemU y hy).2
  have hstab : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g := by
    intro y hy g
    have hfix : glModelRepresentation ψ (m + 1) σ ℓ y w = w := hKw ⟨y, (hmemU y hy).1⟩
    rw [← glModelFunction_translate, hfix]
  have hlev : ∀ z ∈ levelSet F.Carrier a, z ∈ 𝓛 q := by
    intro z hz
    obtain ⟨E, hE, hEv⟩ := exists_mem_principalLevelSubgroup ha
      (1 + Matrix.single (0 : Fin (m + 1 + 1)) (Fin.succ 0) z) (by
        intro i l
        rw [Matrix.add_apply, add_sub_cancel_left, Matrix.single_apply]
        split_ifs
        · exact hz
        · exact zero_mem_levelSet a)
    have h := hL E hE (Fin.succ 0) (Fin.succ_ne_zero 0)
    have he : E.val 0 (Fin.succ 0) = z := by
      rw [hEv, Matrix.add_apply, Matrix.one_apply_ne (Fin.succ_ne_zero 0).symm,
        Matrix.single_apply_same, zero_add]
    rw [he] at h
    exact lattice_mono F (by omega) h
  have hSm : MeasurableSet (boxSupport F (n := m + 1) A q a) :=
    (isOpen_boxSupport F A q a).measurableSet
  have hTm : MeasurableSet (torusBox F (n := m + 1) a) := (isOpen_torusBox F ha _).measurableSet
  have hUm : MeasurableSet (unipotentBox F (n := m + 1) q a) :=
    (isOpen_unipotentBox F q a).measurableSet
  have hC : 0 < ((generalLinearHaar F.Carrier (m + 1)).restrict
      (integralSubgroup (ValuativeRel.valuation F.Carrier).integer (m + 1) :
        Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))).real (boxSupport F A q a) *
      ((tailMeasure F (m + 1)).real (torusBox F a) *
        (unipotentHaar F.Carrier (m + 1)).real (unipotentBox F q a)) := by
    refine mul_pos ?_ (mul_pos ?_ ?_)
    · exact ENNReal.toReal_pos (restrict_boxSupport_pos F hA).ne'
        (restrict_boxSupport_lt_top F A q a).ne
    · exact ENNReal.toReal_pos (tailMeasure_torusBox_pos F ha _).ne'
        (tailMeasure_torusBox_lt_top F ha _).ne
    · exact ENNReal.toReal_pos (unipotentHaar_unipotentBox_pos F q a).ne'
        (unipotentHaar_unipotentBox_lt_top F hq a).ne
  refine ⟨compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a), _, hC,
    fun s hs => ?_⟩
  set H := GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
    (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a))
    (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) with hH
  set Fg : Langlands.GeneralLinear (0 + 1) F.Carrier → ℂ := fun g =>
    glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (s + GodementJacquet.jpssShift (m + 1)) with hFg_def
  have hHc : Continuous H :=
    (((compactOpenIndicator (box F A q a) (isCompact_box F A q a)
      (isOpen_box F A q a)).locallyConstant.continuous.comp Units.continuous_val).mul
        (continuous_glModelFunction F ψ σ hσ ℓ w)).mul (continuous_determinantWeight F _ _)
  have hFgc : Continuous Fg :=
    ((continuous_glModelFunction F ψ σ hσ ℓ w).comp (continuous_rankOneEmbedding F m)).mul
      (continuous_determinantWeight F _ _)
  have hin : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer (m + 1),
      k ∈ boxSupport F A q a →
      ∃ r : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin (m + 1) → F.Carrierˣ)) ×
          upperUnipotent (m + 1 + 1) F.Carrier →
        (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin (m + 1) → F.Carrierˣ)) ×
          upperUnipotent (m + 1 + 1) F.Carrier,
        MeasurePreserving r (iwasawaMeasure F (m + 1)) (iwasawaMeasure F (m + 1)) ∧
          ∀ x, H (point x * k) = H (point (r x)) := by
    rintro k hk ⟨-, x₀, hx₀⟩
    obtain ⟨xβ, hβ, y, hy, rfl⟩ := exists_point_mul_of_mem_box F ha hk hx₀
    refine ⟨rshift xβ, measurePreserving_rshift F _ xβ hβ, fun x => ?_⟩
    rw [← mul_assoc, hH, matrixIntegrand_mul_principalLevel F ψ σ ℓ w hA hq hL hstab _ _ hy,
      point_rshift]
  have hout : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer (m + 1),
      k ∉ boxSupport F A q a → ∀ x, H (point x * k) = 0 := by
    intro k hk hkS x
    have hnot : (point x * k).val ∉ box F A q a := fun h => hkS ⟨hk, x, h⟩
    simp only [hH, GodementJacquet.matrixIntegrand, coe_compactOpenIndicator,
      Set.indicator_of_notMem hnot, zero_mul]
  have hpoint : ∀ x, H (point x) =
      (Fg x.1.1 * (torusBox F a).indicator (fun _ => (1 : ℂ)) x.1.2) *
        (unipotentBox F q a).indicator (fun _ => (1 : ℂ)) x.2 := by
    rintro ⟨⟨g, t⟩, u⟩
    exact matrixIntegrand_point F ψ σ ℓ w ha hA hq hL hψ hlev hstab hsupp _ g t u
  have hwm : Measurable fun g : Langlands.GeneralLinear (0 + 1) F.Carrier =>
      weight F (m + 1) (g, 1) :=
    ((continuous_weight F (m + 1)).comp (continuous_id.prodMk continuous_const)).measurable
  have hglOne_l : ∫⁻ g, ‖Fg g‖ₑ ∂glOneMeasure F (m + 1) =
      ∫⁻ g, ‖rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        σ ℓ w s g‖ₑ ∂generalLinearHaar F.Carrier 0 := by
    have hwm' : Measurable fun g : Langlands.GeneralLinear (0 + 1) F.Carrier =>
        ((weight F (m + 1) (g, 1) : ℝ≥0) : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hwm
    rw [glOneMeasure, lintegral_withDensity_eq_lintegral_mul _ hwm' hFgc.measurable.enorm]
    refine lintegral_congr fun g => ?_
    rw [Pi.mul_apply, ← weight_smul_integrand F ψ σ ℓ w s g, NNReal.smul_def, enorm_smul,
      NNReal.enorm_eq]
  have hglOne_i : ∫ g, Fg g ∂glOneMeasure F (m + 1) =
      ∫ g, rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        σ ℓ w s g ∂generalLinearHaar F.Carrier 0 := by
    rw [glOneMeasure, integral_withDensity_eq_integral_smul hwm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
      weight_smul_integrand F ψ σ ℓ w s g)
  have hfin : ∫⁻ g, ‖H g‖ₑ ∂generalLinearHaar F.Carrier (m + 1) < ⊤ := by
    rw [lintegral_enorm_eq_of_support F H hHc _ hSm hin hout,
      lintegral_param_of_eq F H Fg _ _ hTm hUm hpoint hFgc.measurable, hglOne_l]
    exact ENNReal.mul_lt_top (restrict_boxSupport_lt_top F A q a)
      (ENNReal.mul_lt_top hs.2 (ENNReal.mul_lt_top (tailMeasure_torusBox_lt_top F ha _)
        (unipotentHaar_unipotentBox_lt_top F hq a)))
  have hHint : Integrable H (generalLinearHaar F.Carrier (m + 1)) :=
    ⟨hHc.aestronglyMeasurable, hfin⟩
  refine ⟨hHint, ?_⟩
  rw [integral_eq_of_support F H hHc _ hSm hin hout hHint,
    integral_param_of_eq F H Fg _ _ hTm hUm hpoint, hglOne_i, Complex.real_smul]
  push_cast
  ring

/-- Every reduced rank-one value is a matrix–Whittaker value. -/
theorem rankOneModelValues_subset (hσ : IsSmooth σ) :
    rankOneModelValues F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier 0) σ ℓ ⊆
      GodementJacquet.Padic.whittakerRationalValues F ψ σ ℓ := by
  rintro R ⟨w, ⟨a₀, hconv⟩, hrat⟩
  obtain ⟨Φ, C, hC, hΦ⟩ := exists_box_constant F ψ σ ℓ w hσ
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hscale : ∀ s : ℂ, GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue F.canonicalTopologicalData) Φ s
        (glModelFunction ψ (m + 1) σ ℓ (((C : ℂ)⁻¹) • w)) =
      fun g => (C : ℂ)⁻¹ * GodementJacquet.matrixIntegrand
        (normalizedAbsoluteValue F.canonicalTopologicalData) Φ s
          (glModelFunction ψ (m + 1) σ ℓ w) g := by
    intro s
    funext g
    simp only [GodementJacquet.matrixIntegrand]
    have h : glModelFunction ψ (m + 1) σ ℓ (((C : ℂ)⁻¹) • w) g =
        (C : ℂ)⁻¹ * glModelFunction ψ (m + 1) σ ℓ w g := rfl
    rw [h]
    ring
  unfold GodementJacquet.Padic.whittakerRationalValues GodementJacquet.whittakerRationalValues
  refine ⟨Φ, ((C : ℂ)⁻¹) • w, ⟨a₀, fun s hs => ?_⟩, ?_⟩
  · change Integrable _ _
    rw [hscale]
    exact (hΦ s (hconv s hs)).1.const_mul _
  · obtain ⟨a₁, ha₁⟩ := hrat
    refine ⟨max a₀ a₁, fun s hs => ?_⟩
    obtain ⟨hden, heq⟩ := ha₁ s (lt_of_le_of_lt (le_max_right _ _) hs)
    refine ⟨hden, ?_⟩
    rw [← heq]
    change ∫ g, GodementJacquet.matrixIntegrand _ Φ _ _ g ∂_ = _
    rw [hscale, integral_const_mul, (hΦ s (hconv s (lt_of_le_of_lt (le_max_left _ _) hs))).2,
      inv_mul_cancel_left₀ hC']

end Comparison

end Measure

end Langlands.RankinSelberg.RankOneBox

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker

universe uF uV

/-- **Every reduced rank-one value is a matrix–Whittaker value.** For `σ` smooth on
`GL_(m+2)` over a p-adic field and a standard functional `ℓ`, every rational function
continuing an absolutely convergent `GL₁` integral
`∫ W(diag(det g, 1, …, 1)) |det g|^(s - (m+1)/2) dg` of a model function `W` of `ℓ`
is a shifted rational value of a matrix–Whittaker integral of the same model. -/
theorem rankOneModelValues_subset_whittakerRationalValues (p : ℕ) [Fact p.Prime]
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (m : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (Langlands.GeneralLinear (0 + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
    IsSmooth σ → ∀ ℓ : glFunctionals ψ (m + 1) σ,
      rankOneModelValues F.canonicalTopologicalData.residueCardinality ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData)
          (generalLinearHaar F.Carrier 0) σ ℓ ⊆
        GodementJacquet.Padic.whittakerRationalValues F ψ σ ℓ :=
  fun hσ ℓ => RankOneBox.rankOneModelValues_subset F ψ σ ℓ hσ

end Langlands.RankinSelberg
