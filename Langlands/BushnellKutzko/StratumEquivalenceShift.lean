import Langlands.BushnellKutzko.StratumEquivalenceSplitting
import Langlands.BushnellKutzko.SubfieldIntegerArithmetic
import Langlands.BushnellKutzko.LatticeChainShifts
import Langlands.BushnellKutzko.CorestrictionLatticeDual

/-! # Lattice shifts of a normalizing field

Helper results for `StratumEquivalenceStatement`. Let `E` be a finite field extension of
`F` acting on `V` with `E^×` normalizing an `𝔬_F`-lattice chain `𝓛`. Each nonzero `a ∈ E`
moves the chain by an integer `shift a`; this file shows that `shift` is `e' · v_E`, where
`e' = shift ϖ_E > 0`, that `e(E|F) · e' = e(𝓛)`, and that a nonzero element lies in `𝔬_E`
(respectively `𝔭_E`) exactly when its shift is at least `0` (respectively `1`). The zero
element, which has shift `0` by convention, lies in both `𝔬_E` and `𝔭_E`, so both criteria
carry a nonzero hypothesis.
-/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

namespace StratumEquivalence

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

local notation "L" => 𝓛.lattice

/-- `v` lies in `L_i` but not in `L_{i+1}`. -/
def ExactDepth (v : V) (i : ℤ) : Prop :=
  v ∈ L i ∧ v ∉ L (i + 1)

omit [Algebra F E] [Module E V] [IsScalarTower F E V] in
theorem ExactDepth.le {v : V} {i j : ℤ} (hv : ExactDepth 𝓛 v i) (hj : v ∈ L j) : j ≤ i := by
  by_contra! h
  exact hv.2 (𝓛.antitone (show i + 1 ≤ j by omega) hj)

omit [Algebra F E] [Module E V] [IsScalarTower F E V] in
theorem ExactDepth.unique {v : V} {i j : ℤ} (hi : ExactDepth 𝓛 v i) (hj : ExactDepth 𝓛 v j) :
    i = j :=
  le_antisymm (hj.le 𝓛 hi.1) (hi.le 𝓛 hj.1)

open scoped Classical in
/-- The shift of a field element, `0` at `0`. -/
def shift (a : E) : ℤ :=
  if h : a = 0 then 0 else (𝓛.fieldShift E hE (Units.mk0 a h)).toAdd

theorem shift_of_ne_zero {a : E} (ha : a ≠ 0) :
    shift 𝓛 hE a = (𝓛.fieldShift E hE (Units.mk0 a ha)).toAdd := by
  simp [shift, ha]

theorem smul_mem_shift_iff {a : E} (ha : a ≠ 0) (i : ℤ) (v : V) :
    a • v ∈ L (i + shift 𝓛 hE a) ↔ v ∈ L i := by
  rw [shift_of_ne_zero 𝓛 hE ha]
  exact 𝓛.mem_lattice_fieldShift E hE (Units.mk0 a ha) i

theorem ExactDepth.smul {a : E} (ha : a ≠ 0) {v : V} {i : ℤ} (hv : ExactDepth 𝓛 v i) :
    ExactDepth 𝓛 (a • v) (i + shift 𝓛 hE a) := by
  refine ⟨(smul_mem_shift_iff 𝓛 hE ha i v).mpr hv.1, fun h => hv.2 ?_⟩
  rw [show i + shift 𝓛 hE a + 1 = (i + 1) + shift 𝓛 hE a by ring] at h
  exact (smul_mem_shift_iff 𝓛 hE ha (i + 1) v).mp h

theorem smul_mem_of_shift_le {a : E} (ha : a ≠ 0) {i j : ℤ} (hj : j ≤ i + shift 𝓛 hE a)
    {v : V} (hv : v ∈ L i) : a • v ∈ L j :=
  𝓛.antitone hj ((smul_mem_shift_iff 𝓛 hE ha i v).mpr hv)

theorem shift_mul {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    shift 𝓛 hE (a * b) = shift 𝓛 hE a + shift 𝓛 hE b := by
  rw [shift_of_ne_zero 𝓛 hE (mul_ne_zero ha hb), shift_of_ne_zero 𝓛 hE ha,
    shift_of_ne_zero 𝓛 hE hb]
  have h : Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb :=
    Units.ext rfl
  rw [h, map_mul, toAdd_mul]

theorem shift_one : shift 𝓛 hE (1 : E) = 0 := by
  rw [shift_of_ne_zero 𝓛 hE one_ne_zero]
  have h : Units.mk0 (1 : E) one_ne_zero = 1 := Units.ext rfl
  rw [h, map_one, toAdd_one]

theorem shift_inv {a : E} (ha : a ≠ 0) : shift 𝓛 hE a⁻¹ = -shift 𝓛 hE a := by
  have h := shift_mul 𝓛 hE (inv_ne_zero ha) ha
  rw [inv_mul_cancel₀ ha, shift_one] at h
  omega

theorem shift_pow {a : E} (ha : a ≠ 0) (n : ℕ) : shift 𝓛 hE (a ^ n) = n * shift 𝓛 hE a := by
  induction n with
  | zero => simp [shift_one]
  | succ n ih =>
    rw [pow_succ, shift_mul 𝓛 hE (pow_ne_zero n ha) ha, ih]
    push_cast
    ring

/-- The shift is determined by the image of `L_0`. -/
theorem shift_eq_of {a : E} (ha : a ≠ 0) {d : ℤ} (h : ∀ v : V, a • v ∈ L d ↔ v ∈ L 0) :
    shift 𝓛 hE a = d := by
  have hL : L (0 + shift 𝓛 hE a) = L d := by
    ext y
    have hy : a • (a⁻¹ • y) = y := smul_inv_smul₀ ha y
    rw [← hy, smul_mem_shift_iff 𝓛 hE ha 0, h]
  simpa using 𝓛.injective hL

section Integers

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

local notation "𝔬" => subfieldIntegers F E

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isScalarTower_integer : IsScalarTower 𝒪[F] E V := by
  refine ⟨fun r a v => ?_⟩
  have h1 : r • a = (r : F) • a := rfl
  have h2 : r • (a • v) = (r : F) • (a • v) := rfl
  rw [h1, h2, smul_assoc]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Integral elements have nonnegative shift. -/
theorem shift_nonneg_of_mem {a : E} (ha : a ∈ 𝔬) : 0 ≤ shift 𝓛 hE a := by
  by_cases h0 : a = 0
  · simp [shift, h0]
  have := isScalarTower_integer (F := F) (E := E) (V := V)
  have h := 𝓛.fieldShift_nonneg_of_integral E hE (Units.mk0 a h0) ha
  rwa [shift_of_ne_zero 𝓛 hE h0]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Units of `𝔬_E` have shift zero. -/
theorem shift_unit (u : (𝔬)ˣ) : shift 𝓛 hE ((u : 𝔬) : E) = 0 := by
  have hu : ((u : 𝔬) : E) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have h1 := shift_nonneg_of_mem 𝓛 hE (u : 𝔬).2
  have h2 := shift_nonneg_of_mem 𝓛 hE ((u⁻¹ : (𝔬)ˣ) : 𝔬).2
  have hinv : (((u⁻¹ : (𝔬)ˣ) : 𝔬) : E) = ((u : 𝔬) : E)⁻¹ :=
    eq_inv_of_mul_eq_one_left (congrArg Subtype.val u.inv_mul)
  rw [hinv, shift_inv 𝓛 hE hu] at h2
  omega

variable [FiniteDimensional F E]

/-- The data attached to a uniformizer `ϖ_E`: its shift `e'` and the representation of every
nonzero element as `u ϖ_E^{±n}`. -/
theorem exists_unit_pow {ϖ : 𝔬} (hϖ : Irreducible ϖ) {a : E} (ha : a ≠ 0) :
    ∃ (n : ℕ) (u : (𝔬)ˣ), a = (u : 𝔬) * (ϖ : E) ^ n ∨ a⁻¹ = (u : 𝔬) * (ϖ : E) ^ n := by
  have := subfieldIntegers_isDiscreteValuationRing F E
  have := subfieldIntegers_isFractionRing F E
  rcases ValuationRing.isInteger_or_isInteger (𝔬) a with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact ha (by simpa using hx.symm)
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    exact ⟨n, u, Or.inl (by rw [← hx]; rfl)⟩
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact (inv_ne_zero ha) (by simpa using hx.symm)
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    exact ⟨n, u, Or.inr (by rw [← hx]; rfl)⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
theorem shift_unit_mul_pow {ϖ : 𝔬} (hϖ : Irreducible ϖ) (u : (𝔬)ˣ) (n : ℕ) :
    shift 𝓛 hE (((u : 𝔬) : E) * (ϖ : E) ^ n) = n * shift 𝓛 hE (ϖ : E) := by
  have hϖ0 : (ϖ : E) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hu : ((u : 𝔬) : E) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  rw [shift_mul 𝓛 hE hu (pow_ne_zero n hϖ0), shift_unit, shift_pow 𝓛 hE hϖ0, zero_add]

/-- `e(E|F) · e' = e(𝓛)`, where `e'` is the shift of a uniformizer of `𝔬_E`. -/
theorem ramificationIndex_mul_shift {ϖ : 𝔬} (hϖ : Irreducible ϖ) :
    (subfieldRamificationIndex F E : ℤ) * shift 𝓛 hE (ϖ : E) = 𝓛.period := by
  have := subfieldIntegers_isDiscreteValuationRing F E
  have := isScalarTower_integer (F := F) (E := E) (V := V)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨u, hu⟩ := baseUniformizer_factorization F E hπ hϖ
  have hπE : algebraMap 𝒪[F] E π =
      ((u : 𝔬) : E) * (ϖ : E) ^ subfieldRamificationIndex F E :=
    congrArg Subtype.val hu
  have hϖ0 : (ϖ : E) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hu0 : ((u : 𝔬) : E) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have hsh : shift 𝓛 hE (((u : 𝔬) : E) * (ϖ : E) ^ subfieldRamificationIndex F E) =
      𝓛.period := by
    apply shift_eq_of 𝓛 hE (mul_ne_zero hu0 (pow_ne_zero _ hϖ0))
    intro v
    rw [← hπE, algebraMap_smul]
    have h := 𝓛.uniformizer_lattice_mem_iff hπ 0 v
    rw [zero_add] at h
    exact h
  rw [shift_unit_mul_pow 𝓛 hE hϖ] at hsh
  exact hsh

/-- The shift `e'` of a uniformizer is positive. -/
theorem shift_uniformizer_pos {ϖ : 𝔬} (hϖ : Irreducible ϖ) : 0 < shift 𝓛 hE (ϖ : E) := by
  have h := ramificationIndex_mul_shift 𝓛 hE hϖ
  have h0 := shift_nonneg_of_mem 𝓛 hE ϖ.2
  have hp : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  rcases h0.lt_or_eq with h0 | h0
  · exact h0
  · rw [← h0, mul_zero] at h
    omega

/-- Every shift is a multiple of `e'`. -/
theorem shift_uniformizer_dvd {ϖ : 𝔬} (hϖ : Irreducible ϖ) {a : E} (ha : a ≠ 0) :
    shift 𝓛 hE (ϖ : E) ∣ shift 𝓛 hE a := by
  obtain ⟨n, u, h | h⟩ := exists_unit_pow hϖ ha
  · rw [h, shift_unit_mul_pow 𝓛 hE hϖ]
    exact Dvd.intro_left _ rfl
  · have hinv := shift_inv 𝓛 hE ha
    rw [h, shift_unit_mul_pow 𝓛 hE hϖ] at hinv
    rw [show shift 𝓛 hE a = -(n * shift 𝓛 hE (ϖ : E)) by omega]
    exact (Dvd.intro_left _ rfl).neg_right

/-- A nonzero element lies in `𝔬_E` exactly when its shift is nonnegative. -/
theorem mem_integers_iff {ϖ : 𝔬} (hϖ : Irreducible ϖ) {a : E} (ha : a ≠ 0) :
    a ∈ 𝔬 ↔ 0 ≤ shift 𝓛 hE a := by
  refine ⟨shift_nonneg_of_mem 𝓛 hE, fun hs => ?_⟩
  have hpos := shift_uniformizer_pos 𝓛 hE hϖ
  obtain ⟨n, u, h | h⟩ := exists_unit_pow hϖ ha
  · rw [h]
    exact mul_mem (u : 𝔬).2 (pow_mem ϖ.2 n)
  · have hinv := shift_inv 𝓛 hE ha
    rw [h, shift_unit_mul_pow 𝓛 hE hϖ] at hinv
    have hn : n = 0 := by
      by_contra hn
      have : (1 : ℤ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      nlinarith
    rw [hn, pow_zero, mul_one] at h
    have ha' : a = (((u⁻¹ : (𝔬)ˣ) : 𝔬) : E) := by
      rw [← inv_inv a, h]
      exact (eq_inv_of_mul_eq_one_left (congrArg Subtype.val u.inv_mul)).symm
    rw [ha']
    exact ((u⁻¹ : (𝔬)ˣ) : 𝔬).2

/-- A nonzero element of `𝔬_E` lies in `𝔭_E` exactly when its shift is at least one. -/
theorem mem_maximalIdeal_iff {ϖ : 𝔬} (hϖ : Irreducible ϖ) {x : 𝔬} (hx : x ≠ 0) :
    x ∈ subfieldMaximalIdeal F E ↔ 1 ≤ shift 𝓛 hE (x : E) := by
  have := subfieldIntegers_isDiscreteValuationRing F E
  have hpos := shift_uniformizer_pos 𝓛 hE hϖ
  rw [subfieldMaximalIdeal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  have hsh : shift 𝓛 hE (((u * ϖ ^ n : 𝔬)) : E) = n * shift 𝓛 hE (ϖ : E) :=
    shift_unit_mul_pow 𝓛 hE hϖ u n
  rw [hsh]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have h1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
    refine ⟨fun _ => by nlinarith, fun _ => ?_⟩
    rw [Units.isUnit_units_mul, isUnit_pow_iff hn.ne']
    exact hϖ.not_isUnit

end Integers

end StratumEquivalence

end Langlands.BushnellKutzko
