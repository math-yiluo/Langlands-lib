import Langlands.Representation.Conductor.SphericalCyclicity.Lattice

/-!
# The extensions by zero generate the principal series

A subrepresentation of the principal series of rank `n + 2` containing every extension by
zero of the principal series of rank `n + 1` is everything.  A function `f` fixed by the
principal congruence subgroup `K_a` is cut into finitely many pieces supported on sets
`B K_a κ` (`κ` integral); a translate of each piece is supported on `B K_a`, and the
translate by `diag(ϖ^(a-1), 1, …, 1)` of a function supported on `B K_a` is an extension by
zero.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCyclicity

open Matrix Langlands.GeneralLinear Langlands.Conductor
open Langlands.Conductor.UnramifiedPrincipalSeries Langlands.Induction
open scoped BigOperators

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F]

set_option quotPrecheck false in
local notation "𝒱" => ValuativeRel.valuation F
set_option quotPrecheck false in
local notation "𝒪" => (ValuativeRel.valuation F).integer

/-! ### Normality of principal congruence subgroups -/

/-- A principal congruence subgroup is normalized by the integral group. -/
theorem conj_mem_principalLevel {m a : ℕ} {κ k : GL (Fin (m + 1)) F}
    (hκ : κ ∈ integralSubgroup 𝒪 m) (hk : k ∈ principalLevelSubgroup F m a) :
    κ * k * κ⁻¹ ∈ principalLevelSubgroup F m a := by
  obtain ⟨h₀, rfl⟩ := hκ
  obtain ⟨k₀, hk₀, rfl⟩ := hk
  refine ⟨h₀ * k₀ * h₀⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  change Matrix.GeneralLinearGroup.map
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪 ^ a)) k₀ = 1 at hk₀
  change Matrix.GeneralLinearGroup.map
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪 ^ a)) (h₀ * k₀ * h₀⁻¹) = 1
  simp only [map_mul, map_inv, hk₀, mul_one, mul_inv_cancel]

/-! ### The sets `B K_a` -/

/-- The set `B K_a` of products of an upper-triangular matrix and an element of the
principal congruence subgroup of level `a`. -/
def InBK (m a : ℕ) (x : GL (Fin (m + 1)) F) : Prop :=
  ∃ b : Borel (F := F) m, ∃ k ∈ principalLevelSubgroup F m a, x = b.val * k

theorem inBK_borel_mul_iff {m a : ℕ} (b : Borel (F := F) m) (x : GL (Fin (m + 1)) F) :
    InBK m a (b.val * x) ↔ InBK m a x := by
  constructor
  · rintro ⟨b', k, hk, e⟩
    refine ⟨b⁻¹ * b', k, hk, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, ← e, inv_mul_cancel_left]
  · rintro ⟨b', k, hk, rfl⟩
    exact ⟨b * b', k, hk, by rw [Subgroup.coe_mul, mul_assoc]⟩

theorem inBK_mul_iff {m a : ℕ} {k : GL (Fin (m + 1)) F}
    (hk : k ∈ principalLevelSubgroup F m a) (x : GL (Fin (m + 1)) F) :
    InBK m a (x * k) ↔ InBK m a x := by
  constructor
  · rintro ⟨b, k', hk', e⟩
    refine ⟨b, k' * k⁻¹, mul_mem hk' (inv_mem hk), ?_⟩
    rw [← mul_assoc, ← e, mul_inv_cancel_right]
  · rintro ⟨b, k', hk', rfl⟩
    exact ⟨b, k' * k, mul_mem hk' hk, by rw [mul_assoc]⟩

theorem inBK_translate_iff {m a : ℕ} {κ k : GL (Fin (m + 1)) F}
    (hκ : κ ∈ integralSubgroup 𝒪 m) (hk : k ∈ principalLevelSubgroup F m a)
    (x : GL (Fin (m + 1)) F) : InBK m a (x * k * κ⁻¹) ↔ InBK m a (x * κ⁻¹) := by
  have e : x * k * κ⁻¹ = x * κ⁻¹ * (κ * k * κ⁻¹) := by group
  rw [e, inBK_mul_iff (conj_mem_principalLevel hκ hk)]

/-! ### Finitely many cosets -/

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The integral group is covered by finitely many cosets `K_a κ`. -/
theorem exists_cover (m a : ℕ) : ∃ T : Finset (integralSubgroup 𝒪 m),
    ∀ k ∈ integralSubgroup 𝒪 m, ∃ κ ∈ T,
      k * (κ : GL (Fin (m + 1)) F)⁻¹ ∈ principalLevelSubgroup F m a := by
  have hK : IsCompact ((principalLevelSubgroup F m 0 : Subgroup (GL (Fin (m + 1)) F)) :
      Set (GL (Fin (m + 1)) F)) := isCompact_principalLevelOpenSubgroup F m 0
  rw [principalLevelSubgroup_zero] at hK
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover
    (fun κ : integralSubgroup 𝒪 m => (fun x => x * (κ : GL (Fin (m + 1)) F)⁻¹) ⁻¹'
      ((principalLevelOpenSubgroup F m a : Set (GL (Fin (m + 1)) F))))
    (fun κ => (principalLevelOpenSubgroup F m a).isOpen.preimage (continuous_id.mul continuous_const))
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, by
      show k * k⁻¹ ∈ (principalLevelOpenSubgroup F m a : Set (GL (Fin (m + 1)) F))
      rw [mul_inv_cancel]
      exact (principalLevelOpenSubgroup F m a).one_mem⟩)
  refine ⟨T, fun k hk => ?_⟩
  have := hT hk
  simp only [Set.mem_iUnion, Set.mem_preimage] at this
  obtain ⟨κ, hκ, h⟩ := this
  exact ⟨κ, hκ, h⟩

/-! ### Cutting off principal-series functions -/

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

theorem ext_value {m q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    {f g : PrincipalSeries hϖ m hq z} (h : ∀ x, value hϖ m f x = value hϖ m g x) : f = g :=
  Subtype.ext (Subtype.ext (funext h))

theorem value_sub {m q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    (f g : PrincipalSeries hϖ m hq z) (x : GL (Fin (m + 1)) F) :
    value hϖ m (f - g) x = value hϖ m f x - value hϖ m g x :=
  map_sub (evalAt hϖ hq z x) f g

theorem value_zero {m q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    (x : GL (Fin (m + 1)) F) : value hϖ m (0 : PrincipalSeries hϖ m hq z) x = 0 :=
  map_zero (evalAt hϖ hq z x)

open Classical in
/-- The product of a principal-series function by the indicator function of a set that is
left invariant under the Borel subgroup and right invariant under `K_a`. -/
def cut {m q a : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    (U : GL (Fin (m + 1)) F → Prop)
    (hB : ∀ (b : Borel (F := F) m) x, U (b.val * x) ↔ U x)
    (hU : ∀ k ∈ principalLevelSubgroup F m a, ∀ x, U (x * k) ↔ U x)
    (f : PrincipalSeries hϖ m hq z)
    (hf : ∀ k ∈ principalLevelSubgroup F m a, ∀ x, value hϖ m f (x * k) = value hϖ m f x) :
    PrincipalSeries hϖ m hq z :=
  smoothFunctionOf _ _ (fun x => if U x then value hϖ m f x else 0)
    (fun b x => by
      show (if U (b.val * x) then value hϖ m f (b.val * x) else 0) =
        (normalizedCharacter hϖ m hq z b : ℂ) * (if U x then value hϖ m f x else 0)
      by_cases hx : U x
      · rw [if_pos ((hB b x).2 hx), if_pos hx, value_borel_mul]
      · rw [if_neg (fun h => hx ((hB b x).1 h)), if_neg hx, mul_zero])
    (principalLevelOpenSubgroup F m a)
    (fun k x => by
      show (if U (x * k.val) then value hϖ m f (x * k.val) else 0) =
        (if U x then value hϖ m f x else 0)
      by_cases hx : U x
      · rw [if_pos ((hU _ k.property x).2 hx), if_pos hx, hf _ k.property]
      · rw [if_neg (fun h => hx ((hU _ k.property x).1 h)), if_neg hx])

open Classical in
theorem value_cut {m q a : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    (U : GL (Fin (m + 1)) F → Prop)
    (hB : ∀ (b : Borel (F := F) m) x, U (b.val * x) ↔ U x)
    (hU : ∀ k ∈ principalLevelSubgroup F m a, ∀ x, U (x * k) ↔ U x)
    (f : PrincipalSeries hϖ m hq z)
    (hf : ∀ k ∈ principalLevelSubgroup F m a, ∀ x, value hϖ m f (x * k) = value hϖ m f x)
    (x : GL (Fin (m + 1)) F) :
    value hϖ m (cut hϖ U hB hU f hf) x = if U x then value hϖ m f x else 0 :=
  rfl

theorem cut_mul {m q a : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    (U : GL (Fin (m + 1)) F → Prop)
    (hB : ∀ (b : Borel (F := F) m) x, U (b.val * x) ↔ U x)
    (hU : ∀ k ∈ principalLevelSubgroup F m a, ∀ x, U (x * k) ↔ U x)
    (f : PrincipalSeries hϖ m hq z)
    (hf : ∀ k ∈ principalLevelSubgroup F m a, ∀ x, value hϖ m f (x * k) = value hϖ m f x) :
    ∀ k ∈ principalLevelSubgroup F m a, ∀ x,
      value hϖ m (cut hϖ U hB hU f hf) (x * k) = value hϖ m (cut hϖ U hB hU f hf) x := by
  intro k hk x
  rw [value_cut, value_cut]
  by_cases hx : U x
  · rw [if_pos ((hU _ hk x).2 hx), if_pos hx, hf _ hk]
  · rw [if_neg (fun h => hx ((hU _ hk x).1 h)), if_neg hx]

/-- Right translation by an integral matrix preserves invariance under `K_a`. -/
theorem translate_right_inv {m q a : ℕ} {hq : IsResidueCardinality (F := F) q}
    {z : Fin (m + 1) → ℂˣ} {κ : GL (Fin (m + 1)) F} (hκ : κ ∈ integralSubgroup 𝒪 m)
    (f : PrincipalSeries hϖ m hq z)
    (hf : ∀ k ∈ principalLevelSubgroup F m a, ∀ x, value hϖ m f (x * k) = value hϖ m f x) :
    ∀ k ∈ principalLevelSubgroup F m a, ∀ x,
      value hϖ m (principalSeries hϖ m hq z κ f) (x * k) =
        value hϖ m (principalSeries hϖ m hq z κ f) x := by
  intro k hk x
  rw [rightTranslation, rightTranslation]
  have e : x * k * κ = x * κ * (κ⁻¹ * k * κ⁻¹⁻¹) := by group
  rw [e, hf _ (conj_mem_principalLevel (inv_mem hκ) hk)]

/-! ### Explicit matrices -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem lowerUnip_mul_blockDiag_one {m : ℕ} (y : Fin m → F) (α : Fˣ) :
    lowerUnip y * blockDiag α (1 : GL (Fin m) F) =
      blockDiag α 1 * lowerUnip ((α : F) • y) := by
  apply Units.ext
  simp only [Units.val_mul, lowerUnip_val, blockDiag_val, blk_mul]
  congr 1 <;> simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockDiag_one_mul_comm {m : ℕ} (h : GL (Fin m) F) (α : Fˣ) :
    blockDiag 1 h * blockDiag α 1 = blockDiag α 1 * blockDiag 1 h := by
  simp only [blockDiag_mul, one_mul, mul_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem lowGL_blockDiag {n : ℕ} (α : Fˣ) (h : GL (Fin (n + 1)) F) :
    lowGL (blockDiag α h) = h := by
  have hu : IsUnit (low (blockDiag α h).val).det := by
    rw [low_blockDiag]
    exact (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  apply Units.ext
  rw [lowGL_val hu, low_blockDiag]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem lowerUnip_mem_principalLevel {n a : ℕ} {y : Fin (n + 1) → F}
    (hy : ∀ i, 𝒱 (y i) ≤ 𝒱 (ϖ : F) ^ a) :
    lowerUnip y ∈ principalLevelSubgroup F (n + 1) a := by
  have key : ∀ y' : Fin (n + 1) → F, (∀ i, 𝒱 (y' i) ≤ 𝒱 (ϖ : F) ^ a) →
      ∀ i j, 𝒱 ((lowerUnip y' : GL (Fin (n + 2)) F).val i j -
        (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) i j) ≤ 𝒱 (ϖ : F) ^ a := by
    intro y' hy' i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Matrix.one_apply_ne (Fin.succ_ne_zero j).symm]
    · simpa [Matrix.one_apply_ne (Fin.succ_ne_zero i)] using hy' i
    · rw [one_succ_succ, lowerUnip_val, blk_succ_succ, sub_self, map_zero]
      exact zero_le
  refine (mem_principalLevelSubgroup_iff hϖ _).2 ⟨key y hy, ?_⟩
  rw [lowerUnip_inv]
  exact key (-y) (fun i => by rw [Pi.neg_apply, Valuation.map_neg]; exact hy i)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem blockDiag_one_mem_principalLevel {n a : ℕ} {h : GL (Fin (n + 1)) F}
    (hh : h ∈ principalLevelSubgroup F n a) :
    blockDiag 1 h ∈ principalLevelSubgroup F (n + 1) a := by
  have key : ∀ h' : GL (Fin (n + 1)) F, h' ∈ principalLevelSubgroup F n a →
      ∀ i j, 𝒱 ((blockDiag 1 h' : GL (Fin (n + 2)) F).val i j -
        (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) i j) ≤ 𝒱 (ϖ : F) ^ a := by
    intro h' hh' i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Matrix.one_apply_ne (Fin.succ_ne_zero j).symm]
    · simp [Matrix.one_apply_ne (Fin.succ_ne_zero i)]
    · rw [one_succ_succ, blockDiag_val, blk_succ_succ]
      exact ((mem_principalLevelSubgroup_iff hϖ h').1 hh').1 i j
  refine (mem_principalLevelSubgroup_iff hϖ _).2 ⟨key h hh, ?_⟩
  rw [blockDiag_inv, inv_one]
  exact key h⁻¹ (inv_mem hh)

variable {n : ℕ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem val_cellVec_le {a : ℕ} (ha : 0 < a) {k : GL (Fin (n + 2)) F}
    (hk : k ∈ principalLevelSubgroup F (n + 1) a) (i : Fin (n + 1)) :
    𝒱 (cellVec k i) ≤ 𝒱 (ϖ : F) ^ a := by
  have hu := mem_parahoric_of_principalLevel hϖ ha hk
  have hunit := isUnit_det_low_of_parahoric hϖ hu
  have hint := lowGL_mem_integral_of_parahoric hϖ hu
  have hinv : (low k.val)⁻¹ = ((lowGL k)⁻¹ : GL (Fin (n + 1)) F).val := by
    rw [Matrix.coe_units_inv, lowGL_val hunit]
  have hc : ∀ j, 𝒱 (colT k.val j) ≤ 𝒱 (ϖ : F) ^ a := by
    intro j
    have := ((mem_principalLevelSubgroup_iff hϖ k).1 hk).1 j.succ 0
    rwa [Matrix.one_apply_ne (Fin.succ_ne_zero j), sub_zero] at this
  rw [cellVec, hinv]
  simp only [mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul]
  calc 𝒱 (((lowGL k)⁻¹ : GL (Fin (n + 1)) F).val i j) * 𝒱 (colT k.val j)
      ≤ 1 * 𝒱 (ϖ : F) ^ a :=
        mul_le_mul' (val_le_one_of_mem (integral_entry (inv_mem hint) i j)) (hc j)
    _ = 𝒱 (ϖ : F) ^ a := one_mul _

/-- The element `diag(ϖ^(a-1), 1, …, 1)`. -/
def tHead (ϖ : Fˣ) (a : ℕ) : GL (Fin (n + 2)) F := blockDiag (ϖ ^ (a - 1)) 1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem inCell_mul_tHead_inv {a : ℕ} (ha : 0 < a) {k : GL (Fin (n + 2)) F}
    (hk : k ∈ principalLevelSubgroup F (n + 1) a) : InCell (k * (tHead ϖ a)⁻¹) := by
  have hu := mem_parahoric_of_principalLevel hϖ ha hk
  rw [tHead, blockDiag_inv, inv_one]
  refine ⟨(isUnit_det_low_mul_blockDiag _ _ _).2 (isUnit_det_low_of_parahoric hϖ hu),
    fun i => ?_⟩
  rw [cellVec_mul_blockDiag, inv_one, Units.val_one, one_mulVec, Pi.smul_apply, smul_eq_mul,
    map_mul]
  have hpow : 𝒱 (ϖ : F) ^ a = 𝒱 (((ϖ ^ (a - 1) : Fˣ) : F)) * 𝒱 (ϖ : F) := by
    rw [Units.val_pow_eq_pow_val, map_pow, ← pow_succ, Nat.sub_add_cancel ha]
  have hinv : 𝒱 ((((ϖ ^ (a - 1))⁻¹ : Fˣ) : F)) * 𝒱 (((ϖ ^ (a - 1) : Fˣ) : F)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc 𝒱 ((((ϖ ^ (a - 1))⁻¹ : Fˣ) : F)) * 𝒱 (cellVec k i)
      ≤ 𝒱 ((((ϖ ^ (a - 1))⁻¹ : Fˣ) : F)) * 𝒱 (ϖ : F) ^ a :=
        mul_le_mul' le_rfl (val_cellVec_le hϖ ha hk i)
    _ = 𝒱 (ϖ : F) := by rw [hpow, ← mul_assoc, hinv, one_mul]
    _ < 1 := hϖ.1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem inCell_of_inBK {a : ℕ} (ha : 0 < a) {x : GL (Fin (n + 2)) F}
    (hx : InBK (n + 1) a (x * tHead ϖ a)) : InCell x := by
  obtain ⟨b, k, hk, e⟩ := hx
  have hx' : x = b.val * (k * (tHead ϖ a)⁻¹) := by
    rw [← mul_assoc, ← e, mul_inv_cancel_right]
  rw [hx', inCell_mul_iff (colT_borel b)]
  exact inCell_mul_tHead_inv hϖ ha hk

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem lowerUnip_smul_mem {a : ℕ} (ha : 0 < a) {y : Fin (n + 1) → F} (hy : IsSmall y) :
    lowerUnip (((ϖ ^ (a - 1) : Fˣ) : F) • y) ∈ principalLevelSubgroup F (n + 1) a := by
  apply lowerUnip_mem_principalLevel hϖ
  intro i
  rw [Pi.smul_apply, smul_eq_mul, map_mul, Units.val_pow_eq_pow_val, map_pow]
  calc 𝒱 (ϖ : F) ^ (a - 1) * 𝒱 (y i) ≤ 𝒱 (ϖ : F) ^ (a - 1) * 𝒱 (ϖ : F) :=
        mul_le_mul' le_rfl ((val_lt_one_iff_le_uniformizer hϖ _).1 (hy i))
    _ = 𝒱 (ϖ : F) ^ a := by rw [← pow_succ, Nat.sub_add_cancel ha]

/-! ### Decomposition of the cell -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A matrix with vanishing first-column tail and identity lower-right block is
upper triangular. -/
theorem isUpperTriangular_of_colT_low {X : Matrix (Fin (n + 2)) (Fin (n + 2)) F}
    (h0 : colT X = 0) (h1 : low X = 1) : X.IsUpperTriangular := by
  intro i j hij
  cases i using Fin.cases with
  | zero => exact absurd hij (Fin.not_lt_zero _)
  | succ i =>
    cases j using Fin.cases with
    | zero => exact congrFun h0 i
    | succ j =>
      have := congrFun (congrFun h1 i) j
      rw [low_apply] at this
      rw [this, Matrix.one_apply_ne (ne_of_gt (Fin.succ_lt_succ_iff.1 hij))]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Every element of the cell is `b diag(1, D) L(y)` with `b` upper triangular and `y`
small. -/
theorem cell_decomp {x : GL (Fin (n + 2)) F} (hx : InCell x) :
    ∃ b : Borel (F := F) (n + 1), ∃ D : GL (Fin (n + 1)) F, ∃ y : Fin (n + 1) → F,
      IsSmall y ∧ x = b.val * (blockDiag 1 D * lowerUnip y) := by
  set y := cellVec x with hy
  set p := x * lowerUnip (-y) with hp
  have hpc : colT p.val = 0 := colT_mul_lowerUnip_neg_cellVec hx.1
  have hpu := (isUnit_of_colT_eq_zero hpc).1
  set D := lowGL p with hD
  set bb := p * (blockDiag 1 D)⁻¹ with hbb
  have hbc : colT bb.val = 0 := by
    rw [hbb, Units.val_mul, colT_mul_of_colT_eq_zero hpc, blockDiag_inv, colT_blockDiag,
      mulVec_zero]
  have hbl : low bb.val = 1 := by
    rw [hbb, Units.val_mul, low_mul_of_colT_eq_zero hpc, blockDiag_inv, low_blockDiag, hD,
      ← lowGL_val hpu, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨⟨bb, isUpperTriangular_of_colT_low hbc hbl⟩, D, y, hx.2, ?_⟩
  change x = bb * (blockDiag 1 D * lowerUnip y)
  rw [← mul_assoc, hbb, inv_mul_cancel_right, hp, mul_assoc, lowerUnip_add, neg_add_cancel,
    lowerUnip_zero, mul_one]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Two Borel-covariant functions that are right invariant under the small lower
unipotent matrices and agree on the matrices `diag(1, D)` agree on the cell. -/
theorem eq_of_inCell (φ₁ φ₂ : GL (Fin (n + 2)) F → ℂ) (χ : Borel (F := F) (n + 1) → ℂ)
    (h₁ : ∀ b x, φ₁ (b.val * x) = χ b * φ₁ x) (h₂ : ∀ b x, φ₂ (b.val * x) = χ b * φ₂ x)
    (hL₁ : ∀ y, IsSmall y → ∀ x, φ₁ (x * lowerUnip y) = φ₁ x)
    (hL₂ : ∀ y, IsSmall y → ∀ x, φ₂ (x * lowerUnip y) = φ₂ x)
    (hD : ∀ D, φ₁ (blockDiag 1 D) = φ₂ (blockDiag 1 D)) {x : GL (Fin (n + 2)) F}
    (hx : InCell x) : φ₁ x = φ₂ x := by
  obtain ⟨b, D, y, hy, rfl⟩ := cell_decomp hx
  rw [h₁, h₂, hL₁ y hy, hL₂ y hy, hD]

/-! ### Restriction to the block-diagonal matrices -/

section Restrict

variable {q : ℕ} (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 2) → ℂˣ)

/-- The embedding `b ↦ diag(1, b)` of the Borel subgroups. -/
def borelHead (b : Borel (F := F) n) : Borel (F := F) (n + 1) :=
  ⟨blockDiag 1 b.val, by
    change (blk ((1 : Fˣ) : F) 0 0 (b.val : Matrix (Fin (n + 1)) (Fin (n + 1)) F)).IsUpperTriangular
    intro i j hij
    cases i using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero _)
    | succ i =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        have hb : (b.val : Matrix (Fin (n + 1)) (Fin (n + 1)) F).IsUpperTriangular := b.property
        exact hb (Fin.succ_lt_succ_iff.1 hij)⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem borelHead_val (b : Borel (F := F) n) : (borelHead b).val = blockDiag 1 b.val := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem lowBorel_borelHead (b : Borel (F := F) n) : lowBorel (borelHead b) = b :=
  Subtype.ext (lowGL_blockDiag 1 b.val)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem diagonalUnit_borelHead (b : Borel (F := F) n) :
    diagonalUnit (n + 1) 0 (borelHead b) = 1 := by
  apply Units.ext
  rw [diagonalUnit_val]
  rfl

theorem normalizedCharacter_borelHead (b : Borel (F := F) n) :
    normalizedCharacter hϖ (n + 1) hq z (borelHead b) =
      sqrtResidueUnit hq ^ ordDet hϖ b.val * normalizedCharacter hϖ n hq (tailParam z) b := by
  rw [normalizedCharacter_split, diagonalUnit_borelHead, ord_one, lowBorel_borelHead]
  simp

/-- The function `D ↦ s^(-ord det D) G(diag(1, D))`. -/
def restrictFun (G : PrincipalSeries hϖ (n + 1) hq z) (D : GL (Fin (n + 1)) F) : ℂ :=
  ((sqrtResidueUnit hq ^ (-ordDet hϖ D) : ℂˣ) : ℂ) * value hϖ (n + 1) G (blockDiag 1 D)

theorem restrictFun_borel_mul (G : PrincipalSeries hϖ (n + 1) hq z) (b : Borel (F := F) n)
    (D : GL (Fin (n + 1)) F) :
    restrictFun hϖ hq z G (b.val * D) =
      (normalizedCharacter hϖ n hq (tailParam z) b : ℂ) * restrictFun hϖ hq z G D := by
  unfold restrictFun
  have e : blockDiag (1 : Fˣ) (b.val * D) = (borelHead b).val * blockDiag 1 D := by
    rw [borelHead_val, blockDiag_mul, one_mul]
  have hu : sqrtResidueUnit hq ^ (-(ordDet hϖ b.val + ordDet hϖ D)) *
      (sqrtResidueUnit hq ^ ordDet hϖ b.val * normalizedCharacter hϖ n hq (tailParam z) b) =
        normalizedCharacter hϖ n hq (tailParam z) b * sqrtResidueUnit hq ^ (-ordDet hϖ D) := by
    rw [neg_add, _root_.zpow_add, _root_.zpow_neg]
    group
    exact mul_comm _ _
  rw [e, value_borel_mul, normalizedCharacter_borelHead, ordDet_mul, ← mul_assoc,
    ← Units.val_mul, hu, Units.val_mul, mul_assoc]

theorem restrictFun_mul_level (G : PrincipalSeries hϖ (n + 1) hq z) {a : ℕ}
    (hG : ∀ h ∈ principalLevelSubgroup F n a, ∀ x,
      value hϖ (n + 1) G (x * blockDiag 1 h) = value hϖ (n + 1) G x)
    {h : GL (Fin (n + 1)) F} (hh : h ∈ principalLevelSubgroup F n a) (D : GL (Fin (n + 1)) F) :
    restrictFun hϖ hq z G (D * h) = restrictFun hϖ hq z G D := by
  unfold restrictFun
  have e : blockDiag (1 : Fˣ) (D * h) = blockDiag 1 D * blockDiag 1 h := by
    rw [blockDiag_mul, one_mul]
  rw [ordDet_mul, ordDet_eq_zero_of_integral hϖ (integral_of_mem_principalLevel hh), add_zero,
    e, hG h hh]

/-- The restriction of `G` to the matrices `diag(1, D)`, as a principal-series function of
rank `n + 1`. -/
def restrict (G : PrincipalSeries hϖ (n + 1) hq z) {a : ℕ}
    (hG : ∀ h ∈ principalLevelSubgroup F n a, ∀ x,
      value hϖ (n + 1) G (x * blockDiag 1 h) = value hϖ (n + 1) G x) :
    PrincipalSeries hϖ n hq (tailParam z) :=
  smoothFunctionOf _ _ (restrictFun hϖ hq z G) (fun b D => restrictFun_borel_mul hϖ hq z G b D)
    (principalLevelOpenSubgroup F n a)
    (fun k D => restrictFun_mul_level hϖ hq z G hG k.property D)

theorem value_restrict (G : PrincipalSeries hϖ (n + 1) hq z) {a : ℕ}
    (hG : ∀ h ∈ principalLevelSubgroup F n a, ∀ x,
      value hϖ (n + 1) G (x * blockDiag 1 h) = value hϖ (n + 1) G x)
    (D : GL (Fin (n + 1)) F) :
    value hϖ n (restrict hϖ hq z G hG) D = restrictFun hϖ hq z G D :=
  rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isSmall_add_iff {m : ℕ} {y : Fin m → F} (hy : IsSmall y) (v : Fin m → F) :
    IsSmall (v + y) ↔ IsSmall v :=
  show v + y ∈ smallSubgroup m ↔ v ∈ smallSubgroup m from
    (smallSubgroup m).add_mem_cancel_right ((mem_smallSubgroup y).2 hy)

theorem extFun_mul_lowerUnip_small (ψ : PrincipalSeries hϖ n hq (tailParam z))
    {y : Fin (n + 1) → F} (hy : IsSmall y) (x : GL (Fin (n + 2)) F) :
    extFun hϖ ψ (x * lowerUnip y) = extFun hϖ ψ x := by
  simp only [extFun]
  rw [cellFun_mul_lowerUnip]
  have h := cellFun_eq_of_iff hϖ (hq := hq) (z := z) (P := IsSmall)
    (P' := fun v => IsSmall (v + y)) (φ := value hϖ n ψ) (φ' := value hϖ n ψ) (x := x)
    (x' := x) 1 (and_congr_right fun _ => isSmall_add_iff hy (cellVec x))
    (fun _ => (one_mul _).symm)
  rwa [one_mul] at h

theorem cellScalar_blockDiag_one (D : GL (Fin (n + 1)) F) :
    cellScalar hϖ hq z (blockDiag 1 D) = sqrtResidueUnit hq ^ ordDet hϖ D := by
  unfold cellScalar headOrd
  rw [lowGL_blockDiag, ordDet_blockDiag, ord_one]
  simp

theorem extFun_blockDiag_one (ψ : PrincipalSeries hϖ n hq (tailParam z))
    (D : GL (Fin (n + 1)) F) :
    extFun hϖ ψ (blockDiag 1 D) =
      ((sqrtResidueUnit hq ^ ordDet hϖ D : ℂˣ) : ℂ) * value hϖ n ψ D := by
  have hu : IsUnit (low (blockDiag (1 : Fˣ) D).val).det := by
    rw [low_blockDiag]
    exact (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit
  have hc : InCell (blockDiag (1 : Fˣ) D) := by
    refine ⟨hu, fun i => ?_⟩
    rw [cellVec, colT_blockDiag, mulVec_zero, Pi.zero_apply, map_zero]
    exact zero_lt_one
  rw [extFun_apply, if_pos hc, lowGL_blockDiag, cellScalar_blockDiag_one]

/-- A function in the principal series of rank `n + 2` that vanishes off the cell and is
right invariant under the small lower unipotent matrices is the extension of its
restriction. -/
theorem extend_restrict (G : PrincipalSeries hϖ (n + 1) hq z) {a : ℕ}
    (hG : ∀ h ∈ principalLevelSubgroup F n a, ∀ x,
      value hϖ (n + 1) G (x * blockDiag 1 h) = value hϖ (n + 1) G x)
    (hG0 : ∀ x, ¬InCell x → value hϖ (n + 1) G x = 0)
    (hGL : ∀ y, IsSmall y → ∀ x, value hϖ (n + 1) G (x * lowerUnip y) = value hϖ (n + 1) G x) :
    extend hϖ hq z (restrict hϖ hq z G hG) = G := by
  apply ext_value hϖ
  intro x
  rw [extend_value]
  by_cases hx : InCell x
  · refine eq_of_inCell (extFun hϖ (restrict hϖ hq z G hG)) (value hϖ (n + 1) G)
      (fun b => (normalizedCharacter hϖ (n + 1) hq z b : ℂ))
      (fun b x => extFun_covariance hϖ _ b x) (fun b x => value_borel_mul hϖ G b x)
      (fun y hy x => extFun_mul_lowerUnip_small hϖ hq z _ hy x) hGL (fun D => ?_) hx
    rw [extFun_blockDiag_one, value_restrict, restrictFun, ← mul_assoc, ← Units.val_mul,
      ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_mul]
  · rw [extFun_apply, if_neg hx, hG0 x hx]

end Restrict

/-! ### Functions supported on `B K_a` -/

section Support

variable {q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (n + 2) → ℂˣ}

/-- A function fixed by `K_a` and supported on `B K_a` lies in every subrepresentation
containing all extensions by zero. -/
theorem mem_of_support_inBK (S : Subrepresentation (principalSeries hϖ (n + 1) hq z))
    (hS : ∀ ψ, extend hϖ hq z ψ ∈ S) {a : ℕ} (ha : 0 < a)
    (g : PrincipalSeries hϖ (n + 1) hq z)
    (hg : ∀ k ∈ principalLevelSubgroup F (n + 1) a, ∀ x,
      value hϖ (n + 1) g (x * k) = value hϖ (n + 1) g x)
    (hsupp : ∀ x, ¬InBK (n + 1) a x → value hϖ (n + 1) g x = 0) : g ∈ S := by
  set t : GL (Fin (n + 2)) F := tHead ϖ a with ht
  set G := principalSeries hϖ (n + 1) hq z t g with hGdef
  have hG4 : ∀ h ∈ principalLevelSubgroup F n a, ∀ x,
      value hϖ (n + 1) G (x * blockDiag 1 h) = value hϖ (n + 1) G x := by
    intro h hh x
    rw [hGdef, rightTranslation, rightTranslation, mul_assoc, ht, tHead,
      blockDiag_one_mul_comm, ← mul_assoc, hg _ (blockDiag_one_mem_principalLevel hϖ hh)]
  have hG0 : ∀ x, ¬InCell x → value hϖ (n + 1) G x = 0 := by
    intro x hx
    rw [hGdef, rightTranslation]
    exact hsupp _ (fun h => hx (inCell_of_inBK hϖ ha h))
  have hGL : ∀ y, IsSmall y → ∀ x,
      value hϖ (n + 1) G (x * lowerUnip y) = value hϖ (n + 1) G x := by
    intro y hy x
    rw [hGdef, rightTranslation, rightTranslation, mul_assoc, ht, tHead,
      lowerUnip_mul_blockDiag_one, ← mul_assoc, hg _ (lowerUnip_smul_mem hϖ ha hy)]
  have hE := extend_restrict hϖ hq z G hG4 hG0 hGL
  have hg' : g = principalSeries hϖ (n + 1) hq z t⁻¹ G := by
    apply ext_value hϖ
    intro x
    rw [hGdef, rightTranslation, rightTranslation, inv_mul_cancel_right]
  rw [hg', ← hE]
  exact S.apply_mem_toSubmodule _ (hS _)

/-- The piece of `g` supported on `B K_a κ`. -/
theorem cut_translate_mem (S : Subrepresentation (principalSeries hϖ (n + 1) hq z))
    (hS : ∀ ψ, extend hϖ hq z ψ ∈ S) {a : ℕ} (ha : 0 < a)
    {κ : GL (Fin (n + 2)) F} (hκ : κ ∈ integralSubgroup 𝒪 (n + 1))
    (g : PrincipalSeries hϖ (n + 1) hq z)
    (hg : ∀ k ∈ principalLevelSubgroup F (n + 1) a, ∀ x,
      value hϖ (n + 1) g (x * k) = value hϖ (n + 1) g x) :
    cut hϖ (fun x => InBK (n + 1) a (x * κ⁻¹))
      (fun b x => by rw [mul_assoc]; exact inBK_borel_mul_iff b _)
      (fun k hk x => inBK_translate_iff hκ hk x) g hg ∈ S := by
  have hg1 := translate_right_inv hϖ hκ g hg
  set c := cut hϖ (InBK (n + 1) a) (fun b x => inBK_borel_mul_iff b x)
    (fun k hk x => inBK_mul_iff hk x) (principalSeries hϖ (n + 1) hq z κ g) hg1 with hc
  have hcS : c ∈ S := by
    refine mem_of_support_inBK hϖ S hS ha c (cut_mul hϖ _ _ _ _ hg1) (fun x hx => ?_)
    rw [hc, value_cut, if_neg hx]
  have e : cut hϖ (fun x => InBK (n + 1) a (x * κ⁻¹))
      (fun b x => by rw [mul_assoc]; exact inBK_borel_mul_iff b _)
      (fun k hk x => inBK_translate_iff hκ hk x) g hg =
        principalSeries hϖ (n + 1) hq z κ⁻¹ c := by
    apply ext_value hϖ
    intro x
    rw [rightTranslation, hc, value_cut, value_cut, rightTranslation, inv_mul_cancel_right]
  rw [e]
  exact S.apply_mem_toSubmodule _ hcS

/-- **Step C.** A subrepresentation of the principal series of rank `n + 2` containing
every extension by zero is everything. -/
theorem eq_top_of_extend_mem (S : Subrepresentation (principalSeries hϖ (n + 1) hq z))
    (hS : ∀ ψ, extend hϖ hq z ψ ∈ S) : S = ⊤ := by
  have hall : ∀ f : PrincipalSeries hϖ (n + 1) hq z, f ∈ S := by
    intro f
    have ha : 0 < level hϖ f := level_pos hϖ f
    have hf := level_spec hϖ f
    obtain ⟨T, hT⟩ := exists_cover (F := F) (n + 1) (level hϖ f)
    have key : ∀ T' : Finset (integralSubgroup 𝒪 (n + 1)),
        ∀ g : PrincipalSeries hϖ (n + 1) hq z,
        (∀ k ∈ principalLevelSubgroup F (n + 1) (level hϖ f), ∀ x,
          value hϖ (n + 1) g (x * k) = value hϖ (n + 1) g x) →
        (∀ x, (∀ κ ∈ T', ¬InBK (n + 1) (level hϖ f) (x * (κ : GL (Fin (n + 2)) F)⁻¹)) →
          value hϖ (n + 1) g x = 0) → g ∈ S := by
      intro T'
      classical
      induction T' using Finset.induction_on with
      | empty =>
        intro g _ hg0
        have : g = 0 := ext_value hϖ (fun x => by
          rw [value_zero]
          exact hg0 x (fun κ hκ => absurd hκ (Finset.notMem_empty κ)))
        rw [this]
        exact S.toSubmodule.zero_mem
      | insert κ T' hκT ih =>
        intro g hg hg0
        have hcut := cut_translate_mem hϖ S hS ha κ.property g hg
        set c := cut hϖ (fun x => InBK (n + 1) (level hϖ f) (x * (κ : GL (Fin (n + 2)) F)⁻¹))
          (fun b x => by rw [mul_assoc]; exact inBK_borel_mul_iff b _)
          (fun k hk x => inBK_translate_iff κ.property hk x) g hg with hc
        have hrest : g - c ∈ S := by
          refine ih (g - c) (fun k hk x => ?_) (fun x hx => ?_)
          · rw [value_sub, value_sub, hg k hk x, cut_mul hϖ _ _ _ _ hg k hk x]
          · rw [value_sub, hc, value_cut]
            by_cases h : InBK (n + 1) (level hϖ f) (x * (κ : GL (Fin (n + 2)) F)⁻¹)
            · rw [if_pos h, sub_self]
            · rw [if_neg h, sub_zero]
              refine hg0 x (fun κ' hκ' => ?_)
              rcases Finset.mem_insert.1 hκ' with rfl | hκ'
              · exact h
              · exact hx κ' hκ'
        have := S.toSubmodule.add_mem hcut hrest
        rwa [add_sub_cancel] at this
    refine key T f hf (fun x hx => absurd ?_ (fun h => h))
    exfalso
    obtain ⟨b, k, rfl⟩ := exists_borel_integral (n + 1) x
    obtain ⟨κ, hκ, hk⟩ := hT k.val k.property
    exact hx κ hκ ⟨b, k.val * (κ : GL (Fin (n + 2)) F)⁻¹, hk, by rw [mul_assoc]⟩
  apply Subrepresentation.ext
  exact Submodule.eq_top_iff'.2 hall

end Support

end Langlands.Conductor.SphericalCyclicity
