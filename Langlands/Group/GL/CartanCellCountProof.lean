import Langlands.Group.GL.CartanCellCountStatement
import Langlands.Group.GL.CartanQuotientLawsProof
import Langlands.HarmonicAnalysis.Conductor
import Langlands.LocalField.Normalization.Proof
import Mathlib.GroupTheory.Index

/-!
# Counting left cosets in an antidominant Cartan double coset

Conjugation by `a(lam)⁻¹` maps the entrywise congruence subgroup
`levelSubgroup lam` into `K`, so a left translate `k a(lam) K` with `k ∈ K`
depends only on the coset of `k` modulo that subgroup. Its index in `K` is
bounded through a chain of fundamental-coweight steps; each step is the kernel
of an additive reduction map to residue-field matrices.
-/

noncomputable section

open scoped WithZero

namespace Langlands.GeneralLinear.CartanQuotient

universe uF

namespace CellCount

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ### Valuation levels -/

/-- `x` lies in `ϖ ^ e O`, measured by the discrete valuation. -/
def Level (e : ℤ) (x : F.Carrier) : Prop :=
  T.discreteValuation x ≤ WithZero.exp (-e)

variable {T}

theorem level_zero (e : ℤ) : Level T e 0 := by
  simp [Level]

theorem Level.add {e : ℤ} {x y : F.Carrier} (hx : Level T e x) (hy : Level T e y) :
    Level T e (x + y) :=
  (T.discreteValuation.map_add x y).trans (max_le hx hy)

theorem Level.neg {e : ℤ} {x : F.Carrier} (hx : Level T e x) : Level T e (-x) := by
  rwa [Level, Valuation.map_neg]

theorem Level.sub {e : ℤ} {x y : F.Carrier} (hx : Level T e x) (hy : Level T e y) :
    Level T e (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem Level.mul {e f : ℤ} {x y : F.Carrier} (hx : Level T e x) (hy : Level T f y) :
    Level T (e + f) (x * y) := by
  rw [Level, map_mul, neg_add, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem Level.mono {e f : ℤ} {x : F.Carrier} (h : f ≤ e) (hx : Level T e x) : Level T f x :=
  hx.trans (WithZero.exp_le_exp.mpr (neg_le_neg h))

theorem Level.sum {ι : Type*} {s : Finset ι} {e : ℤ} {f : ι → F.Carrier}
    (h : ∀ i ∈ s, Level T e (f i)) : Level T e (∑ i ∈ s, f i) :=
  T.discreteValuation.map_sum_le h

theorem Level.le_one {e : ℤ} {x : F.Carrier} (he : 0 ≤ e) (hx : Level T e x) :
    T.discreteValuation x ≤ 1 :=
  hx.trans (WithZero.exp_le_one_iff.mpr (neg_nonpos.mpr he))

theorem level_zero_iff {x : F.Carrier} : Level T 0 x ↔ T.discreteValuation x ≤ 1 := by
  simp [Level]

/-- Multiplying by `ϖ ^ (-k)` lowers the level by `k`. -/
theorem level_uniformizer_mul_iff (e k : ℤ) (x : F.Carrier) :
    Level T e (((LocalFactor.PadicAbelian.uniformizerUnit T ^ (-k) : F.Carrierˣ) :
      F.Carrier) * x) ↔ Level T (e + k) x := by
  simp only [Level, map_mul, LocalFactor.PadicAbelian.uniformizerUnit_zpow_value, neg_neg]
  constructor
  · intro h
    have h' := mul_le_mul' (le_refl (WithZero.exp (-k))) h
    rwa [← mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, one_mul,
      ← WithZero.exp_add, ← neg_add, add_comm k e] at h'
  · intro h
    have h' := mul_le_mul' (le_refl (WithZero.exp k)) h
    rwa [← WithZero.exp_add, show k + -(e + k) = -e by ring] at h'

/-! ### Residues of integral elements -/

variable (T) in
/-- The residue class of an integral element, and zero off the integers. -/
def res (x : F.Carrier) : T.ResidueField := by
  classical
  exact if h : x ∈ T.Integers then T.residue ⟨x, h⟩ else 0

theorem mem_integers_of_le_one {x : F.Carrier} (hx : T.discreteValuation x ≤ 1) :
    x ∈ T.Integers :=
  (T.mem_integers_iff_discreteValuation_le_one x).mpr hx

theorem res_of_mem {x : F.Carrier} (h : x ∈ T.Integers) : res T x = T.residue ⟨x, h⟩ := by
  classical
  simp only [res, dite_eq_left h]

theorem res_add {x y : F.Carrier} (hx : T.discreteValuation x ≤ 1)
    (hy : T.discreteValuation y ≤ 1) : res T (x + y) = res T x + res T y := by
  have hxy : T.discreteValuation (x + y) ≤ 1 :=
    (T.discreteValuation.map_add x y).trans (max_le hx hy)
  rw [res_of_mem (mem_integers_of_le_one hxy), res_of_mem (mem_integers_of_le_one hx),
    res_of_mem (mem_integers_of_le_one hy), ← map_add]
  rfl

theorem res_eq_zero_iff {x : F.Carrier} (hx : T.discreteValuation x ≤ 1) :
    res T x = 0 ↔ Level T 1 x := by
  rw [res_of_mem (mem_integers_of_le_one hx), IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  have key : ∀ y : ℤᵐ⁰, y < 1 ↔ y ≤ WithZero.exp (-1) := by
    intro y
    simpa [← WithZero.exp_add] using
      (WithZero.lt_mul_exp_iff_le (x := y) (y := WithZero.exp (-1)) WithZero.exp_ne_zero)
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  change ValuativeRel.valuation F.Carrier x < 1 ↔
    e (ValuativeRel.valuation F.Carrier x) ≤ WithZero.exp (-1)
  rw [← key, ← map_one e, e.strictMono.lt_iff_lt]

theorem res_zero : res T (0 : F.Carrier) = 0 :=
  (res_eq_zero_iff (by simp)).mpr (level_zero 1)

/-- Equal residues of integral elements give a difference of level one. -/
theorem level_sub_of_res_eq {x y : F.Carrier} (hx : T.discreteValuation x ≤ 1)
    (hy : T.discreteValuation y ≤ 1) (h : res T x = res T y) : Level T 1 (y - x) := by
  have hyx : T.discreteValuation (y - x) ≤ 1 :=
    (T.discreteValuation.map_sub y x).trans (max_le hy hx)
  have h' : res T y = res T (y - x) + res T x := by
    rw [← res_add hyx hx, sub_add_cancel]
  rw [h, right_eq_add] at h'
  exact (res_eq_zero_iff hyx).mp h'

/-! ### Integral matrices -/

theorem mem_maximalCompact_iff {n : ℕ} (g : GeneralLinear n F.Carrier) :
    g ∈ maximalCompact T n ↔
      (∀ i j, T.discreteValuation (g i j) ≤ 1) ∧
        (∀ i j, T.discreteValuation ((g⁻¹ : GeneralLinear n F.Carrier) i j) ≤ 1) := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => (h i j).property, fun i j => ?_⟩
    rw [← map_inv]
    exact (h⁻¹ i j).property
  · rintro ⟨hg, hi⟩
    let O := T.discreteValuation.integer
    let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g i j, hg i j⟩
    let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨g⁻¹ i j, hi i j⟩
    have hab : A * B = 1 := by
      apply Matrix.ext
      intro i j
      apply Subtype.val_injective
      change ((A * B).map O.subtype) i j = ((1 : Matrix _ _ O).map O.subtype) i j
      rw [Matrix.map_mul, Matrix.map_one O.subtype (map_zero O.subtype) (map_one O.subtype)]
      change ((g * g⁻¹ : GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier) i j = _
      rw [mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
    have hba : B * A = 1 := by
      apply Matrix.ext
      intro i j
      apply Subtype.val_injective
      change ((B * A).map O.subtype) i j = ((1 : Matrix _ _ O).map O.subtype) i j
      rw [Matrix.map_mul, Matrix.map_one O.subtype (map_zero O.subtype) (map_one O.subtype)]
      change ((g⁻¹ * g : GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier) i j = _
      rw [inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
    exact ⟨⟨A, B, hab, hba⟩, Matrix.GeneralLinearGroup.ext (fun _ _ => rfl)⟩

/-! ### Entrywise congruence levels -/

/-- The level `1 + max 0 (μ i - μ j)` imposed on the entry `(i, j)`. -/
def lev {n : ℕ} (μ : Fin n → ℤ) (i j : Fin n) : ℤ :=
  1 + max 0 (μ i - μ j)

theorem one_le_lev {n : ℕ} (μ : Fin n → ℤ) (i j : Fin n) : 1 ≤ lev μ i j := by
  unfold lev
  have := le_max_left (0 : ℤ) (μ i - μ j)
  omega

theorem lev_add_one_le {n : ℕ} (μ : Fin n → ℤ) (i k j : Fin n) :
    lev μ i j + 1 ≤ lev μ i k + lev μ k j := by
  unfold lev
  have h1 := le_max_left (0 : ℤ) (μ i - μ k)
  have h2 := le_max_right (0 : ℤ) (μ i - μ k)
  have h3 := le_max_left (0 : ℤ) (μ k - μ j)
  have h4 := le_max_right (0 : ℤ) (μ k - μ j)
  have : max (0 : ℤ) (μ i - μ j) ≤ max 0 (μ i - μ k) + max 0 (μ k - μ j) :=
    max_le (by omega) (by omega)
  omega

variable (T) in
/-- Entrywise congruence of `A - 1` at the levels of `μ`. -/
def Congr {n : ℕ} (μ : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) F.Carrier) : Prop :=
  ∀ i j, Level T (lev μ i j) ((A - 1) i j)

theorem congr_one {n : ℕ} (μ : Fin n → ℤ) : Congr T μ 1 := fun i j => by
  rw [sub_self]
  exact level_zero _

theorem mul_sub_one {n : ℕ} (A B : Matrix (Fin n) (Fin n) F.Carrier) :
    A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by
  simp only [sub_mul, mul_sub, mul_one, one_mul]
  abel

theorem cross_level {n : ℕ} {μ : Fin n → ℤ} {A B : Matrix (Fin n) (Fin n) F.Carrier}
    (hA : Congr T μ A) (hB : Congr T μ B) (i j : Fin n) :
    Level T (lev μ i j + 1) (((A - 1) * (B - 1)) i j) := by
  rw [Matrix.mul_apply]
  exact Level.sum fun k _ => ((hA i k).mul (hB k j)).mono (lev_add_one_le μ i k j)

theorem Congr.mul {n : ℕ} {μ : Fin n → ℤ} {A B : Matrix (Fin n) (Fin n) F.Carrier}
    (hA : Congr T μ A) (hB : Congr T μ B) : Congr T μ (A * B) := by
  intro i j
  rw [mul_sub_one, Matrix.add_apply, Matrix.add_apply]
  exact (((cross_level hA hB i j).mono (by omega)).add (hA i j)).add (hB i j)

theorem Congr.mono {n : ℕ} {μ ν : Fin n → ℤ} {A : Matrix (Fin n) (Fin n) F.Carrier}
    (hA : Congr T μ A) (h : ∀ i j, lev ν i j ≤ lev μ i j) : Congr T ν A :=
  fun i j => (hA i j).mono (h i j)

theorem Congr.entry_le_one {n : ℕ} {μ : Fin n → ℤ} {A : Matrix (Fin n) (Fin n) F.Carrier}
    (hA : Congr T μ A) (i j : Fin n) : T.discreteValuation (A i j) ≤ 1 := by
  have h : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) F.Carrier) i j := by simp
  rw [h]
  refine (T.discreteValuation.map_add _ _).trans
    (max_le ((hA i j).le_one (by linarith [one_le_lev μ i j])) ?_)
  rw [Matrix.one_apply]
  split_ifs <;> simp

variable (T) in
/-- The subgroup of `g` with `g - 1` and `g⁻¹ - 1` congruent at the levels of `μ`.
For `μ = 0` it is the principal congruence subgroup of level one. -/
def levelSubgroup {n : ℕ} (μ : Fin n → ℤ) : Subgroup (GeneralLinear n F.Carrier) where
  carrier := {g | Congr T μ (g : Matrix (Fin n) (Fin n) F.Carrier) ∧
    Congr T μ ((g⁻¹ : GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier)}
  mul_mem' {g h} hg hh := by
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨hh1, hh2⟩ := hh
    refine ⟨?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.coe_mul]
      exact hg1.mul hh1
    · rw [mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul]
      exact hh2.mul hg2
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.coe_one]
      exact congr_one μ
    · rw [inv_one, Matrix.GeneralLinearGroup.coe_one]
      exact congr_one μ
  inv_mem' {g} hg := by
    obtain ⟨hg1, hg2⟩ := hg
    refine ⟨hg2, ?_⟩
    rw [inv_inv]
    exact hg1

theorem mem_levelSubgroup {n : ℕ} {μ : Fin n → ℤ} {g : GeneralLinear n F.Carrier} :
    g ∈ levelSubgroup T μ ↔ Congr T μ (g : Matrix (Fin n) (Fin n) F.Carrier) ∧
      Congr T μ ((g⁻¹ : GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier) :=
  Iff.rfl

theorem levelSubgroup_le_maximalCompact {n : ℕ} (μ : Fin n → ℤ) :
    levelSubgroup T μ ≤ maximalCompact T n := fun _ hg =>
  (mem_maximalCompact_iff _).mpr ⟨hg.1.entry_le_one, hg.2.entry_le_one⟩

theorem levelSubgroup_le_zero {n : ℕ} (μ : Fin n → ℤ) :
    levelSubgroup T μ ≤ levelSubgroup T (0 : Fin n → ℤ) := by
  have h : ∀ i j, lev (0 : Fin n → ℤ) i j ≤ lev μ i j := fun i j => by
    simp [lev]
  exact fun _ hg => ⟨hg.1.mono h, hg.2.mono h⟩

/-! ### Conjugation by the diagonal representative -/

theorem representative_conj_apply {n : ℕ} (μ : Fin n → ℤ) (g : GeneralLinear n F.Carrier)
    (i j : Fin n) :
    ((representative T μ)⁻¹ * g * representative T μ) i j =
      (((LocalFactor.PadicAbelian.uniformizerUnit T ^ μ i)⁻¹ : F.Carrierˣ) : F.Carrier) *
        g i j * ((LocalFactor.PadicAbelian.uniformizerUnit T ^ μ j : F.Carrierˣ) : F.Carrier) := by
  rw [representative, Iwasawa.torus_inv, Iwasawa.torus, Iwasawa.diagonalUnits_mul_mul_apply]

theorem valuation_representative_conj_apply {n : ℕ} (μ : Fin n → ℤ)
    (g : GeneralLinear n F.Carrier) (i j : Fin n) :
    T.discreteValuation (((representative T μ)⁻¹ * g * representative T μ) i j) =
      WithZero.exp (μ i - μ j) * T.discreteValuation (g i j) := by
  rw [representative_conj_apply, map_mul, map_mul, ← zpow_neg,
    LocalFactor.PadicAbelian.uniformizerUnit_zpow_value,
    LocalFactor.PadicAbelian.uniformizerUnit_zpow_value, neg_neg, mul_right_comm,
    ← WithZero.exp_add, ← sub_eq_add_neg]

theorem Congr.conj_entry_le_one {n : ℕ} {μ : Fin n → ℤ} {g : GeneralLinear n F.Carrier}
    (hg : Congr T μ (g : Matrix (Fin n) (Fin n) F.Carrier)) (i j : Fin n) :
    T.discreteValuation (((representative T μ)⁻¹ * g * representative T μ) i j) ≤ 1 := by
  rw [valuation_representative_conj_apply]
  by_cases hij : i = j
  · subst hij
    simpa using hg.entry_le_one i i
  · have h := hg i j
    rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at h
    calc WithZero.exp (μ i - μ j) * T.discreteValuation (g i j)
        ≤ WithZero.exp (μ i - μ j) * WithZero.exp (-lev μ i j) := mul_le_mul' le_rfl h
      _ = WithZero.exp (μ i - μ j - lev μ i j) := by
        rw [← WithZero.exp_add]
        congr 1
      _ ≤ 1 := WithZero.exp_le_one_iff.mpr (by
        unfold lev
        have := le_max_right (0 : ℤ) (μ i - μ j)
        omega)

theorem conj_mem_maximalCompact {n : ℕ} {μ : Fin n → ℤ} {g : GeneralLinear n F.Carrier}
    (hg : g ∈ levelSubgroup T μ) :
    (representative T μ)⁻¹ * g * representative T μ ∈ maximalCompact T n := by
  rw [mem_maximalCompact_iff]
  refine ⟨hg.1.conj_entry_le_one, ?_⟩
  have h : ((representative T μ)⁻¹ * g * representative T μ)⁻¹ =
      (representative T μ)⁻¹ * g⁻¹ * representative T μ := by
    group
  rw [h]
  exact hg.2.conj_entry_le_one

/-! ### The index of the level-one subgroup in `K` -/

/-- A map whose fibres lie in single left cosets bounds the number of cosets. -/
theorem finite_quotient_of_fibres {G X : Type*} [Group G] [Finite X] (H : Subgroup G)
    (f : G → X) (hf : ∀ x y, f x = f y → x⁻¹ * y ∈ H) :
    Finite (G ⧸ H) ∧ Nat.card (G ⧸ H) ≤ Nat.card X := by
  classical
  let s : Set.range f → G ⧸ H := fun y => QuotientGroup.mk y.2.choose
  have hs : Function.Surjective s := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      refine ⟨⟨f x, x, rfl⟩, ?_⟩
      have hx : f (show ∃ y, f y = f x from ⟨x, rfl⟩).choose = f x :=
        (show ∃ y, f y = f x from ⟨x, rfl⟩).choose_spec
      exact QuotientGroup.eq.mpr (hf _ _ hx)
  have : Finite (Set.range f) := Subtype.finite
  exact ⟨Finite.of_surjective s hs,
    (Nat.card_le_card_of_surjective s hs).trans (Finite.card_subtype_le _)⟩

theorem congr_zero_inv_mul {n : ℕ} {x y : GeneralLinear n F.Carrier}
    (hx : x ∈ maximalCompact T n) (hy : y ∈ maximalCompact T n)
    (h : ∀ i j, res T (x i j) = res T (y i j)) :
    Congr T (0 : Fin n → ℤ) ((x⁻¹ * y : GeneralLinear n F.Carrier) :
      Matrix (Fin n) (Fin n) F.Carrier) := by
  obtain ⟨hx1, hx2⟩ := (mem_maximalCompact_iff x).mp hx
  obtain ⟨hy1, -⟩ := (mem_maximalCompact_iff y).mp hy
  have hm : ((x⁻¹ * y : GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier) - 1 =
      ((x⁻¹ : GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier) *
        ((y : Matrix (Fin n) (Fin n) F.Carrier) - (x : Matrix (Fin n) (Fin n) F.Carrier)) := by
    rw [mul_sub, ← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  intro i j
  rw [hm, Matrix.mul_apply]
  have hl : lev (0 : Fin n → ℤ) i j = 0 + 1 := by simp [lev]
  rw [hl]
  refine Level.sum fun k _ => ?_
  refine (level_zero_iff.mpr (hx2 i k)).mul ?_
  rw [Matrix.sub_apply]
  exact level_sub_of_res_eq (hx1 k j) (hy1 k j) (h k j)

theorem relIndex_levelSubgroup_zero (n : ℕ) :
    (levelSubgroup T (0 : Fin n → ℤ)).relIndex (maximalCompact T n) ≠ 0 ∧
      (levelSubgroup T (0 : Fin n → ℤ)).relIndex (maximalCompact T n) ≤
        T.residueCardinality ^ (n * n) := by
  have := T.finite_residueField
  let K := maximalCompact T n
  let f : K → (Fin n → Fin n → T.ResidueField) := fun g i j => res T ((g : GeneralLinear n F.Carrier) i j)
  have hf : ∀ x y, f x = f y → x⁻¹ * y ∈ (levelSubgroup T (0 : Fin n → ℤ)).subgroupOf K := by
    intro x y hxy
    have h : ∀ i j, res T ((x : GeneralLinear n F.Carrier) i j) =
        res T ((y : GeneralLinear n F.Carrier) i j) := fun i j => congrFun (congrFun hxy i) j
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨congr_zero_inv_mul x.2 y.2 h, ?_⟩
    rw [mul_inv_rev, inv_inv]
    exact congr_zero_inv_mul y.2 x.2 fun i j => (h i j).symm
  obtain ⟨hfin, hcard⟩ := finite_quotient_of_fibres _ f hf
  have hidx : (levelSubgroup T (0 : Fin n → ℤ)).relIndex (maximalCompact T n) =
      Nat.card (K ⧸ (levelSubgroup T (0 : Fin n → ℤ)).subgroupOf K) := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
  rw [hidx]
  refine ⟨Nat.card_pos.ne', hcard.trans ?_⟩
  simp only [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  rw [← pow_mul]
  rfl

/-! ### Fundamental-coweight steps -/

/-- The fundamental coweight `ω_m`: one on the coordinates below `m`, zero elsewhere. -/
def coweight (n m : ℕ) : Fin n → ℤ := fun i => if (i : ℕ) < m then 1 else 0

/-- The entry positions `(i, j)` with `i < m ≤ j`. -/
abbrev Block (n m : ℕ) := {x : Fin n × Fin n // (x.1 : ℕ) < m ∧ m ≤ (x.2 : ℕ)}

theorem lev_add_coweight {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) (m : ℕ) (i j : Fin n) :
    lev (μ + coweight n m) i j =
      lev μ i j + if (i : ℕ) < m ∧ m ≤ (j : ℕ) then 1 else 0 := by
  unfold lev coweight
  simp only [Pi.add_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · have := hμ h.le
    have hij : (i : ℕ) < j := h
    split_ifs <;> omega
  · simp
  · have := hμ h.le
    have hij : (j : ℕ) < i := h
    split_ifs <;> omega

variable (T) in
/-- The scaled entry `ϖ ^ (-lev μ i j) (A - 1)_{ij}`. -/
def scaledEntry {n : ℕ} (μ : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) F.Carrier) (i j : Fin n) :
    F.Carrier :=
  ((LocalFactor.PadicAbelian.uniformizerUnit T ^ (-lev μ i j) : F.Carrierˣ) : F.Carrier) *
    (A - 1) i j

theorem Congr.scaledEntry_le_one {n : ℕ} {μ : Fin n → ℤ} {A : Matrix (Fin n) (Fin n) F.Carrier}
    (hA : Congr T μ A) (i j : Fin n) : T.discreteValuation (scaledEntry T μ A i j) ≤ 1 := by
  rw [← level_zero_iff, scaledEntry, level_uniformizer_mul_iff, zero_add]
  exact hA i j

theorem res_scaledEntry_eq_zero_iff {n : ℕ} {μ : Fin n → ℤ}
    {A : Matrix (Fin n) (Fin n) F.Carrier} (hA : Congr T μ A) (i j : Fin n) :
    res T (scaledEntry T μ A i j) = 0 ↔ Level T (lev μ i j + 1) ((A - 1) i j) := by
  rw [res_eq_zero_iff (hA.scaledEntry_le_one i j), scaledEntry, level_uniformizer_mul_iff,
    add_comm]

theorem res_scaledEntry_mul {n : ℕ} {μ : Fin n → ℤ} {A B : Matrix (Fin n) (Fin n) F.Carrier}
    (hA : Congr T μ A) (hB : Congr T μ B) (i j : Fin n) :
    res T (scaledEntry T μ (A * B) i j) =
      res T (scaledEntry T μ A i j) + res T (scaledEntry T μ B i j) := by
  set u := ((LocalFactor.PadicAbelian.uniformizerUnit T ^ (-lev μ i j) : F.Carrierˣ) :
    F.Carrier)
  have hc : T.discreteValuation (u * ((A - 1) * (B - 1)) i j) ≤ 1 := by
    rw [← level_zero_iff, level_uniformizer_mul_iff, zero_add]
    exact (cross_level hA hB i j).mono (by omega)
  have hc0 : res T (u * ((A - 1) * (B - 1)) i j) = 0 := by
    rw [res_eq_zero_iff hc, level_uniformizer_mul_iff, add_comm]
    exact cross_level hA hB i j
  have hsplit : scaledEntry T μ (A * B) i j =
      u * ((A - 1) * (B - 1)) i j + scaledEntry T μ A i j + scaledEntry T μ B i j := by
    simp only [scaledEntry, u, mul_sub_one A B, Matrix.add_apply, mul_add]
  rw [hsplit, res_add ((T.discreteValuation.map_add _ _).trans
      (max_le hc (hA.scaledEntry_le_one i j))) (hB.scaledEntry_le_one i j),
    res_add hc (hA.scaledEntry_le_one i j), hc0, zero_add]

variable (T) in
/-- The additive reduction of the `(i, j)` entries with `i < m ≤ j` at the levels of `μ`. -/
def blockMap {n : ℕ} (μ : Fin n → ℤ) (m : ℕ) :
    levelSubgroup T μ →* Multiplicative (Block n m → T.ResidueField) where
  toFun g := Multiplicative.ofAdd fun x =>
    res T (scaledEntry T μ ((g : GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier)
      x.1.1 x.1.2)
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    funext x
    simp only [OneMemClass.coe_one, Matrix.GeneralLinearGroup.coe_one, scaledEntry, sub_self,
      Matrix.zero_apply, mul_zero, res_zero, Pi.zero_apply]
  map_mul' g h := by
    rw [← ofAdd_add]
    congr 1
    funext x
    simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Pi.add_apply]
    exact res_scaledEntry_mul g.2.1 h.2.1 x.1.1 x.1.2

theorem blockMap_eq_one_iff {n : ℕ} {μ : Fin n → ℤ} {m : ℕ} (g : levelSubgroup T μ) :
    blockMap T μ m g = 1 ↔ ∀ x : Block n m,
      Level T (lev μ x.1.1 x.1.2 + 1)
        ((((g : GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier) - 1) x.1.1 x.1.2) := by
  change Multiplicative.ofAdd _ = 1 ↔ _
  rw [ofAdd_eq_one, funext_iff]
  exact forall_congr' fun x => res_scaledEntry_eq_zero_iff g.2.1 x.1.1 x.1.2

theorem congr_add_coweight {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) {m : ℕ}
    {A : Matrix (Fin n) (Fin n) F.Carrier} (hA : Congr T μ A)
    (hB : ∀ x : Block n m, Level T (lev μ x.1.1 x.1.2 + 1) ((A - 1) x.1.1 x.1.2)) :
    Congr T (μ + coweight n m) A := by
  intro i j
  rw [lev_add_coweight hμ]
  split_ifs with h
  · exact hB ⟨(i, j), h⟩
  · simpa using hA i j

theorem Congr.of_add_coweight {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) {m : ℕ}
    {A : Matrix (Fin n) (Fin n) F.Carrier} (hA : Congr T (μ + coweight n m) A) :
    Congr T μ A ∧
      ∀ x : Block n m, Level T (lev μ x.1.1 x.1.2 + 1) ((A - 1) x.1.1 x.1.2) := by
  refine ⟨fun i j => (hA i j).mono ?_, fun x => ?_⟩
  · rw [lev_add_coweight hμ]
    split_ifs <;> omega
  · have h := hA x.1.1 x.1.2
    rwa [lev_add_coweight hμ, ite_eq_left x.2] at h

theorem levelSubgroup_add_coweight_le {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) (m : ℕ) :
    levelSubgroup T (μ + coweight n m) ≤ levelSubgroup T μ := fun _ hg =>
  ⟨(hg.1.of_add_coweight hμ).1, (hg.2.of_add_coweight hμ).1⟩

theorem blockMap_ker {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) (m : ℕ) :
    (blockMap T μ m).ker = (levelSubgroup T (μ + coweight n m)).subgroupOf (levelSubgroup T μ) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_levelSubgroup]
  constructor
  · intro hg
    have hinv : blockMap T μ m g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
    rw [blockMap_eq_one_iff] at hg hinv
    exact ⟨congr_add_coweight hμ g.2.1 hg, congr_add_coweight hμ g.2.2 hinv⟩
  · intro hg
    rw [blockMap_eq_one_iff]
    exact (hg.1.of_add_coweight hμ).2

theorem relIndex_add_coweight {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) (m : ℕ) :
    (levelSubgroup T (μ + coweight n m)).relIndex (levelSubgroup T μ) ≠ 0 ∧
      (levelSubgroup T (μ + coweight n m)).relIndex (levelSubgroup T μ) ≤
        T.residueCardinality ^ Nat.card (Block n m) := by
  have := T.finite_residueField
  have hk : (levelSubgroup T (μ + coweight n m)).relIndex (levelSubgroup T μ) =
      Nat.card (blockMap T μ m).range := by
    rw [Subgroup.relIndex, ← blockMap_ker hμ m, Subgroup.index_ker]
  rw [hk]
  refine ⟨Nat.card_pos.ne', ?_⟩
  calc Nat.card (blockMap T μ m).range
      ≤ Nat.card (Multiplicative (Block n m → T.ResidueField)) := Finite.card_subtype_le _
    _ = Nat.card (Block n m → T.ResidueField) := Nat.card_congr Multiplicative.toAdd
    _ = T.residueCardinality ^ Nat.card (Block n m) := by
      rw [Nat.card_fun]
      rfl

/-! ### Degrees -/

theorem degree_add {n : ℕ} (lam μ : Fin n → ℤ) : degree (lam + μ) = degree lam + degree μ := by
  simp only [degree, Pi.add_apply, add_sub_add_comm, Finset.sum_add_distrib]

theorem degree_coweight (n m : ℕ) : degree (coweight n m) = Nat.card (Block n m) := by
  classical
  have hterm : ∀ i j : Fin n, i < j →
      coweight n m i - coweight n m j = if (i : ℕ) < m ∧ m ≤ (j : ℕ) then 1 else 0 := by
    intro i j hij
    have hij' : (i : ℕ) < j := hij
    unfold coweight
    split_ifs <;> omega
  have hsum : ∀ i : Fin n,
      ∑ j ∈ Finset.univ.filter (fun j => i < j), (coweight n m i - coweight n m j) =
        ∑ j : Fin n, if (i : ℕ) < m ∧ m ≤ (j : ℕ) then (1 : ℤ) else 0 := by
    intro i
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h1 h2 h2
    · rw [hterm i j h1, ite_eq_left h2]
    · rw [hterm i j h1, ite_eq_right h2]
    · exfalso
      exact h1 (show (i : ℕ) < j by omega)
    · rfl
  rw [degree, Finset.sum_congr rfl fun i _ => hsum i, ← Fintype.sum_prod_type',
    Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-! ### The induction on the degree -/

theorem exists_descent {n : ℕ} {lam : Fin n → ℤ} (hlam : Antitone lam)
    (hne : ¬ ∀ i j, lam i = lam j) :
    ∃ (m : ℕ) (hm : 0 < m) (hmn : m < n), lam ⟨m, hmn⟩ < lam ⟨m - 1, by omega⟩ := by
  by_contra! h
  apply hne
  have key : ∀ (k : ℕ) (hk : k < n), lam ⟨k, hk⟩ = lam ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have h1 := h (k + 1) (by omega) hk
      have h2 := hlam (show (⟨k, by omega⟩ : Fin n) ≤ ⟨k + 1, hk⟩ from
        Fin.mk_le_mk.mpr (by omega))
      simp only [Nat.add_sub_cancel] at h1
      rw [← ih (by omega)]
      exact le_antisymm h2 h1
  intro i j
  have hi := key i i.2
  have hj := key j j.2
  simp only [Fin.eta] at hi hj
  rw [hi, hj]

theorem antitone_sub_coweight {n : ℕ} {lam : Fin n → ℤ} (hlam : Antitone lam) {m : ℕ}
    (hm : 0 < m) (hmn : m < n) (hd : lam ⟨m, hmn⟩ < lam ⟨m - 1, by omega⟩) :
    Antitone (lam - coweight n m) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  have h0 := hlam hij
  simp only [Pi.sub_apply, coweight]
  split_ifs with h1 h2 h2
  · linarith
  · omega
  · have hjm : lam j ≤ lam ⟨m, hmn⟩ := hlam (Fin.mk_le_mk.mpr (by omega) : (⟨m, hmn⟩ : Fin n) ≤ j)
    have him : lam ⟨m - 1, by omega⟩ ≤ lam i :=
      hlam (Fin.mk_le_mk.mpr (by omega) : i ≤ (⟨m - 1, by omega⟩ : Fin n))
    linarith
  · linarith

theorem relIndex_levelSubgroup_le (n : ℕ) :
    ∀ (N : ℕ) (lam : Fin n → ℤ), Antitone lam → degree lam < N →
      (levelSubgroup T lam).relIndex (levelSubgroup T (0 : Fin n → ℤ)) ≠ 0 ∧
        ((levelSubgroup T lam).relIndex (levelSubgroup T (0 : Fin n → ℤ)) : ℝ) ≤
          (T.residueCardinality : ℝ) ^ degree lam := by
  have hq : (0 : ℝ) < T.residueCardinality := by
    exact_mod_cast (Nat.zero_lt_one.trans T.residueCardinality_gt_one)
  intro N
  induction N with
  | zero =>
    intro lam hlam hN
    exact absurd hN (not_lt.mpr (by exact_mod_cast degree_nonneg lam hlam))
  | succ N ih =>
    intro lam hlam hN
    by_cases hc : ∀ i j, lam i = lam j
    · have hlev : ∀ i j, lev lam i j = lev (0 : Fin n → ℤ) i j := fun i j => by
        simp [lev, hc i j]
      have hS : levelSubgroup T lam = levelSubgroup T (0 : Fin n → ℤ) := by
        ext g
        simp only [mem_levelSubgroup, Congr, hlev]
      have hd : degree lam = 0 := Finset.sum_eq_zero fun i _ =>
        Finset.sum_eq_zero fun j _ => by rw [hc i j, sub_self]
      rw [hS, Subgroup.relIndex_self, hd]
      simp
    · obtain ⟨m, hm, hmn, hd⟩ := exists_descent hlam hc
      obtain ⟨μ, hμ, rfl⟩ : ∃ μ, Antitone μ ∧ lam = μ + coweight n m :=
        ⟨lam - coweight n m, antitone_sub_coweight hlam hm hmn hd, (sub_add_cancel _ _).symm⟩
      have hdeg : degree (μ + coweight n m) = degree μ + Nat.card (Block n m) := by
        rw [degree_add, degree_coweight]
      have hB : 0 < Nat.card (Block n m) := by
        have : Nonempty (Block n m) :=
          ⟨⟨(⟨m - 1, by omega⟩, ⟨m, hmn⟩), by simp only; omega⟩⟩
        exact Nat.card_pos
      obtain ⟨h0, hle0⟩ := ih μ hμ (by have := degree_nonneg μ hμ; push_cast at hN ⊢; omega)
      obtain ⟨h1, hle1⟩ := relIndex_add_coweight (T := T) hμ m
      have hmul := Subgroup.relIndex_mul_relIndex _ _ _ (levelSubgroup_add_coweight_le (T := T) hμ m)
        (levelSubgroup_le_zero (T := T) μ)
      refine ⟨?_, ?_⟩
      · rw [← hmul]
        exact mul_ne_zero h1 h0
      · rw [← hmul, Nat.cast_mul, hdeg, zpow_add₀ hq.ne', zpow_natCast, mul_comm]
        refine mul_le_mul hle0 (by exact_mod_cast hle1) (by positivity) (by positivity)

end CellCount

open CellCount in
/-- Every antidominant Cartan double coset `K a(lam) K` is covered by at most
`q ^ (n * n) * delta(lam)⁻¹` left translates `r a(lam) K`. -/
theorem cartanCellCount : CartanCellCountStatement.{uF} := by
  intro p _ F T n
  classical
  refine ⟨(T.residueCardinality : ℝ) ^ (n * n), fun lam hlam => ?_⟩
  let K := maximalCompact T n
  let S := levelSubgroup T lam
  obtain ⟨h0, hle0⟩ := relIndex_levelSubgroup_le (T := T) n ((degree lam).toNat + 1) lam hlam
    (by have := degree_nonneg lam hlam; omega)
  obtain ⟨h1, hle1⟩ := relIndex_levelSubgroup_zero (T := T) n
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ (levelSubgroup_le_zero (T := T) lam)
    (levelSubgroup_le_maximalCompact (T := T) (0 : Fin n → ℤ))
  have hidx : (S.subgroupOf K).index ≠ 0 := by
    change S.relIndex K ≠ 0
    rw [← hmul]
    exact mul_ne_zero h0 h1
  have : (S.subgroupOf K).FiniteIndex := ⟨hidx⟩
  let : Fintype (K ⧸ S.subgroupOf K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun x : K ⧸ S.subgroupOf K =>
    ((Quotient.out x : K) : GeneralLinear n F.Carrier), ?_, ?_⟩
  · have hq : (0 : ℝ) ≤ T.residueCardinality := Nat.cast_nonneg _
    calc ((Finset.univ.image fun x : K ⧸ S.subgroupOf K =>
          ((Quotient.out x : K) : GeneralLinear n F.Carrier)).card : ℝ)
        ≤ (Fintype.card (K ⧸ S.subgroupOf K) : ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ = (S.relIndex K : ℝ) := by
          rw [Fintype.card_eq_nat_card, ← Subgroup.index_eq_card]
          rfl
      _ = (S.relIndex (levelSubgroup T (0 : Fin n → ℤ)) : ℝ) *
          ((levelSubgroup T (0 : Fin n → ℤ)).relIndex K : ℝ) := by
          rw [← Nat.cast_mul, hmul]
      _ ≤ (T.residueCardinality : ℝ) ^ degree lam * (T.residueCardinality : ℝ) ^ (n * n) := by
          refine mul_le_mul hle0 (by exact_mod_cast hle1) (Nat.cast_nonneg _) (by positivity)
      _ = (T.residueCardinality : ℝ) ^ (n * n) * (delta T lam)⁻¹ := by
          rw [delta, zpow_neg, inv_inv, mul_comm]
  · intro k₁ hk₁ k₂ hk₂
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (S.subgroupOf K) ⟨k₁, hk₁⟩
    have hhS : ((h : K) : GeneralLinear n F.Carrier) ∈ S := Subgroup.mem_subgroupOf.mp h.2
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ
      (QuotientGroup.mk ⟨k₁, hk₁⟩ : K ⧸ S.subgroupOf K)),
      (representative T lam)⁻¹ * ((h : K) : GeneralLinear n F.Carrier)⁻¹ *
        representative T lam * k₂, ?_, ?_⟩
    · exact K.mul_mem (conj_mem_maximalCompact (S.inv_mem hhS)) hk₂
    · rw [hh, Subgroup.coe_mul]
      group

end Langlands.GeneralLinear.CartanQuotient
