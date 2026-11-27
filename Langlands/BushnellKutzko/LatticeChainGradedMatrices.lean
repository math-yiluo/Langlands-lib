import Langlands.BushnellKutzko.StratumExistence
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Matrices on the graded pieces of a lattice chain -/

noncomputable section

open ValuativeRel IsLocalRing Matrix

namespace Langlands.BushnellKutzko.LatticeChain

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (L : LatticeChain 𝒪[F] F V) {π : 𝒪[F]} (hπ : Irreducible π)

/-- A splitting basis can be normalized so that the indices of its vectors lie in one period. -/
theorem exists_basis_splits_normalized :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) F V), L.Splits b ∧
      ∀ i, 0 ≤ L.index hπ (b i) ∧ L.index hπ (b i) < L.period := by
  classical
  obtain ⟨d, b, hb⟩ := L.exists_basis_splits hπ
  let t (i : Fin d) : ℤ := -(L.index hπ (b i) / L.period)
  let w (i : Fin d) : Fˣ := Units.mk0 ((π : F) ^ t i)
    (zpow_ne_zero _ (coe_uniformizer_ne_zero hπ))
  refine ⟨d, b.unitsSMul w, ?_, ?_⟩
  · intro c k hc i
    simp only [Module.Basis.unitsSMul_apply, Units.smul_def, smul_smul] at hc ⊢
    exact hb _ k hc i
  · intro i
    simp only [Module.Basis.unitsSMul_apply, Units.smul_def]
    change 0 ≤ L.index hπ (((π : F) ^ t i) • b i) ∧
      L.index hπ (((π : F) ^ t i) • b i) < L.period
    rw [L.index_smul hπ (zpow_ne_zero _ (coe_uniformizer_ne_zero hπ)) (b.ne_zero i),
      ordOf_zpow]
    have he : (0 : ℤ) < L.period := by exact_mod_cast L.period_pos
    have hm := Int.emod_add_mul_ediv (L.index hπ (b i)) (L.period : ℤ)
    have h0 := Int.emod_nonneg (L.index hπ (b i)) he.ne'
    have h1 := Int.emod_lt_of_pos (L.index hπ (b i)) he
    dsimp only [t]
    rw [mul_neg, ← sub_eq_add_neg]
    omega

variable {d : ℕ} (b : Module.Basis (Fin d) F V)

local notation "ν" => fun i => L.index hπ (b i)
local notation "mat" => LinearMap.toMatrix b b

/-- In a splitting basis the filtration is an entrywise valuation inequality. -/
theorem mem_endFiltration_iff_matrix_ord (hb : L.Splits b) (n : ℤ) (x : Module.End F V) :
    x ∈ L.endFiltration n ↔
      ∀ i j, mat x i j ≠ 0 → ν j + n ≤ ν i + L.period * ordOf hπ (mat x i j) := by
  constructor
  · intro hx i j hc
    have h := hx (ν j) _ (L.mem_lattice_index hπ (b.ne_zero j))
    have h' := hb (fun k => b.repr (x (b j)) k) (ν j + n) (by simpa only [b.sum_repr] using h) i
    rw [LinearMap.toMatrix_apply] at hc ⊢
    rwa [L.mem_iff_le_index hπ (smul_ne_zero hc (b.ne_zero i)),
      L.index_smul hπ hc (b.ne_zero i)] at h'
  · intro h k v hv
    have hv' := hb (fun j => b.repr v j) k (by simpa only [b.sum_repr] using hv)
    have hsum : x v = ∑ j, b.repr v j • x (b j) := by
      simp only [← map_smul, ← map_sum, b.sum_repr]
    rw [hsum]
    apply Submodule.sum_mem
    intro j _
    let c := b.repr v j
    change c • x (b j) ∈ L.lattice (k + n)
    by_cases hc : c = 0
    · simp [hc]
    have hj : k ≤ ν j + L.period * ordOf hπ c := by
      have hterm := hv' j
      change c • b j ∈ L.lattice k at hterm
      rwa [L.mem_iff_le_index hπ (smul_ne_zero hc (b.ne_zero j)),
        L.index_smul hπ hc (b.ne_zero j)] at hterm
    have hx : x (b j) = ∑ i, mat x i j • b i := by
      simpa only [LinearMap.toMatrix_apply] using (b.sum_repr (x (b j))).symm
    rw [hx, Finset.smul_sum]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : mat x i j = 0
    · simp [hi]
    rw [smul_smul, L.mem_iff_le_index hπ (smul_ne_zero (mul_ne_zero hc hi) (b.ne_zero i)),
      L.index_smul hπ (mul_ne_zero hc hi) (b.ne_zero i), ordOf_mul hπ hc hi, mul_add]
    have hji := h i j hi
    dsimp only at hj hji
    omega

/-- At depths zero and one, entries are integral. Those from a column of index `ν j` to a row of
index less than `ν j + n` are in the maximal ideal. -/
theorem mem_endFiltration_iff_integral_entries (hb : L.Splits b)
    (hν : ∀ i, 0 ≤ ν i ∧ ν i < L.period) {n : ℤ} (hn : 0 ≤ n) (hn' : n ≤ 1)
    (x : Module.End F V) : x ∈ L.endFiltration n ↔
      ∀ i j, ∃ a : 𝒪[F], (a : F) = mat x i j ∧ (ν i < ν j + n → a ∈ 𝓂[F]) := by
  rw [L.mem_endFiltration_iff_matrix_ord hπ b hb]
  have he : (0 : ℤ) < L.period := by exact_mod_cast L.period_pos
  constructor
  · intro hx i j
    let c := mat x i j
    by_cases hc : c = 0
    · exact ⟨0, hc.symm, fun _ => zero_mem _⟩
    have hj := hν j
    have hi := hν i
    have hc' : 0 ≤ ordOf hπ c := by
      by_contra! h
      have hbound : (L.period : ℤ) * ordOf hπ c ≤ L.period * (-1) :=
        mul_le_mul_of_nonneg_left (by omega) he.le
      have hh := hx i j hc
      change ν j + n ≤ ν i + L.period * ordOf hπ c at hh
      simp only [mul_neg, mul_one] at hbound
      omega
    refine ⟨⟨c, mem_integer_of_ordOf_nonneg hπ hc hc'⟩, rfl, fun hlt => ?_⟩
    rw [IsLocalRing.mem_maximalIdeal]
    intro hunit
    obtain ⟨a, ha⟩ := hunit
    have hval : ((a : 𝒪[F]) : F) = c := congrArg Subtype.val ha
    have hz : ordOf hπ c = 0 := by simpa [hval] using ordOf_zpow_mul_unit hπ 0 a
    have hh := hx i j hc
    change ν j + n ≤ ν i + L.period * ordOf hπ c at hh
    rw [hz, mul_zero, add_zero] at hh
    exact (not_lt_of_ge hh) hlt
  · intro hx i j hc
    obtain ⟨a, ha, hma⟩ := hx i j
    rw [← ha] at hc ⊢
    by_cases hlt : ν i < ν j + n
    · have ho := one_le_ordOf_of_mem_maximalIdeal hπ (hma hlt) hc
      have hmul : (L.period : ℤ) ≤ L.period * ordOf hπ (a : F) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left ho he.le
      have hj := hν j
      have hi := hν i
      omega
    · have ho := ordOf_nonneg hπ hc a.2
      exact (not_lt.mp hlt).trans (le_add_of_nonneg_right (mul_nonneg he.le ho))

variable (hb : L.Splits b) (hν : ∀ i, 0 ≤ ν i ∧ ν i < L.period)

local notation "grade" => (fun i : Fin d => - (ν i))
local notation "O" => 𝒪[F]
local notation "k" => ResidueField O

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem matrixMap_injective :
    Function.Injective ((𝒪[F].subtype).mapMatrix : Matrix (Fin d) (Fin d) O →+* _) := by
  intro M N h
  ext i j
  exact congrArg (fun A : Matrix (Fin d) (Fin d) F => A i j) h

/-- The integral matrix of an element of the lattice-chain order in the normalized basis. -/
def orderIntegralMatrix (hs : L.Splits b) (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period) :
    L.order →+* Matrix (Fin d) (Fin d) O := by
  have hentry (x : L.order) (i j : Fin d) : mat x.val i j ∈ 𝒪[F] := by
    obtain ⟨a, ha, _⟩ := (L.mem_endFiltration_iff_integral_entries hπ b hs hn le_rfl
      (by decide : (0 : ℤ) ≤ 1) x.val).mp x.property i j
    exact ha ▸ a.2
  let lift (x : L.order) : Matrix (Fin d) (Fin d) O := fun i j => ⟨_, hentry x i j⟩
  have hlift (x : L.order) : (𝒪[F].subtype).mapMatrix (lift x) =
      LinearMap.toMatrixAlgEquiv b x.val := rfl
  refine { toFun := lift, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }
  · apply matrixMap_injective (F := F)
    rw [hlift, map_one]
    exact map_one (LinearMap.toMatrixAlgEquiv b)
  · intro x y
    apply matrixMap_injective (F := F)
    rw [map_mul, hlift, hlift, hlift]
    exact map_mul (LinearMap.toMatrixAlgEquiv b) x.val y.val
  · apply matrixMap_injective (F := F)
    rw [hlift, map_zero]
    exact map_zero (LinearMap.toMatrixAlgEquiv b)
  · intro x y
    apply matrixMap_injective (F := F)
    rw [map_add, hlift, hlift, hlift]
    exact map_add (LinearMap.toMatrixAlgEquiv b) x.val y.val

@[simp]
theorem coe_orderIntegralMatrix_apply (x : L.order) (i j : Fin d) :
    (L.orderIntegralMatrix hπ b hb hν x i j : F) = mat x.val i j := rfl

/-- Entrywise reduction of the integral matrix of a chain-preserving endomorphism. -/
def orderResidueMatrix (hs : L.Splits b) (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period) :
    L.order →+* Matrix (Fin d) (Fin d) k :=
  RingHom.comp (residue O).mapMatrix (L.orderIntegralMatrix hπ b hs hn)

theorem orderResidueMatrix_blockTriangular (hs : L.Splits b)
    (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period) (x : L.order) :
    Matrix.BlockTriangular (orderResidueMatrix L hπ b hs hn x) grade := by
  intro i j hij
  obtain ⟨a, ha, hma⟩ := (L.mem_endFiltration_iff_integral_entries hπ b hs hn le_rfl
    (by decide : (0 : ℤ) ≤ 1) x.val).mp x.property i j
  change residue O (L.orderIntegralMatrix hπ b hs hn x i j) = 0
  rw [show L.orderIntegralMatrix hπ b hs hn x i j = a from Subtype.ext ha.symm]
  exact (residue_eq_zero_iff _).mpr (hma (by change - ν j < - ν i at hij; omega))

private theorem squareBlock_mul {M N : Matrix (Fin d) (Fin d) k}
    (hM : M.BlockTriangular grade) (hN : N.BlockTriangular grade) (s : ℤ) :
    (M * N).toSquareBlock grade s = M.toSquareBlock grade s * N.toSquareBlock grade s := by
  ext i j
  change (∑ a, M i.val a * N a j.val) =
    ∑ a : {a // grade a = s}, M i.val a.val * N a.val j.val
  rw [← Finset.sum_subtype (Finset.univ.filter fun a => grade a = s)
    (fun a => by simp) (fun a => M i.val a * N a j.val)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a _ ha
  have hne : grade a ≠ s := fun he => ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
  rcases lt_or_gt_of_ne hne with h | h
  · have hi : grade a < grade i.val := by simpa only [i.property] using h
    rw [hM hi, zero_mul]
  · have hj : grade j.val < grade a := by simpa only [j.property] using h
    rw [hN hj, mul_zero]

/-- The square block on the coordinates of one grade gives a multiplicative residue map. -/
def orderResidueBlock (hs : L.Splits b) (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period)
    (s : ℤ) : L.order →* Matrix {i // grade i = s} {i // grade i = s} k where
  toFun x := (L.orderResidueMatrix hπ b hs hn x).toSquareBlock grade s
  map_one' := by
    rw [map_one]
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply, Subtype.ext_iff]
  map_mul' x y := by
    rw [map_mul]
    exact squareBlock_mul L hπ b (L.orderResidueMatrix_blockTriangular hπ b hs hn x)
      (L.orderResidueMatrix_blockTriangular hπ b hs hn y) s

/-- A chain-preserving automorphism is trivial on the graded pieces precisely at depth one. -/
theorem mem_unitFiltration_one_iff_blocks (hs : L.Splits b)
    (hn : ∀ i, 0 ≤ ν i ∧ ν i < L.period) (g : L.unitFiltration 0) :
    g.val ∈ L.unitFiltration 1 ↔
      ∀ s, L.orderResidueBlock hπ b hs hn s ⟨(g.val : Module.End F V), g.property.1⟩ = 1 := by
  let x : L.order := ⟨(g.val : Module.End F V), g.property.1⟩
  let R := L.orderResidueMatrix hπ b hs hn
  let I := L.orderIntegralMatrix hπ b hs hn
  have hsub : R (x - 1) = R x - 1 := by
    have he := R.toAddMonoidHom.map_sub x 1
    change R (x - 1) = R x - R 1 at he
    rwa [R.map_one] at he
  have hiff : (g.val : Module.End F V) - 1 ∈ L.endFiltration 1 ↔
      ∀ i j, ν i ≤ ν j → R (x - 1) i j = 0 := by
    rw [L.mem_endFiltration_iff_integral_entries hπ b hs hn (by decide) le_rfl]
    constructor
    · intro h i j hij
      obtain ⟨a, ha, hma⟩ := h i j
      change residue O (I (x - 1) i j) = 0
      rw [show I (x - 1) i j = a from Subtype.ext ha.symm]
      exact (residue_eq_zero_iff _).mpr (hma (by omega))
    · intro h i j
      exact ⟨I (x - 1) i j, rfl, fun hij => (residue_eq_zero_iff _).mp (h i j (by omega))⟩
  change (_ ∧ _ ∧ _) ↔ _
  rw [and_iff_right g.property.1, and_iff_right g.property.2.1]
  change (g.val : Module.End F V) - 1 ∈ L.endFiltration 1 ↔ _
  rw [hiff]
  constructor
  · intro h s
    ext i j
    have hνij : ν i.val = ν j.val := by
      have := i.property.trans j.property.symm
      change - ν i.val = - ν j.val at this
      omega
    have he := h i.val j.val hνij.le
    rw [hsub, Matrix.sub_apply, sub_eq_zero] at he
    change R x i.val j.val = (1 : Matrix _ _ k) i j
    simp only [he, Matrix.one_apply, Subtype.ext_iff]
  · intro h i j hij
    rcases hij.lt_or_eq with hlt | heq
    · exact L.orderResidueMatrix_blockTriangular hπ b hs hn (x - 1)
        (show grade j < grade i by change - ν j < - ν i; omega)
    · let i' : {a // grade a = grade j} := ⟨i, by change - ν i = - ν j; rw [heq]⟩
      let j' : {a // grade a = grade j} := ⟨j, rfl⟩
      have he := congrArg (fun M => M i' j') (h (grade j))
      change R x i j = (1 : Matrix _ _ k) i' j' at he
      rw [hsub, Matrix.sub_apply, sub_eq_zero]
      simp only [he, Matrix.one_apply, Subtype.ext_iff]
      rfl

end Langlands.BushnellKutzko.LatticeChain
