import Langlands.Group.GL.ConjugatePairRefinementRankStatement
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Set.Card

/-! Strict refinement of concrete conjugate block pairs increases block length.
The split-component inclusion is compared through the linear spans of the
actual matrices, and the parabolic inclusion through the flags of subspaces
that the actual parabolics preserve. -/

noncomputable section

open Matrix

namespace Langlands.ConjugatePairRefinementRankProof

universe uF

open GeneralLinear Exponents

variable {K : Type uF} [Field K] {n : ℕ}

section Shape

variable (B : BlockShape n)

/-- The block containing a standard coordinate. -/
def blk (x : Fin n) : Fin B.length := (B.indexEquiv.symm x).1

theorem blk_index (i : Fin B.length) (r : Fin (B.size i)) : blk B (B.index i r) = i := by
  change (B.indexEquiv.symm (B.indexEquiv ⟨i, r⟩)).1 = i
  rw [Equiv.symm_apply_apply]

/-- A chosen coordinate in each block. -/
def firstIndex (i : Fin B.length) : Fin n := B.index i ⟨0, B.positive i⟩

theorem blk_firstIndex (i : Fin B.length) : blk B (firstIndex B i) = i :=
  blk_index B i _

/-- Standard parabolic membership: entries vanish below the block diagonal. -/
theorem mem_parabolic_iff_blk (g : GeneralLinear n K) :
    g ∈ B.parabolic K ↔ ∀ x y : Fin n, blk B y < blk B x → g x y = 0 := by
  rw [B.mem_parabolic_iff]
  constructor
  · intro h x y hxy
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
    have hb : blk B (B.indexEquiv ⟨j, b⟩) = j := blk_index B j b
    have ha : blk B (B.indexEquiv ⟨i, a⟩) = i := blk_index B i a
    exact h i j a b (by rw [← ha, ← hb]; exact hxy)
  · intro h i j a b hij
    exact h _ _ (by rw [blk_index, blk_index]; exact hij)

/-! ### Block-scalar matrices with field coordinates -/

/-- Block-scalar matrices with arbitrary field coordinates. -/
def scalarLinear : (Fin B.length → K) →ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun a := Matrix.diagonal (fun x => a (blk B x))
  map_add' a b := by rw [Matrix.diagonal_add]; rfl
  map_smul' c a := by rw [RingHom.id_apply, ← Matrix.diagonal_smul]; rfl

theorem scalarLinear_apply (a : Fin B.length → K) :
    scalarLinear B a = Matrix.diagonal (fun x => a (blk B x)) := rfl

/-- Positive block sizes make the field-coordinate block scalars faithful. -/
theorem scalarLinear_injective :
    Function.Injective (scalarLinear (K := K) B) := by
  intro a b h
  have h' := Matrix.diagonal_injective h
  funext i
  have := congrFun h' (firstIndex B i)
  simpa only [blk_firstIndex] using this

/-! ### Flags preserved by the standard parabolic -/

/-- Vectors vanishing on all blocks numbered `m` or later. -/
def flag (m : ℕ) : Submodule K (Fin n → K) where
  carrier := {v | ∀ x, m ≤ (blk B x : ℕ) → v x = 0}
  add_mem' := by
    intro v w hv hw x hx
    simp [hv x hx, hw x hx]
  zero_mem' := by
    intro x _
    rfl
  smul_mem' := by
    intro c v hv x hx
    simp [hv x hx]

theorem mem_flag (m : ℕ) (v : Fin n → K) :
    v ∈ flag (K := K) B m ↔ ∀ x, m ≤ (blk B x : ℕ) → v x = 0 := Iff.rfl

/-- A coordinate vector lies in every flag subspace beyond its block. -/
theorem single_mem_flag {m : ℕ} {y : Fin n} (hy : (blk B y : ℕ) < m) :
    (Pi.single y 1 : Fin n → K) ∈ flag B m := by
  intro x hx
  have hxy : x ≠ y := by
    rintro rfl
    omega
  simp [hxy]

/-- The last flag subspace is the whole space. -/
theorem flag_length : flag (K := K) B B.length = ⊤ := by
  rw [eq_top_iff]
  intro v _ x hx
  exact absurd (blk B x).isLt (not_lt.mpr hx)

/-- The first flag subspace is zero. -/
theorem flag_zero : flag (K := K) B 0 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  funext x
  exact hv x (Nat.zero_le _)

/-- The standard parabolic preserves each flag subspace. -/
theorem mulVec_mem_flag {g : GeneralLinear n K} (hg : g ∈ B.parabolic K) {m : ℕ}
    {v : Fin n → K} (hv : v ∈ flag B m) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ flag B m := by
  rw [mem_parabolic_iff_blk] at hg
  intro x hx
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : m ≤ (blk B y : ℕ)
  · rw [hv y hy, mul_zero]
  · have hxy : blk B y < blk B x := by
      rw [Fin.lt_def]
      omega
    rw [hg x y hxy, zero_mul]

/-- A matrix preserving every standard flag subspace is in the standard parabolic. -/
theorem mem_parabolic_of_flag (g : GeneralLinear n K)
    (hg : ∀ m ≤ B.length, ∀ v ∈ flag (K := K) B m,
      (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ flag B m) :
    g ∈ B.parabolic K := by
  rw [mem_parabolic_iff_blk]
  intro x y hxy
  have hm : (blk B y : ℕ) + 1 ≤ B.length := (blk B y).isLt
  have hv := hg _ hm _ (single_mem_flag B (Nat.lt_succ_self (blk B y : ℕ)))
  have hx := hv x (by rw [Fin.lt_def] at hxy; omega)
  simpa [Matrix.mulVec_single] using hx

/-- Distinct flag indices up to the number of blocks give distinct subspaces. -/
theorem flag_injective {m m' : ℕ} (hm : m ≤ B.length) (hm' : m' ≤ B.length)
    (h : flag (K := K) B m = flag B m') : m = m' := by
  by_contra hne
  wlog hlt : m < m' generalizing m m'
  · exact this hm' hm h.symm (Ne.symm hne) (by omega)
  let i : Fin B.length := ⟨m, by omega⟩
  have hx : (blk B (firstIndex B i) : ℕ) = m := by rw [blk_firstIndex]
  have hmem : (Pi.single (firstIndex B i) 1 : Fin n → K) ∈ flag B m' :=
    single_mem_flag B (by omega)
  rw [← h] at hmem
  have := hmem (firstIndex B i) hx.ge
  simp at this

end Shape

/-! ### Elements of the standard parabolic producing coordinate vectors -/

/-- For coordinates `q` and `x` with the block of `q` not after that of `x`,
some standard parabolic element moves every vector by a nonzero multiple of
its `x` coordinate in the direction of `q`. -/
theorem exists_parabolic_shift (B : BlockShape n) (ht : ∃ t : K, t ≠ 0 ∧ t ≠ 1)
    {q x : Fin n} (hqx : blk B q ≤ blk B x) :
    ∃ g ∈ B.parabolic K, ∃ s : K, s ≠ 0 ∧
      ∀ u : Fin n → K, (g : Matrix (Fin n) (Fin n) K) *ᵥ u - u =
        (s * u x) • Pi.single q 1 := by
  by_cases hq : q = x
  · subst q
    obtain ⟨t, ht0, ht1⟩ := ht
    let d : Fin n → K := Function.update 1 x t
    have hd : (Matrix.diagonal d).det ≠ 0 := by
      rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
      intro z _
      by_cases hz : z = x
      · subst z
        simp [d, ht0]
      · simp [d, hz]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_, t - 1, sub_ne_zero.mpr ht1, ?_⟩
    · rw [mem_parabolic_iff_blk]
      intro a b hab
      have hne : a ≠ b := by
        rintro rfl
        exact lt_irrefl _ hab
      simp [Matrix.diagonal_apply_ne _ hne]
    · intro u
      have hval : ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd : GeneralLinear n K) :
          Matrix (Fin n) (Fin n) K) = Matrix.diagonal d := rfl
      rw [hval]
      funext z
      rw [Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hz : z = x
      · subst z
        simp only [d, Function.update_self, Pi.single_eq_same, mul_one]
        ring
      · simp [d, hz]
  · have hd : (Matrix.transvection q x (1 : K)).det ≠ 0 := by
      rw [Matrix.det_transvection_of_ne _ _ hq]
      exact one_ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_, 1, one_ne_zero, ?_⟩
    · rw [mem_parabolic_iff_blk]
      intro a b hab
      have hne : a ≠ b := by
        rintro rfl
        exact lt_irrefl _ hab
      have hs : ¬ (q = a ∧ x = b) := by
        rintro ⟨rfl, rfl⟩
        exact absurd hqx (not_le.mpr hab)
      simp [Matrix.transvection, Matrix.one_apply_ne hne, Matrix.single_apply_of_ne _ _ _ _ _ hs]
    · intro u
      have hval : ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd : GeneralLinear n K) :
          Matrix (Fin n) (Fin n) K) = Matrix.transvection q x 1 := rfl
      rw [hval, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left,
        Matrix.single_mulVec_eq]

/-- The subspaces invariant under the standard parabolic are exactly its flags. -/
theorem eq_flag_of_invariant (B : BlockShape n) (ht : ∃ t : K, t ≠ 0 ∧ t ≠ 1)
    (U : Submodule K (Fin n → K))
    (hU : ∀ g ∈ B.parabolic K, ∀ u ∈ U, (g : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ U) :
    ∃ m ≤ B.length, U = flag B m := by
  classical
  have hex : ∃ m, U ≤ flag B m := ⟨B.length, by rw [flag_length]; exact le_top⟩
  let m := Nat.find hex
  have hm : U ≤ flag B m := Nat.find_spec hex
  have hmk : m ≤ B.length := Nat.find_min' hex (by rw [flag_length]; exact le_top)
  refine ⟨m, hmk, le_antisymm hm ?_⟩
  rcases Nat.eq_zero_or_eq_succ_pred m with h0 | hsucc
  · rw [h0, flag_zero]
    exact bot_le
  · have hlt : m - 1 < m := by omega
    have hnot : ¬ U ≤ flag B (m - 1) := Nat.find_min hex hlt
    rw [SetLike.not_le_iff_exists] at hnot
    obtain ⟨u, huU, hu⟩ := hnot
    rw [mem_flag] at hu
    push Not at hu
    obtain ⟨x, hx, hux⟩ := hu
    have hxm : (blk B x : ℕ) < m := by
      by_contra hc
      exact hux (hm huU x (not_lt.mp hc))
    intro v hv
    rw [pi_eq_sum_univ' v]
    apply Submodule.sum_mem
    intro q _
    by_cases hvq : v q = 0
    · rw [hvq, zero_smul]
      exact U.zero_mem
    · have hq : (blk B q : ℕ) < m := by
        by_contra hc
        exact hvq (hv q (not_lt.mp hc))
      have hqx : blk B q ≤ blk B x := by
        rw [Fin.le_def]
        omega
      obtain ⟨g, hg, s, hs, hgu⟩ := exists_parabolic_shift B ht hqx
      have hmem : (s * u x) • (Pi.single q 1 : Fin n → K) ∈ U := by
        rw [← hgu u]
        exact U.sub_mem (hU g hg u huU) huU
      have hsx : s * u x ≠ 0 := mul_ne_zero hs hux
      apply U.smul_mem
      have := U.smul_mem (s * u x)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hsx, one_smul] at this

/-! ### Conjugated pairs -/

section Pair

variable (P : ConjugateBlockPair n K)

local notation "mat" g => ((g : GeneralLinear n K) : Matrix (Fin n) (Fin n) K)

/-- Membership in the actual parabolic, after cancelling the conjugator. -/
theorem mem_parabolic_iff_conj (g : GeneralLinear n K) :
    g ∈ P.parabolic ↔ P.conjugator⁻¹ * g * P.conjugator ∈ P.shape.parabolic K := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    change P.conjugator⁻¹ * (P.conjugator * h * P.conjugator⁻¹) * P.conjugator ∈ _
    simpa [mul_assoc] using hh
  · intro hg
    refine ⟨_, hg, ?_⟩
    change P.conjugator * (P.conjugator⁻¹ * g * P.conjugator) * P.conjugator⁻¹ = g
    group

/-- Conjugated matrices act on conjugated vectors. -/
theorem conj_mulVec (c g : GeneralLinear n K) (v : Fin n → K) :
    (mat (c⁻¹ * g * c)) *ᵥ ((mat c⁻¹) *ᵥ v) = (mat c⁻¹) *ᵥ ((mat g) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  group

theorem inv_mulVec_mulVec (c : GeneralLinear n K) (v : Fin n → K) :
    (mat c⁻¹) *ᵥ ((mat c) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]

theorem mulVec_inv_mulVec (c : GeneralLinear n K) (v : Fin n → K) :
    (mat c) *ᵥ ((mat c⁻¹) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec]

/-- The conjugated flag subspaces of a pair. -/
def pairFlag (m : ℕ) : Submodule K (Fin n → K) :=
  (flag P.shape m).comap (Matrix.toLin' (mat P.conjugator⁻¹))

theorem mem_pairFlag (m : ℕ) (v : Fin n → K) :
    v ∈ pairFlag P m ↔ (mat P.conjugator⁻¹) *ᵥ v ∈ flag P.shape m := by
  rw [pairFlag, Submodule.mem_comap, Matrix.toLin'_apply]

/-- The actual parabolic preserves each conjugated flag subspace. -/
theorem mulVec_mem_pairFlag {g : GeneralLinear n K} (hg : g ∈ P.parabolic) {m : ℕ}
    {v : Fin n → K} (hv : v ∈ pairFlag P m) : (mat g) *ᵥ v ∈ pairFlag P m := by
  rw [mem_pairFlag] at hv ⊢
  rw [← conj_mulVec]
  exact mulVec_mem_flag P.shape ((mem_parabolic_iff_conj P g).mp hg) hv

/-- A matrix preserving every conjugated flag subspace is in the actual parabolic. -/
theorem mem_parabolic_of_pairFlag (g : GeneralLinear n K)
    (hg : ∀ m ≤ P.shape.length, ∀ v ∈ pairFlag P m, (mat g) *ᵥ v ∈ pairFlag P m) :
    g ∈ P.parabolic := by
  rw [mem_parabolic_iff_conj]
  apply mem_parabolic_of_flag
  intro m hm w hw
  have hv : (mat P.conjugator) *ᵥ w ∈ pairFlag P m := by
    rw [mem_pairFlag, inv_mulVec_mulVec]
    exact hw
  have h := (mem_pairFlag P m _).mp (hg m hm _ hv)
  rwa [← conj_mulVec, inv_mulVec_mulVec] at h

/-- The subspaces invariant under the actual parabolic are its conjugated flags. -/
theorem eq_pairFlag_of_invariant (ht : ∃ t : K, t ≠ 0 ∧ t ≠ 1)
    (U : Submodule K (Fin n → K))
    (hU : ∀ g ∈ P.parabolic, ∀ u ∈ U, (mat g) *ᵥ u ∈ U) :
    ∃ m ≤ P.shape.length, U = pairFlag P m := by
  let U' := U.comap (Matrix.toLin' (mat P.conjugator))
  have hmem' : ∀ w, w ∈ U' ↔ (mat P.conjugator) *ᵥ w ∈ U := by
    intro w
    rw [Submodule.mem_comap, Matrix.toLin'_apply]
  have hU' : ∀ h ∈ P.shape.parabolic K, ∀ w ∈ U', (mat h) *ᵥ w ∈ U' := by
    intro h hh w hw
    rw [hmem'] at hw ⊢
    have hc : P.conjugator * h * P.conjugator⁻¹ ∈ P.parabolic := by
      rw [mem_parabolic_iff_conj]
      simpa [mul_assoc] using hh
    have key := hU _ hc _ hw
    have heq : (mat (P.conjugator * h * P.conjugator⁻¹)) *ᵥ ((mat P.conjugator) *ᵥ w) =
        (mat P.conjugator) *ᵥ ((mat h) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rwa [heq] at key
  obtain ⟨m, hm, hUm⟩ := eq_flag_of_invariant P.shape ht U' hU'
  refine ⟨m, hm, ?_⟩
  ext v
  rw [mem_pairFlag, ← hUm, hmem', mulVec_inv_mulVec]

/-- Distinct flag indices give distinct conjugated flag subspaces. -/
theorem pairFlag_injective {m m' : ℕ} (hm : m ≤ P.shape.length) (hm' : m' ≤ P.shape.length)
    (h : pairFlag P m = pairFlag P m') : m = m' := by
  apply flag_injective (K := K) P.shape hm hm'
  ext w
  have := congrArg (fun U : Submodule K (Fin n → K) => (mat P.conjugator) *ᵥ w ∈ U) h
  simp only [mem_pairFlag, inv_mulVec_mulVec, eq_iff_iff] at this
  exact this

/-! ### Linear spans of split components -/

/-- The conjugated block-scalar matrices with arbitrary field coordinates. -/
def pairLinear : (Fin P.shape.length → K) →ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun a := (mat P.conjugator) * scalarLinear P.shape a * (mat P.conjugator⁻¹)
  map_add' a b := by rw [map_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c a := by
    rw [map_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem pairLinear_apply (a : Fin P.shape.length → K) :
    pairLinear P a = (mat P.conjugator) * scalarLinear P.shape a * (mat P.conjugator⁻¹) :=
  rfl

/-- The conjugated field-coordinate block scalars are faithful. -/
theorem pairLinear_injective : Function.Injective (pairLinear P) := by
  intro a b h
  apply scalarLinear_injective P.shape
  have h' := congrArg (fun X => (mat P.conjugator⁻¹) * X * (mat P.conjugator)) h
  simp only [pairLinear_apply] at h'
  have e : ∀ X : Matrix (Fin n) (Fin n) K,
      (mat P.conjugator⁻¹) * ((mat P.conjugator) * X * (mat P.conjugator⁻¹)) *
        (mat P.conjugator) = X := by
    intro X
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  rwa [e, e] at h'

/-- Actual split-component matrices are the unit-coordinate values of `pairLinear`. -/
theorem coe_scalarMap (a : Fin P.shape.length → Kˣ) :
    (mat P.scalarMap a) = pairLinear P (fun i => (a i : K)) := by
  rw [ConjugateBlockPair.scalarMap_apply, Units.val_mul, Units.val_mul,
    BlockShape.coe_blockScalar]
  rfl

/-- The linear span of the actual split-component matrices. -/
def splitSpan : Submodule K (Matrix (Fin n) (Fin n) K) :=
  Submodule.span K ((fun g : GeneralLinear n K => (mat g)) '' (P.splitComponent : Set _))

/-- Over a field with an element other than `0` and `1`, the actual split
component spans the conjugated block-scalar algebra. -/
theorem splitSpan_eq (ht : ∃ t : K, t ≠ 0 ∧ t ≠ 1) :
    splitSpan P = LinearMap.range (pairLinear P) := by
  classical
  apply le_antisymm
  · rw [splitSpan, Submodule.span_le]
    rintro _ ⟨g, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, (coe_scalarMap P a).symm⟩
  · rintro _ ⟨v, rfl⟩
    rw [pi_eq_sum_univ' v, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    apply Submodule.smul_mem
    obtain ⟨t, ht0, ht1⟩ := ht
    let a : Fin P.shape.length → Kˣ := Function.update 1 i (Units.mk0 t ht0)
    have ha : (Pi.single i 1 : Fin P.shape.length → K) =
        (t - 1)⁻¹ • ((fun j => (a j : K)) - fun j => ((1 : Fin P.shape.length → Kˣ) j : K)) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [a, inv_mul_cancel₀ (sub_ne_zero.mpr ht1)]
      · simp [a, hj]
    rw [ha, map_smul, map_sub]
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · rw [← coe_scalarMap]
      exact Submodule.subset_span ⟨_, ⟨a, rfl⟩, rfl⟩
    · rw [← coe_scalarMap]
      exact Submodule.subset_span ⟨_, ⟨1, rfl⟩, rfl⟩

/-- The span of the actual split component has dimension equal to the block length. -/
theorem finrank_splitSpan (ht : ∃ t : K, t ≠ 0 ∧ t ≠ 1) :
    Module.finrank K (splitSpan P) = P.shape.length := by
  rw [splitSpan_eq P ht, LinearMap.finrank_range_of_inj (pairLinear_injective P),
    Module.finrank_fin_fun]

/-- A matrix group element in the conjugated block-scalar algebra lies in the
actual split component. -/
theorem mem_splitComponent_of_mem_range (g : GeneralLinear n K)
    (hg : (mat g) ∈ LinearMap.range (pairLinear P)) : g ∈ P.splitComponent := by
  obtain ⟨v, hv⟩ := hg
  have hdet : (mat g).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    exact this.ne_zero
  have hdiag : (scalarLinear P.shape v).det ≠ 0 := by
    rw [← hv, pairLinear_apply, Matrix.det_mul, Matrix.det_mul] at hdet
    intro h0
    apply hdet
    rw [h0, mul_zero, zero_mul]
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i hi
    apply hdiag
    rw [scalarLinear_apply, Matrix.det_diagonal]
    apply Finset.prod_eq_zero (Finset.mem_univ (firstIndex P.shape i))
    rw [blk_firstIndex, hi]
  refine ⟨fun i => Units.mk0 (v i) (hv0 i), ?_⟩
  apply Units.ext
  rw [coe_scalarMap, ← hv]
  rfl

end Pair

/-! ### Comparison of pairs -/

/-- Split-component inclusion bounds the block lengths. -/
theorem length_le_of_splitComponent_le (ht : ∃ t : K, t ≠ 0 ∧ t ≠ 1)
    {P Q : ConjugateBlockPair n K} (h : P.splitComponent ≤ Q.splitComponent) :
    P.shape.length ≤ Q.shape.length := by
  rw [← finrank_splitSpan P ht, ← finrank_splitSpan Q ht]
  exact Submodule.finrank_mono (Submodule.span_mono (Set.image_mono h))

/-- Split-component inclusion between pairs of the same length is an equality. -/
theorem splitComponent_le_of_length_eq (ht : ∃ t : K, t ≠ 0 ∧ t ≠ 1)
    {P Q : ConjugateBlockPair n K} (h : P.splitComponent ≤ Q.splitComponent)
    (hl : P.shape.length = Q.shape.length) : Q.splitComponent ≤ P.splitComponent := by
  have hspan : splitSpan P = splitSpan Q :=
    Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono (Set.image_mono h))
      (by rw [finrank_splitSpan P ht, finrank_splitSpan Q ht, hl])
  intro g hg
  apply mem_splitComponent_of_mem_range P g
  rw [← splitSpan_eq P ht, hspan]
  exact Submodule.subset_span ⟨g, hg, rfl⟩

/-- Parabolic inclusion between pairs of the same length is an equality. -/
theorem parabolic_le_of_length_eq (ht : ∃ t : K, t ≠ 0 ∧ t ≠ 1)
    {P Q : ConjugateBlockPair n K} (h : Q.parabolic ≤ P.parabolic)
    (hl : P.shape.length = Q.shape.length) : P.parabolic ≤ Q.parabolic := by
  let SP : Set (Submodule K (Fin n → K)) :=
    Set.range fun m : Fin (P.shape.length + 1) => pairFlag P m
  let SQ : Set (Submodule K (Fin n → K)) :=
    Set.range fun m : Fin (Q.shape.length + 1) => pairFlag Q m
  have hsub : SP ⊆ SQ := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨m', hm', he⟩ := eq_pairFlag_of_invariant Q ht (pairFlag P m)
      (fun g hg u hu => mulVec_mem_pairFlag P (h hg) hu)
    exact ⟨⟨m', by omega⟩, he.symm⟩
  have hinjP : Function.Injective fun m : Fin (P.shape.length + 1) => pairFlag P m := by
    intro a b hab
    exact Fin.ext (pairFlag_injective P (by omega) (by omega) hab)
  have hinjQ : Function.Injective fun m : Fin (Q.shape.length + 1) => pairFlag Q m := by
    intro a b hab
    exact Fin.ext (pairFlag_injective Q (by omega) (by omega) hab)
  have hcard : SQ.ncard ≤ SP.ncard := by
    rw [Set.ncard_range_of_injective hinjP, Set.ncard_range_of_injective hinjQ,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_fin, hl]
  have heq : SP = SQ := Set.eq_of_subset_of_ncard_le hsub hcard (Set.finite_range _)
  intro g hg
  apply mem_parabolic_of_pairFlag Q g
  intro m hm v hv
  have hQ : pairFlag Q m ∈ SQ := ⟨⟨m, by omega⟩, rfl⟩
  rw [← heq] at hQ
  obtain ⟨m', hm'⟩ := hQ
  rw [← hm'] at hv ⊢
  exact mulVec_mem_pairFlag P hg hv

/-- Strict refinement of actual pairs increases the block length. -/
theorem length_lt_of_strictlyRefines (ht : ∃ t : K, t ≠ 0 ∧ t ≠ 1)
    {P Q : ConjugateBlockPair n K} (h : Q.StrictlyRefines P) :
    P.shape.length < Q.shape.length := by
  obtain ⟨⟨hpar, hsplit⟩, hnot⟩ := h
  have hle := length_le_of_splitComponent_le ht hsplit
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd ⟨parabolic_le_of_length_eq ht hpar heq,
      splitComponent_le_of_length_eq ht hsplit heq⟩ hnot

end Langlands.ConjugatePairRefinementRankProof

namespace Langlands

universe uF

open ConjugatePairRefinementRankProof in
/-- Strict refinement of actual conjugate block pairs increases block length,
which is bounded by the ambient rank, over every infinite field. -/
theorem conjugatePairRefinementRank : ConjugatePairRefinementRankStatement.{uF} := by
  intro K _ _ n
  classical
  have ht : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset K)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    exact ⟨t, ht⟩
  exact ⟨fun P Q h => length_lt_of_strictlyRefines ht h, fun P => P.shape.length_le⟩

end Langlands
