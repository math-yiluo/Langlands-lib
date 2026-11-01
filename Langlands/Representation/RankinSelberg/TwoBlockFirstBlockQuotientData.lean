import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
import Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation

/-!
# The first-block norm-one quotient and the first-block slice average

JPSS (1983), Section 4.6, printed page 412, equation (6): for `r = t_1 + t_2`,

`∫_{N_(t_1,t_2) \ G_r^m} f(g) dg =
  ∫_{G_(t_1)^0 N_(t_1,t_2) \ G_r^0} dh ∫_{N_(t_1) \ G_(t_1)^m} f[diag(a, 1) h] d^×a`.

For two blocks of sizes `a = m 0 + 1` and `b = m 1 + 1` of total rank `t + 1`, this module
constructs the actual data of this displayed formula: the first-block embedding
`u ↦ diag(u, 1_b)`, the subgroup `L = diag(GL_a^0, N_b) = G_(t_1)^0 N_(t_1,t_2)` with its
quotient `L \ GL_(t+1)` and determinant slices, the fiber map
`([u], g) ↦ [diag(u, 1) g]_H` from the small quotient `N_a \ GL_a` to
`H \ GL_(t+1)` with `H = N_(t_1,t_2)`, the inner slice integral and its descent to
`L \ GL_(t+1)`. No integrability, quotient-measure, or Fubini statement is asserted.
-/

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg.TwoBlockFirstBlockQuotient

open GeneralLinear TwoBlockJacquet TwoBlockDeformation QuotientIntegration

universe uF uR

/-! ### Block-diagonal matrices -/

section Algebra

variable (R : Type uR) [CommRing R]

variable {m : Fin 2 → ℕ}

/-- The Levi element of the two blocks with diagonal blocks `u` and `w`. -/
def blockPair : GeneralLinear (m 0 + 1) R × GeneralLinear (m 1 + 1) R →*
    ∀ i : Fin 2, GeneralLinear (m i + 1) R where
  toFun x := Pi.mulSingle 0 x.1 * Pi.mulSingle 1 x.2
  map_one' := by simp
  map_mul' x y := by
    funext i
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl <;> simp

@[simp]
theorem blockPair_apply_zero (x : GeneralLinear (m 0 + 1) R × GeneralLinear (m 1 + 1) R) :
    blockPair R x 0 = x.1 := by
  simp [blockPair]

@[simp]
theorem blockPair_apply_one (x : GeneralLinear (m 0 + 1) R × GeneralLinear (m 1 + 1) R) :
    blockPair R x 1 = x.2 := by
  simp [blockPair]

/-- Every Levi element of the two blocks is the pair of its blocks. -/
theorem blockPair_eta (L : ∀ i : Fin 2, GeneralLinear (m i + 1) R) :
    blockPair R (L 0, L 1) = L := by
  funext i
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl <;> simp

end Algebra

section TwoBlocks

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]

/-- `det diag(u, w) = det u * det w`. -/
theorem determinant_leviEmbedding_blockPair (u : GeneralLinear (m 0 + 1) R)
    (w : GeneralLinear (m 1 + 1) R) :
    GeneralLinear.determinant ((succBlockShape m h).leviEmbedding R (blockPair R (u, w))) =
      GeneralLinear.determinant u * GeneralLinear.determinant w := by
  rw [Langlands.Parabolic.FlattenedModulusCalculation.determinant_leviEmbedding]
  exact (Fin.prod_univ_two _).trans (by simp)

/-- `diag(u, w)` lies in `H = N_(t_1,t_2)` when both blocks are upper unipotent. -/
theorem leviEmbedding_blockPair_mem_blockUnipotent {u : GeneralLinear (m 0 + 1) R}
    {w : GeneralLinear (m 1 + 1) R} (hu : u ∈ upperUnipotent (m 0 + 1) R)
    (hw : w ∈ upperUnipotent (m 1 + 1) R) :
    (succBlockShape m h).leviEmbedding R (blockPair R (u, w)) ∈
      TwoBlockUnipotentQuotient.blockUnipotent h R := by
  refine ⟨fun i => ⟨blockPair R (u, w) i, ?_⟩, rfl⟩
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · simpa using hu
  · simpa using hw

/-! ### The first-block embedding -/

/-- The first-block embedding `u ↦ diag(u, 1_b)` of JPSS (4.6), (6), through the published
Levi embedding of `succBlockShape m h`. -/
def firstBlockEmbedding : GeneralLinear (m 0 + 1) R →* GeneralLinear (t + 1) R :=
  ((succBlockShape m h).leviEmbedding R).comp ((blockPair R).comp (MonoidHom.inl _ _))

/-- Representative formula: `firstBlockEmbedding u = diag(u, 1)`. -/
theorem firstBlockEmbedding_apply (u : GeneralLinear (m 0 + 1) R) :
    firstBlockEmbedding h R u = (succBlockShape m h).leviEmbedding R (blockPair R (u, 1)) :=
  rfl

@[simp]
theorem firstBlockEmbedding_index_zero_zero (u : GeneralLinear (m 0 + 1) R)
    (a b : Fin (m 0 + 1)) :
    firstBlockEmbedding h R u ((succBlockShape m h).index 0 a)
      ((succBlockShape m h).index 0 b) = u a b := by
  rw [firstBlockEmbedding_apply, BlockShape.leviEmbedding_apply_same]
  simp

@[simp]
theorem firstBlockEmbedding_index_zero_one (u : GeneralLinear (m 0 + 1) R)
    (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)) :
    firstBlockEmbedding h R u ((succBlockShape m h).index 0 a)
      ((succBlockShape m h).index 1 b) = 0 :=
  leviEmbedding_index_zero_one h _ a b

@[simp]
theorem firstBlockEmbedding_index_one_zero (u : GeneralLinear (m 0 + 1) R)
    (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)) :
    firstBlockEmbedding h R u ((succBlockShape m h).index 1 a)
      ((succBlockShape m h).index 0 b) = 0 :=
  leviEmbedding_index_one_zero h _ a b

@[simp]
theorem firstBlockEmbedding_index_one_one (u : GeneralLinear (m 0 + 1) R)
    (a b : Fin (m 1 + 1)) :
    firstBlockEmbedding h R u ((succBlockShape m h).index 1 a)
      ((succBlockShape m h).index 1 b) = if a = b then 1 else 0 := by
  rw [firstBlockEmbedding_apply, BlockShape.leviEmbedding_apply_same]
  simp [Matrix.one_apply]

theorem firstBlockEmbedding_injective : Function.Injective (firstBlockEmbedding h R) := by
  intro u u' hu
  have hL := congrFun ((succBlockShape m h).leviEmbedding_injective R hu) 0
  simpa using hL

/-- `det diag(u, 1) = det u`. -/
@[simp]
theorem determinant_firstBlockEmbedding (u : GeneralLinear (m 0 + 1) R) :
    GeneralLinear.determinant (firstBlockEmbedding h R u) = GeneralLinear.determinant u := by
  rw [firstBlockEmbedding_apply, determinant_leviEmbedding_blockPair, map_one, mul_one]

/-- Embedding an upper-unipotent first block gives an element of `H = N_(t_1,t_2)`. -/
theorem firstBlockEmbedding_mem_blockUnipotent {u : GeneralLinear (m 0 + 1) R}
    (hu : u ∈ upperUnipotent (m 0 + 1) R) :
    firstBlockEmbedding h R u ∈ TwoBlockUnipotentQuotient.blockUnipotent h R :=
  leviEmbedding_blockPair_mem_blockUnipotent h R hu (upperUnipotent (m 1 + 1) R).one_mem

/-- The block identity `diag(v, 1) diag(u, w) = diag(1, w) diag(v u, 1)`. -/
theorem firstBlockEmbedding_mul_leviEmbedding_blockPair (v u : GeneralLinear (m 0 + 1) R)
    (w : GeneralLinear (m 1 + 1) R) :
    firstBlockEmbedding h R v * (succBlockShape m h).leviEmbedding R (blockPair R (u, w)) =
      (succBlockShape m h).leviEmbedding R (blockPair R (1, w)) *
        firstBlockEmbedding h R (v * u) := by
  have e1 : blockPair R (v, 1) * blockPair R (u, w) = blockPair R (v * u, w) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have e2 : blockPair R (1, w) * blockPair R (v * u, 1) = blockPair R (v * u, w) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  rw [firstBlockEmbedding_apply, firstBlockEmbedding_apply,
    ← map_mul ((succBlockShape m h).leviEmbedding R),
    ← map_mul ((succBlockShape m h).leviEmbedding R), e1, e2]

/-! ### Matrices with vanishing off-diagonal blocks -/

/-- A matrix whose lower-left block vanishes lies in the published block parabolic. -/
theorem mem_parabolic_of_index_one_zero (g : GeneralLinear (t + 1) R)
    (h10 : ∀ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)),
      g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0) :
    g ∈ (succBlockShape m h).parabolic R := by
  rw [BlockShape.mem_parabolic_iff]
  intro i j a b hji
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · simp at hji
  · simp at hji
  · exact h10 a b
  · simp at hji

/-- A matrix whose two off-diagonal blocks vanish is the Levi embedding of its diagonal
blocks. -/
theorem leviEmbedding_leviProjection_of_blocks (g : GeneralLinear (t + 1) R)
    (hg : g ∈ (succBlockShape m h).parabolic R)
    (h01 : ∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
      g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0)
    (h10 : ∀ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)),
      g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0) :
    (succBlockShape m h).leviEmbedding R ((succBlockShape m h).leviProjection R ⟨g, hg⟩) = g := by
  apply ext_index h
  · intro a b
    rw [BlockShape.leviEmbedding_apply_same]
    rfl
  · intro a b
    rw [leviEmbedding_index_zero_one, h01]
  · intro a b
    rw [leviEmbedding_index_one_zero, h10]
  · intro a b
    rw [BlockShape.leviEmbedding_apply_same]
    rfl

/-- For a matrix with vanishing off-diagonal blocks and upper-unipotent second block, the
determinant of the first diagonal block is the determinant of the matrix. -/
theorem det_firstBlock_eq (g : GeneralLinear (t + 1) R)
    (h01 : ∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
      g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0)
    (h10 : ∀ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)),
      g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0)
    (hlow : ∀ (a b : Fin (m 1 + 1)), b < a →
      g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) = 0)
    (hdiag : ∀ a : Fin (m 1 + 1),
      g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 a) = 1) :
    ((g : Matrix (Fin (t + 1)) (Fin (t + 1)) R).submatrix ((succBlockShape m h).index 0)
      ((succBlockShape m h).index 0)).det = (GeneralLinear.determinant g : R) := by
  have hg := mem_parabolic_of_index_one_zero h R g h10
  set L := (succBlockShape m h).leviProjection R ⟨g, hg⟩ with hLdef
  have hL1 : L 1 ∈ upperUnipotent (m 1 + 1) R := ⟨fun a b hab => hlow a b hab, hdiag⟩
  have hsub : (g : Matrix (Fin (t + 1)) (Fin (t + 1)) R).submatrix ((succBlockShape m h).index 0)
      ((succBlockShape m h).index 0) = (L 0 : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) R) := rfl
  have hgL : (succBlockShape m h).leviEmbedding R (blockPair R (L 0, L 1)) = g := by
    rw [blockPair_eta]
    exact leviEmbedding_leviProjection_of_blocks h R g hg h01 h10
  rw [hsub, ← hgL, determinant_leviEmbedding_blockPair,
    TwoBlockUnipotentQuotient.determinant_eq_one_of_mem_upperUnipotent R hL1, mul_one,
    Matrix.GeneralLinearGroup.val_det_apply]

end TwoBlocks

section AlgebraTopology

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (R : Type uR) [CommRing R] [TopologicalSpace R]

theorem continuous_blockPair : Continuous (blockPair (m := m) R) := by
  apply continuous_pi
  intro i
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · simpa using continuous_fst
  · simpa using continuous_snd

theorem continuous_firstBlockEmbedding : Continuous (firstBlockEmbedding h R) :=
  ((succBlockShape m h).leviEmbeddingContinuous R).continuous.comp
    ((continuous_blockPair R).comp (continuous_id.prodMk continuous_const))

end AlgebraTopology

/-! ### The last row and the fiber map -/

section Field

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (K : Type uR) [Field K]

/-- The last coordinate lies in the second block, since `b ≥ 1`. -/
theorem last_eq_index_one :
    Fin.last t = (succBlockShape m h).index 1 (Fin.last (m 1)) := by
  apply Fin.ext
  rw [val_index_one h, Fin.val_last, Fin.val_last]
  have := blockRanks_add h
  omega

/-- `lastRow (diag(u, 1) g) = lastRow g`. -/
@[simp]
theorem lastRow_firstBlockEmbedding_mul (u : GeneralLinear (m 0 + 1) K)
    (g : GeneralLinear (t + 1) K) :
    lastRow (firstBlockEmbedding h K u * g) = lastRow g := by
  funext j
  simp only [lastRow]
  rw [mul_apply_index h, last_eq_index_one h]
  have h0 : ∀ c : Fin (m 0 + 1),
      firstBlockEmbedding h K u ((succBlockShape m h).index 1 (Fin.last (m 1)))
        ((succBlockShape m h).index 0 c) * g ((succBlockShape m h).index 0 c) j = 0 :=
    fun c => by rw [firstBlockEmbedding_index_one_zero, zero_mul]
  have h1 : ∀ c : Fin (m 1 + 1),
      firstBlockEmbedding h K u ((succBlockShape m h).index 1 (Fin.last (m 1)))
        ((succBlockShape m h).index 1 c) * g ((succBlockShape m h).index 1 c) j =
      if Fin.last (m 1) = c then g ((succBlockShape m h).index 1 c) j else 0 :=
    fun c => by rw [firstBlockEmbedding_index_one_one, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_congr rfl fun c _ => h0 c, Finset.sum_congr rfl fun c _ => h1 c,
    Finset.sum_const_zero, zero_add, Fintype.sum_ite_eq]

/-- The fiber map `([u], g) ↦ [diag(u, 1) g]_H` from the small quotient
`N_(m 0 + 1) \ GL_(m 0 + 1)` to `H \ GL_(t+1)`, by actual quotient descent: left
multiplication of `u` by `n ∈ N_(m 0 + 1)` multiplies `diag(u, 1) g` on the left by
`diag(n, 1) ∈ H`. -/
def fiberPoint (q : LeftUnipotentQuotient (m 0) K) (g : GeneralLinear (t + 1) K) :
    TwoBlockUnipotentQuotient.BlockQuotient h K :=
  descend _
    (fun u => (Quotient.mk _ (firstBlockEmbedding h K u * g) :
      TwoBlockUnipotentQuotient.BlockQuotient h K))
    (fun n u => by
      rw [map_mul, mul_assoc]
      exact TwoBlockUnipotentQuotient.mk_mul_of_mem _
        (firstBlockEmbedding_mem_blockUnipotent h K n.property) _)
    q

/-- Representative formula: `fiberPoint [u] g = [diag(u, 1) g]_H`. -/
@[simp]
theorem fiberPoint_mk (u : GeneralLinear (m 0 + 1) K) (g : GeneralLinear (t + 1) K) :
    fiberPoint h K (Quotient.mk _ u) g = Quotient.mk _ (firstBlockEmbedding h K u * g) :=
  rfl

end Field

/-! ### The norm-one first block and the mixed subgroup -/

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The norm-one subgroup `GL_n^0 = {u | |det u| = 1}`, the kernel of the published
determinant norm for the canonical realization. -/
abbrev normOneSubgroup (n : ℕ) : Subgroup (GeneralLinear n F.Carrier) :=
  (F.canonicalTopologicalData.determinantNorm n).ker

theorem mem_normOneSubgroup_iff {n : ℕ} (u : GeneralLinear n F.Carrier) :
    u ∈ normOneSubgroup F n ↔ F.canonicalTopologicalData.determinantNorm n u = 1 :=
  Iff.rfl

/-- Norm one is the condition `|det u| = 1` for the normalized absolute value. -/
theorem mem_normOneSubgroup_iff_normalizedAbs {n : ℕ} (u : GeneralLinear n F.Carrier) :
    u ∈ normOneSubgroup F n ↔
      F.canonicalTopologicalData.normalizedAbs (u : Matrix (Fin n) (Fin n) F.Carrier).det = 1 := by
  rw [MonoidHom.mem_ker, ← Units.val_inj, ← NNReal.coe_inj,
    PadicField.TopologicalData.determinantNorm_coe, Units.val_one, NNReal.coe_one,
    Matrix.GeneralLinearGroup.val_det_apply]

/-- A norm-one matrix has determinant of order zero. -/
theorem ord_determinant_eq_zero {n : ℕ} {u : GeneralLinear n F.Carrier}
    (hu : u ∈ normOneSubgroup F n) :
    F.canonicalTopologicalData.ord (GeneralLinear.determinant u : F.Carrier) = 0 := by
  rw [PadicField.TopologicalData.ord_eq_zero_iff_normalizedAbs,
    Matrix.GeneralLinearGroup.val_det_apply]
  exact (mem_normOneSubgroup_iff_normalizedAbs F u).mp hu

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The embedding `(u, n) ↦ diag(u, n)` of `GL_(m 0 + 1)^0 × N_(m 1 + 1)` into
`GL_(t+1)`, through the published Levi embedding of `succBlockShape m h`. -/
def mixedEmbedding :
    normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier →*
      GeneralLinear (t + 1) F.Carrier :=
  ((succBlockShape m h).leviEmbedding F.Carrier).comp ((blockPair F.Carrier).comp
    (MonoidHom.prodMap (normOneSubgroup F (m 0 + 1)).subtype
      (upperUnipotent (m 1 + 1) F.Carrier).subtype))

theorem mixedEmbedding_apply
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) :
    mixedEmbedding F h x =
      (succBlockShape m h).leviEmbedding F.Carrier (blockPair F.Carrier (x.1.val, x.2.val)) :=
  rfl

@[simp]
theorem mixedEmbedding_index_zero_zero
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier)
    (a b : Fin (m 0 + 1)) :
    mixedEmbedding F h x ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 0 b) =
      x.1.val a b := by
  rw [mixedEmbedding_apply, BlockShape.leviEmbedding_apply_same]
  simp

@[simp]
theorem mixedEmbedding_index_zero_one
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier)
    (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)) :
    mixedEmbedding F h x ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) =
      0 :=
  leviEmbedding_index_zero_one h _ a b

@[simp]
theorem mixedEmbedding_index_one_zero
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier)
    (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)) :
    mixedEmbedding F h x ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) =
      0 :=
  leviEmbedding_index_one_zero h _ a b

@[simp]
theorem mixedEmbedding_index_one_one
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier)
    (a b : Fin (m 1 + 1)) :
    mixedEmbedding F h x ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) =
      x.2.val a b := by
  rw [mixedEmbedding_apply, BlockShape.leviEmbedding_apply_same]
  simp

theorem mixedEmbedding_injective : Function.Injective (mixedEmbedding F h) := by
  intro x y hxy
  have hL := (succBlockShape m h).leviEmbedding_injective F.Carrier hxy
  have h0 : blockPair F.Carrier (x.1.val, x.2.val) 0 = blockPair F.Carrier (y.1.val, y.2.val) 0 :=
    congrFun hL 0
  have h1 : blockPair F.Carrier (x.1.val, x.2.val) 1 = blockPair F.Carrier (y.1.val, y.2.val) 1 :=
    congrFun hL 1
  simp only [blockPair_apply_zero, blockPair_apply_one] at h0 h1
  exact Prod.ext (Subtype.ext h0) (Subtype.ext h1)

/-- `det diag(u, n) = det u`. -/
@[simp]
theorem determinant_mixedEmbedding
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) :
    GeneralLinear.determinant (mixedEmbedding F h x) = GeneralLinear.determinant x.1.val := by
  rw [mixedEmbedding_apply, determinant_leviEmbedding_blockPair,
    TwoBlockUnipotentQuotient.determinant_eq_one_of_mem_upperUnipotent F.Carrier x.2.property,
    mul_one]

/-- The subgroup `L = G_(t_1)^0 N_(t_1,t_2) = diag(GL_(m 0 + 1)^0, N_(m 1 + 1))` of JPSS
(4.6), (6): the actual image of `mixedEmbedding`. -/
def mixedSubgroup : Subgroup (GeneralLinear (t + 1) F.Carrier) :=
  (mixedEmbedding F h).range

theorem mixedEmbedding_mem
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) :
    mixedEmbedding F h x ∈ mixedSubgroup F h :=
  ⟨x, rfl⟩

/-- Intrinsic block-entry description of `L`: both off-diagonal blocks vanish, the first
diagonal block has determinant of normalized absolute value one (so it is invertible), and
the second diagonal block is upper unipotent. -/
theorem mem_mixedSubgroup_iff (g : GeneralLinear (t + 1) F.Carrier) :
    g ∈ mixedSubgroup F h ↔
      (∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
        g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0) ∧
      (∀ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)),
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0) ∧
      F.canonicalTopologicalData.normalizedAbs
        ((g : Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier).submatrix
          ((succBlockShape m h).index 0) ((succBlockShape m h).index 0)).det = 1 ∧
      (∀ (a b : Fin (m 1 + 1)), b < a →
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) = 0) ∧
      (∀ a : Fin (m 1 + 1),
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 a) = 1) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨mixedEmbedding_index_zero_one F h x, mixedEmbedding_index_one_zero F h x, ?_,
      fun a b hab => ?_, fun a => ?_⟩
    · have hsub : ((mixedEmbedding F h x : Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier).submatrix
          ((succBlockShape m h).index 0) ((succBlockShape m h).index 0)) =
          (x.1.val : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier) := by
        ext a b
        exact mixedEmbedding_index_zero_zero F h x a b
      rw [hsub]
      exact (mem_normOneSubgroup_iff_normalizedAbs F x.1.val).mp x.1.property
    · rw [mixedEmbedding_index_one_one]
      exact UpperUnipotent.entry_eq_zero x.2 hab
    · rw [mixedEmbedding_index_one_one]
      exact UpperUnipotent.entry_diag x.2 a
  · rintro ⟨h01, h10, hdet, hlow, hdiag⟩
    have hg := mem_parabolic_of_index_one_zero h F.Carrier g h10
    set L := (succBlockShape m h).leviProjection F.Carrier ⟨g, hg⟩ with hLdef
    have hL0 : L 0 ∈ normOneSubgroup F (m 0 + 1) := by
      rw [mem_normOneSubgroup_iff_normalizedAbs]
      exact hdet
    have hL1 : L 1 ∈ upperUnipotent (m 1 + 1) F.Carrier :=
      ⟨fun a b hab => hlow a b hab, hdiag⟩
    refine ⟨(⟨L 0, hL0⟩, ⟨L 1, hL1⟩), ?_⟩
    change (succBlockShape m h).leviEmbedding F.Carrier (blockPair F.Carrier (L 0, L 1)) = g
    rw [blockPair_eta]
    exact leviEmbedding_leviProjection_of_blocks h F.Carrier g hg h01 h10

/-- Equivalent intrinsic description with the determinant norm of the whole matrix: this
form exhibits `L` as an intersection of closed conditions. -/
theorem mem_mixedSubgroup_iff_determinantNorm (g : GeneralLinear (t + 1) F.Carrier) :
    g ∈ mixedSubgroup F h ↔
      (∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
        g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0) ∧
      (∀ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)),
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0) ∧
      g ∈ normOneSubgroup F (t + 1) ∧
      (∀ (a b : Fin (m 1 + 1)), b < a →
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) = 0) ∧
      (∀ a : Fin (m 1 + 1),
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 a) = 1) := by
  rw [mem_mixedSubgroup_iff]
  constructor
  · rintro ⟨h01, h10, hdet, hlow, hdiag⟩
    refine ⟨h01, h10, ?_, hlow, hdiag⟩
    rw [mem_normOneSubgroup_iff_normalizedAbs, ← Matrix.GeneralLinearGroup.val_det_apply,
      ← det_firstBlock_eq h F.Carrier g h01 h10 hlow hdiag]
    exact hdet
  · rintro ⟨h01, h10, hdet, hlow, hdiag⟩
    refine ⟨h01, h10, ?_, hlow, hdiag⟩
    rw [det_firstBlock_eq h F.Carrier g h01 h10 hlow hdiag,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact (mem_normOneSubgroup_iff_normalizedAbs F g).mp hdet

/-- The first diagonal block of an element of `L` is invertible. -/
theorem det_firstBlock_ne_zero {g : GeneralLinear (t + 1) F.Carrier}
    (hg : g ∈ mixedSubgroup F h) :
    ((g : Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier).submatrix
      ((succBlockShape m h).index 0) ((succBlockShape m h).index 0)).det ≠ 0 := by
  intro h0
  have hdet := ((mem_mixedSubgroup_iff F h g).mp hg).2.2.1
  rw [h0, PadicField.TopologicalData.normalizedAbs_zero] at hdet
  exact zero_ne_one hdet

/-- `L ≤ ker |det|`. -/
theorem mixedSubgroup_le_normOneSubgroup : mixedSubgroup F h ≤ normOneSubgroup F (t + 1) := by
  rintro _ ⟨x, rfl⟩
  change F.canonicalTopologicalData.normalizedAbsUnits
    (GeneralLinear.determinant (mixedEmbedding F h x)) = 1
  rw [determinant_mixedEmbedding]
  exact x.1.property

/-- `H = N_(t_1,t_2) ≤ L`: the first block of `H` is upper unipotent, hence of norm one. -/
theorem blockUnipotent_le_mixedSubgroup :
    TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier ≤ mixedSubgroup F h := by
  rintro _ ⟨n, rfl⟩
  refine ⟨(⟨(n 0).val, determinantNorm_eq_one_of_mem_upperUnipotent F
    F.canonicalTopologicalData (n 0).property⟩, n 1), ?_⟩
  rw [mixedEmbedding_apply, TwoBlockUnipotentQuotient.blockEmbedding_apply]
  exact congrArg _ (blockPair_eta F.Carrier fun i => (n i).val)

theorem mixedSubgroup_le_parabolic :
    mixedSubgroup F h ≤ (succBlockShape m h).parabolic F.Carrier := fun g hg =>
  mem_parabolic_of_index_one_zero h F.Carrier g ((mem_mixedSubgroup_iff F h g).mp hg).2.1

/-- The diagonal blocks of an element of `L`, by the published Levi projection. -/
def mixedCoordinates (g : mixedSubgroup F h) :
    normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier :=
  (⟨(succBlockShape m h).leviProjection F.Carrier
      ⟨g.val, mixedSubgroup_le_parabolic F h g.property⟩ 0, by
      rw [mem_normOneSubgroup_iff_normalizedAbs]
      exact ((mem_mixedSubgroup_iff F h g.val).mp g.property).2.2.1⟩,
    ⟨(succBlockShape m h).leviProjection F.Carrier
      ⟨g.val, mixedSubgroup_le_parabolic F h g.property⟩ 1,
      ⟨fun a b hab => ((mem_mixedSubgroup_iff F h g.val).mp g.property).2.2.2.1 a b hab,
        ((mem_mixedSubgroup_iff F h g.val).mp g.property).2.2.2.2⟩⟩)

theorem mixedCoordinates_mixedEmbedding
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) :
    mixedCoordinates F h ⟨mixedEmbedding F h x, mixedEmbedding_mem F h x⟩ = x := by
  refine Prod.ext (Subtype.ext (Matrix.GeneralLinearGroup.ext fun a b => ?_))
    (Subtype.ext (Matrix.GeneralLinearGroup.ext fun a b => ?_))
  · change (succBlockShape m h).leviProjection F.Carrier
      ⟨mixedEmbedding F h x, mixedSubgroup_le_parabolic F h (mixedEmbedding_mem F h x)⟩ 0 a b = _
    rw [BlockShape.leviProjection_apply]
    exact mixedEmbedding_index_zero_zero F h x a b
  · change (succBlockShape m h).leviProjection F.Carrier
      ⟨mixedEmbedding F h x, mixedSubgroup_le_parabolic F h (mixedEmbedding_mem F h x)⟩ 1 a b = _
    rw [BlockShape.leviProjection_apply]
    exact mixedEmbedding_index_one_one F h x a b

theorem mixedEmbedding_mixedCoordinates (g : mixedSubgroup F h) :
    mixedEmbedding F h (mixedCoordinates F h g) = g.val := by
  rw [mixedEmbedding_apply]
  change (succBlockShape m h).leviEmbedding F.Carrier
    (blockPair F.Carrier (((succBlockShape m h).leviProjection F.Carrier
      ⟨g.val, mixedSubgroup_le_parabolic F h g.property⟩ 0),
      ((succBlockShape m h).leviProjection F.Carrier
      ⟨g.val, mixedSubgroup_le_parabolic F h g.property⟩ 1))) = g.val
  rw [blockPair_eta]
  exact leviEmbedding_leviProjection_of_blocks h F.Carrier g.val _
    ((mem_mixedSubgroup_iff F h g.val).mp g.property).1
    ((mem_mixedSubgroup_iff F h g.val).mp g.property).2.1

/-- The multiplicative equivalence of `GL_(m 0 + 1)^0 × N_(m 1 + 1)` with `L`; the inverse
extracts the diagonal blocks. -/
def mixedSubgroupEquiv :
    normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier ≃* mixedSubgroup F h where
  toFun x := ⟨mixedEmbedding F h x, mixedEmbedding_mem F h x⟩
  invFun := mixedCoordinates F h
  left_inv := mixedCoordinates_mixedEmbedding F h
  right_inv g := Subtype.ext (mixedEmbedding_mixedCoordinates F h g)
  map_mul' x y := Subtype.ext (map_mul (mixedEmbedding F h) x y)

@[simp]
theorem mixedSubgroupEquiv_apply_val
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) :
    (mixedSubgroupEquiv F h x).val = mixedEmbedding F h x :=
  rfl

/-- Inverse formula, entrywise on the first block. -/
theorem mixedSubgroupEquiv_symm_apply_fst (g : mixedSubgroup F h) (a b : Fin (m 0 + 1)) :
    ((mixedSubgroupEquiv F h).symm g).1.val a b =
      g.val ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 0 b) :=
  rfl

/-- Inverse formula, entrywise on the second block. -/
theorem mixedSubgroupEquiv_symm_apply_snd (g : mixedSubgroup F h) (a b : Fin (m 1 + 1)) :
    ((mixedSubgroupEquiv F h).symm g).2.val a b =
      g.val ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) :=
  rfl

/-- The equivalence `GL_(m 0 + 1)^0 × N_(m 1 + 1) ≃ L` is a homeomorphism for the canonical
p-adic topology. -/
def mixedSubgroupHomeomorph :
    letI := F.canonicalTopologicalData.topology
    normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier ≃ₜ* mixedSubgroup F h :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  { toMulEquiv := mixedSubgroupEquiv F h
    continuous_toFun :=
      (((succBlockShape m h).leviEmbeddingContinuous F.Carrier).continuous.comp
        ((continuous_blockPair F.Carrier).comp
          ((continuous_subtype_val.comp continuous_fst).prodMk
            (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
    continuous_invFun := by
      have hP : Continuous (fun g : mixedSubgroup F h =>
          (succBlockShape m h).leviProjection F.Carrier
            ⟨g.val, mixedSubgroup_le_parabolic F h g.property⟩) :=
        ((succBlockShape m h).leviProjectionContinuous F.Carrier).continuous.comp
          (continuous_subtype_val.subtype_mk _)
      exact (((continuous_apply 0).comp hP).subtype_mk _).prodMk
        (((continuous_apply 1).comp hP).subtype_mk _) }

theorem mixedSubgroupHomeomorph_toMulEquiv :
    letI := F.canonicalTopologicalData.topology
    (mixedSubgroupHomeomorph F h).toMulEquiv = mixedSubgroupEquiv F h :=
  rfl

/-- `L` is closed: it is cut out by the vanishing of the off-diagonal blocks, the
upper-unipotent conditions on the second block, and the open, hence closed, kernel of
`|det|`. -/
theorem isClosed_mixedSubgroup :
    letI := F.canonicalTopologicalData.topology
    IsClosed (mixedSubgroup F h : Set (GeneralLinear (t + 1) F.Carrier)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (t + 1)
  have he : (mixedSubgroup F h : Set (GeneralLinear (t + 1) F.Carrier)) =
      (⋂ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)), {g : GeneralLinear (t + 1) F.Carrier |
        g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0}) ∩
      ((⋂ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)), {g : GeneralLinear (t + 1) F.Carrier |
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0}) ∩
      ((normOneSubgroup F (t + 1) : Set (GeneralLinear (t + 1) F.Carrier)) ∩
      ((⋂ (a : Fin (m 1 + 1)) (b : Fin (m 1 + 1)) (_ : b < a),
        {g : GeneralLinear (t + 1) F.Carrier |
          g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) = 0}) ∩
      (⋂ (a : Fin (m 1 + 1)), {g : GeneralLinear (t + 1) F.Carrier |
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 a) = 1})))) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_mixedSubgroup_iff_determinantNorm F h g
  have hentry : ∀ (k l : Fin (t + 1)) (c : F.Carrier),
      IsClosed {g : GeneralLinear (t + 1) F.Carrier | g k l = c} := fun k l c =>
    isClosed_eq (GeneralLinear.entry (R := F.Carrier) k l).continuous continuous_const
  rw [he]
  exact (isClosed_iInter fun a => isClosed_iInter fun b => hentry _ _ _).inter
    ((isClosed_iInter fun a => isClosed_iInter fun b => hentry _ _ _).inter
      ((Subgroup.isClosed_of_isOpen _ (T.isOpen_ker_determinantNorm (t + 1))).inter
        ((isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
          hentry _ _ _).inter
          (isClosed_iInter fun a => hentry _ _ _))))

/-! ### The mixed quotient `L \ GL_(t+1)` -/

/-- The actual left quotient `L \ GL_(t+1)`. -/
abbrev MixedQuotient := LeftQuotient (mixedSubgroup F h)

/-- The canonical projection `H \ G → L \ G`, `[g]_H ↦ [g]_L`, by quotient descent through
`H ≤ L`. -/
def projection : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → MixedQuotient F h :=
  descend _ (fun g => (Quotient.mk _ g : MixedQuotient F h))
    (fun u g => TwoBlockUnipotentQuotient.mk_mul_of_mem _
      (blockUnipotent_le_mixedSubgroup F h u.property) g)

@[simp]
theorem projection_mk (g : GeneralLinear (t + 1) F.Carrier) :
    projection F h (Quotient.mk _ g) = Quotient.mk _ g :=
  rfl

theorem projection_surjective : Function.Surjective (projection F h) := by
  intro q
  induction q using Quotient.inductionOn with
  | h g => exact ⟨Quotient.mk _ g, rfl⟩

/-- The projection `H \ G → L \ G` is continuous for the quotient topologies. -/
theorem continuous_projection :
    letI := F.canonicalTopologicalData.topology
    Continuous (projection F h) := by
  let := F.canonicalTopologicalData.topology
  exact Continuous.quotient_lift continuous_quotient_mk' _

/-- The projection intertwines right translation on the two quotients. -/
theorem projection_rightTranslate :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (g : GeneralLinear (t + 1) F.Carrier)
      (q : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier),
      projection F h (rightTranslate _ g q) = rightTranslate _ g (projection F h q) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro g q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- The mixed quotient is Hausdorff for the canonical p-adic topology. -/
theorem t2Space_mixedQuotient :
    letI := F.canonicalTopologicalData.topology
    T2Space (MixedQuotient F h) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  exact leftQuotient_t2Space _ (isClosed_mixedSubgroup F h)

/-- The quotient determinant order `[g]_L ↦ ord(det g)`; it is well defined because every
element of `L` has determinant of order zero. -/
def determinantOrder : MixedQuotient F h → ℤ :=
  descend _
    (fun g => F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier))
    (fun l g => by
      rw [map_mul, Units.val_mul,
        F.canonicalTopologicalData.ord_mul (GeneralLinear.determinant l.val).ne_zero
          (GeneralLinear.determinant g).ne_zero,
        ord_determinant_eq_zero F (mixedSubgroup_le_normOneSubgroup F h l.property), zero_add])

@[simp]
theorem determinantOrder_mk (g : GeneralLinear (t + 1) F.Carrier) :
    determinantOrder F h (Quotient.mk _ g) =
      F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) :=
  rfl

/-- The determinant order is continuous into the discrete integers. -/
theorem continuous_determinantOrder :
    letI := F.canonicalTopologicalData.topology
    Continuous (determinantOrder F h) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  exact Continuous.quotient_lift
    ((continuous_ord_units T).comp (T.generalLinearDeterminant (t + 1)).continuous) _

/-- The determinant slice `L \ G^k = {q | ord(det q) = k}` of the mixed quotient. The
outer domain of JPSS (4.6), (6) is the slice `k = 0`. -/
def determinantSlice (k : ℤ) : Set (MixedQuotient F h) :=
  {q | determinantOrder F h q = k}

theorem mem_determinantSlice {k : ℤ} {q : MixedQuotient F h} :
    q ∈ determinantSlice F h k ↔ determinantOrder F h q = k :=
  Iff.rfl

theorem mk_mem_determinantSlice {k : ℤ} {g : GeneralLinear (t + 1) F.Carrier} :
    (Quotient.mk _ g : MixedQuotient F h) ∈ determinantSlice F h k ↔
      F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) = k :=
  Iff.rfl

theorem isClopen_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    IsClopen (determinantSlice F h k) := by
  let := F.canonicalTopologicalData.topology
  exact (isClopen_discrete ({k} : Set ℤ)).preimage (continuous_determinantOrder F h)

/-- Every slice is measurable for any Borel structure on the mixed quotient. -/
theorem measurableSet_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace (MixedQuotient F h)] [BorelSpace (MixedQuotient F h)],
      MeasurableSet (determinantSlice F h k) := by
  let := F.canonicalTopologicalData.topology
  intro _ _
  exact (isClopen_determinantSlice F h k).isOpen.measurableSet

/-- The determinant order of `[g]_L` is that of `[g]_H`. -/
@[simp]
theorem determinantOrder_projection_mk (g : GeneralLinear (t + 1) F.Carrier) :
    determinantOrder F h (projection F h (Quotient.mk _ g)) =
      F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) :=
  rfl

/-- Pullback identity: the preimage of `L \ G^k` in `H \ G` is the published slice
`H \ G^k`. -/
theorem projection_preimage_determinantSlice (k : ℤ) :
    projection F h ⁻¹' determinantSlice F h k =
      TwoBlockUnipotentQuotient.determinantSlice F h k := by
  ext q
  induction q using Quotient.inductionOn with
  | h g => rfl

/-- Right translation by `g` shifts the determinant order by `ord(det g)`. -/
theorem determinantOrder_rightTranslate :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (g : GeneralLinear (t + 1) F.Carrier) (q : MixedQuotient F h),
      determinantOrder F h (rightTranslate _ g q) =
        determinantOrder F h q +
          F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro g q
  induction q using Quotient.inductionOn with
  | h x =>
    rw [rightTranslate_mk, determinantOrder_mk, determinantOrder_mk, map_mul, Units.val_mul,
      F.canonicalTopologicalData.ord_mul (GeneralLinear.determinant x).ne_zero
        (GeneralLinear.determinant g).ne_zero]

/-- Right-translation shift formula for the slices. -/
theorem rightTranslate_mem_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (g : GeneralLinear (t + 1) F.Carrier) (q : MixedQuotient F h),
      rightTranslate _ g q ∈ determinantSlice F h k ↔
        q ∈ determinantSlice F h
          (k - F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro g q
  rw [mem_determinantSlice, mem_determinantSlice, determinantOrder_rightTranslate F h g q,
    eq_sub_iff_add_eq]

/-! ### The fiber map from the small quotient -/

/-- The fiber map is jointly continuous in `(q, g)`. -/
theorem continuous_fiberPoint :
    letI := F.canonicalTopologicalData.topology
    Continuous (Function.uncurry (fiberPoint h F.Carrier)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let := T.generalLinearTopologicalGroup (t + 1)
  have hq : IsOpenQuotientMap (Prod.map (leftQuotientMap (upperUnipotent (m 0 + 1) F.Carrier))
      (id : GeneralLinear (t + 1) F.Carrier → GeneralLinear (t + 1) F.Carrier)) :=
    (leftQuotient_isOpenQuotientMap _).prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  have he : Function.uncurry (fiberPoint h F.Carrier) ∘
      Prod.map (leftQuotientMap (upperUnipotent (m 0 + 1) F.Carrier)) id =
      fun x : GeneralLinear (m 0 + 1) F.Carrier × GeneralLinear (t + 1) F.Carrier =>
        (Quotient.mk _ (firstBlockEmbedding h F.Carrier x.1 * x.2) :
          TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) :=
    rfl
  rw [he]
  exact continuous_quotient_mk'.comp
    (((continuous_firstBlockEmbedding h F.Carrier).comp continuous_fst).mul continuous_snd)

/-- Right translation of the base point translates the fiber point. -/
theorem fiberPoint_mul :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (q : LeftUnipotentQuotient (m 0) F.Carrier) (g g' : GeneralLinear (t + 1) F.Carrier),
      fiberPoint h F.Carrier q (g * g') = rightTranslate _ g' (fiberPoint h F.Carrier q g) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro q g g'
  induction q using Quotient.inductionOn with
  | h u => rw [fiberPoint_mk, fiberPoint_mk, rightTranslate_mk, mul_assoc]

/-- `fiberPoint q g` lies in the published slice `H \ G^k` exactly when
`ord(det q) + ord(det g) = k`. -/
theorem fiberPoint_mem_determinantSlice_iff (q : LeftUnipotentQuotient (m 0) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) (k : ℤ) :
    fiberPoint h F.Carrier q g ∈ TwoBlockUnipotentQuotient.determinantSlice F h k ↔
      RankinSelberg.determinantOrder F.canonicalTopologicalData (m 0) q +
        F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) = k := by
  induction q using Quotient.inductionOn with
  | h u =>
    rw [fiberPoint_mk, TwoBlockUnipotentQuotient.mk_mem_determinantSlice,
      RankinSelberg.determinantOrder_mk, map_mul, Units.val_mul,
      F.canonicalTopologicalData.ord_mul
        (GeneralLinear.determinant (firstBlockEmbedding h F.Carrier u)).ne_zero
        (GeneralLinear.determinant g).ne_zero,
      determinant_firstBlockEmbedding]

/-- Change of fiber: left multiplication of the base point by `diag(u, n) ∈ L` is right
multiplication of the small quotient by `u`. -/
theorem fiberPoint_mixedEmbedding_mul :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (m 0 + 1)
    ∀ (q : LeftUnipotentQuotient (m 0) F.Carrier) (u : normOneSubgroup F (m 0 + 1))
      (n : upperUnipotent (m 1 + 1) F.Carrier) (g : GeneralLinear (t + 1) F.Carrier),
      fiberPoint h F.Carrier q (mixedEmbedding F h (u, n) * g) =
        fiberPoint h F.Carrier (rightTranslate _ u.val q) g := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (m 0 + 1)
  intro q u n g
  induction q using Quotient.inductionOn with
  | h v =>
    rw [rightTranslate_mk, fiberPoint_mk, fiberPoint_mk, ← mul_assoc, mixedEmbedding_apply,
      firstBlockEmbedding_mul_leviEmbedding_blockPair, mul_assoc]
    exact TwoBlockUnipotentQuotient.mk_mul_of_mem _
      (leviEmbedding_blockPair_mem_blockUnipotent h F.Carrier
        (upperUnipotent (m 0 + 1) F.Carrier).one_mem n.property) _

/-! ### The inner slice integral and the first-block average -/

/-- Right translation of the small quotient by every norm-one `u` preserves the measure,
for the Borel structure of the quotient topology. -/
def NormOneRightInvariant (n : ℕ)
    (μA : letI := F.canonicalTopologicalData.topology
      letI := borel (LeftUnipotentQuotient n F.Carrier)
      Measure (LeftUnipotentQuotient n F.Carrier)) : Prop :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  ∀ u : normOneSubgroup F (n + 1), MeasurePreserving (rightTranslate _ u.val) μA μA

/-- A compatible quotient measure on the small full-unipotent quotient, in the sense of the
published `QuotientIntegration.IsCompatible`, is invariant under all right translations,
in particular under those by norm-one matrices. -/
theorem normOneRightInvariant_of_isCompatible (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ [MeasurableSpace (GeneralLinear (n + 1) F.Carrier)]
      [BorelSpace (GeneralLinear (n + 1) F.Carrier)]
      [MeasurableSpace (upperUnipotent (n + 1) F.Carrier)]
      [BorelSpace (upperUnipotent (n + 1) F.Carrier)]
      [MeasurableMul (upperUnipotent (n + 1) F.Carrier)]
      (μG : Measure (GeneralLinear (n + 1) F.Carrier))
      (μH : Measure (upperUnipotent (n + 1) F.Carrier)) [Measure.IsMulRightInvariant μH]
      (ν : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) μG μH ν → NormOneRightInvariant F n ν := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro _ _ _ _ _ μG μH _ ν hν u
  exact hν.right_invariant u.val

variable
  (μA : letI := F.canonicalTopologicalData.topology
    letI := borel (LeftUnipotentQuotient (m 0) F.Carrier)
    Measure (LeftUnipotentQuotient (m 0) F.Carrier))

/-- The inner integral of JPSS (4.6), (6): the total Bochner integral
`∫_{N_a \ GL_a^k} f(fiberPoint q g) dμA(q)` over the published small slice, for the supplied
measure on the Borel structure of the small quotient. -/
def fiberIntegral (k : ℤ) (f : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  letI := F.canonicalTopologicalData.topology
  letI := borel (LeftUnipotentQuotient (m 0) F.Carrier)
  ∫ q in RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k,
    f (fiberPoint h F.Carrier q g) ∂μA

theorem fiberIntegral_def (k : ℤ) (f : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := borel (LeftUnipotentQuotient (m 0) F.Carrier)
    fiberIntegral F h μA k f g =
      ∫ q in RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k,
        f (fiberPoint h F.Carrier q g) ∂μA :=
  rfl

/-- Left invariance under `diag(u, n) ∈ L`, without any integrability hypothesis: right
translation by `u` preserves `μA` and, since `ord(det u) = 0`, the small slice. -/
theorem fiberIntegral_mixedEmbedding_mul (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → ℂ)
    (u : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    fiberIntegral F h μA k f (mixedEmbedding F h (u, n) * g) = fiberIntegral F h μA k f g := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let := borel (LeftUnipotentQuotient (m 0) F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient (m 0) F.Carrier) := ⟨rfl⟩
  have hS : rightTranslate _ u.val ⁻¹' RankinSelberg.determinantSlice T (m 0) k =
      RankinSelberg.determinantSlice T (m 0) k := by
    ext q
    rw [Set.mem_preimage, RankinSelberg.rightTranslate_mem_determinantSlice T (m 0) k u.val q,
      ord_determinant_eq_zero F u.property, sub_zero]
  rw [fiberIntegral_def, fiberIntegral_def]
  simp_rw [fiberPoint_mixedEmbedding_mul F h _ u n g]
  have hI := (hμA u).setIntegral_preimage_emb (rightTranslate _ u.val).measurableEmbedding
    (fun q => f (fiberPoint h F.Carrier q g)) (RankinSelberg.determinantSlice T (m 0) k)
  rw [hS] at hI
  exact hI

/-- Left invariance under every element of `L`. -/
theorem fiberIntegral_mixedSubgroup_mul (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → ℂ) (l : mixedSubgroup F h)
    (g : GeneralLinear (t + 1) F.Carrier) :
    fiberIntegral F h μA k f (l.val * g) = fiberIntegral F h μA k f g := by
  obtain ⟨x, hx⟩ := l.property
  rw [← hx]
  exact fiberIntegral_mixedEmbedding_mul F h μA hμA k f x.1 x.2 g

/-- Right translation of the base point is right translation of the integrand. -/
theorem fiberIntegral_mul :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (k : ℤ) (f : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → ℂ)
      (g g' : GeneralLinear (t + 1) F.Carrier),
      fiberIntegral F h μA k f (g * g') =
        fiberIntegral F h μA k (fun r => f (rightTranslate _ g' r)) g := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro k f g g'
  simp only [fiberIntegral_def, fiberPoint_mul]

/-- The first-block average on the actual quotient `L \ GL_(t+1)`: the actual descent of
the left-`L`-invariant inner slice integral. No coset representative is chosen. -/
def firstBlockAverage (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → ℂ) : MixedQuotient F h → ℂ :=
  descend _ (fiberIntegral F h μA k f) (fiberIntegral_mixedSubgroup_mul F h μA hμA k f)

/-- Representative evaluation of the first-block average. -/
theorem firstBlockAverage_mk (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := borel (LeftUnipotentQuotient (m 0) F.Carrier)
    firstBlockAverage F h μA hμA k f (Quotient.mk _ g) =
      ∫ q in RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k,
        f (fiberPoint h F.Carrier q g) ∂μA :=
  rfl

/-- Right translation on `L \ GL_(t+1)` corresponds to right translation of the function on
`H \ GL_(t+1)`. -/
theorem firstBlockAverage_rightTranslate (hμA : NormOneRightInvariant F (m 0) μA) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (k : ℤ) (f : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → ℂ)
      (g : GeneralLinear (t + 1) F.Carrier) (q : MixedQuotient F h),
      firstBlockAverage F h μA hμA k f (rightTranslate _ g q) =
        firstBlockAverage F h μA hμA k (fun r => f (rightTranslate _ g r)) q := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro k f g q
  induction q using Quotient.inductionOn with
  | h x =>
    rw [rightTranslate_mk]
    exact fiberIntegral_mul F h μA k f x g

end Padic

end Langlands.RankinSelberg.TwoBlockFirstBlockQuotient
