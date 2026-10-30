import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.CuspidalSupport.BlockPermutationTensor
import Langlands.LocalField.Uniformizer

/-!
# Block scalars on Weyl transports of block tensors

Inverse Levi conjugation by a Levi-conjugating permutation sends a block scalar
of the target Levi to the block scalar of the source Levi with the entries
relabelled by the induced map of blocks. Consequently a block scalar acts on the
transport of an external block tensor of factors with scalar characters by the
product of the relabelled characters.
-/

noncomputable section

namespace Langlands.SegmentFullJacquet

open GeneralLinear Geometric CuspidalSupport

universe uF uV

section Conjugation

variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n}

/-- Inverse Levi conjugation relabels block scalars along the block map. -/
theorem leviConjugation_symm_blockScalarLevi (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) (g : Fin B.length → Fin C.length)
    (hg : ∀ a, blockIndex C (w a) = g (blockIndex B a)) (t : Fin C.length → Fˣ) :
    (leviConjugation B C w hw).symm (C.blockScalarLevi F t) =
      B.blockScalarLevi F (t ∘ g) := by
  apply B.leviEmbedding_injective F
  rw [leviConjugation_symm_embedding]
  have h1 : (permutation n F w)⁻¹ * C.leviEmbedding F (C.blockScalarLevi F t) *
      permutation n F w =
      permutation n F w⁻¹ * C.blockScalar F t * (permutation n F w⁻¹)⁻¹ := by
    rw [permutation_inv, permutation_inv, inv_inv]
    rfl
  rw [h1]
  change _ = B.blockScalar F (t ∘ g)
  apply Units.ext
  ext x y
  rw [permutation_conjugate_entry, inv_inv, B.coe_blockScalar, C.coe_blockScalar,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    have := hg x
    simp only [blockIndex] at this
    simp [this]
  · simp [hxy, w.injective.ne hxy]

end Conjugation

section Scalar

variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n}
  {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- A block scalar acts on a block tensor of factors with scalar characters by
the product of the characters at its entries. -/
theorem blockTensor_blockScalarLevi
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)}
    {ω : Fin B.length → (Fˣ →* ℂˣ)}
    (h : ∀ i, Classification.HasScalarCharacter (σ i) GeneralLinear.scalar (ω i))
    (s : Fin B.length → Fˣ) (v : PiTensorProduct ℂ V) :
    B.blockTensor σ (B.blockScalarLevi F s) v = (∏ i, (ω i (s i) : ℂ)) • v := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have hf : (fun i => σ i (B.blockScalarLevi F s i) (f i)) =
        fun i => (ω i (s i) : ℂ) • f i :=
      funext fun i => h i (s i) (f i)
    rw [map_smul, B.blockTensor_tprod, hf, MultilinearMap.map_smul_univ, smul_comm r]
  | add x y hx hy =>
    rw [map_add, hx, hy, smul_add]

/-- A block scalar of the target acts on the Weyl transport of a block tensor by
the product of the characters at the relabelled entries. -/
theorem transport_blockTensor_blockScalarLevi (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w)
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)}
    {ω : Fin B.length → (Fˣ →* ℂˣ)}
    (h : ∀ i, Classification.HasScalarCharacter (σ i) GeneralLinear.scalar (ω i))
    (t : Fin C.length → Fˣ) (v : PiTensorProduct ℂ V) :
    transport B C w hw (B.blockTensor σ) (C.blockScalarLevi F t) v =
      (∏ i, (ω i (t (blockMap B C w i)) : ℂ)) • v := by
  change B.blockTensor σ ((leviConjugation B C w hw).symm (C.blockScalarLevi F t)) v = _
  rw [leviConjugation_symm_blockScalarLevi w hw (blockMap B C w)
    (TotalConjugatingCount.blockIndex_apply hw)]
  exact blockTensor_blockScalarLevi h _ v

end Scalar

section Digits

/-- Base-`b` expansions with digits below `b` are unique. -/
theorem digits_sum_injective {b : ℕ} : ∀ {k : ℕ} {d d' : Fin k → ℕ},
    (∀ j, d j < b) → (∀ j, d' j < b) →
    ∑ j, d j * b ^ (j : ℕ) = ∑ j, d' j * b ^ (j : ℕ) → d = d'
  | 0, d, d', _, _, _ => funext fun j => j.elim0
  | k + 1, d, d', hd, hd', h => by
    have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) (hd 0)
    have hsplit : ∀ e : Fin (k + 1) → ℕ,
        ∑ j, e j * b ^ (j : ℕ) = e 0 + b * ∑ j : Fin k, e j.succ * b ^ (j : ℕ) := by
      intro e
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit, hsplit] at h
    have h0 : d 0 = d' 0 := by
      have := congrArg (· % b) h
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd 0), Nat.mod_eq_of_lt (hd' 0)]
        using this
    have hrest : ∑ j : Fin k, d j.succ * b ^ (j : ℕ) = ∑ j : Fin k, d' j.succ * b ^ (j : ℕ) := by
      have := congrArg (· / b) h
      simpa [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (hd 0), Nat.div_eq_of_lt (hd' 0)]
        using this
    have htail := digits_sum_injective (fun j => hd j.succ) (fun j => hd' j.succ) hrest
    funext j
    refine Fin.cases h0 (fun j => ?_) j
    exact congrFun htail j

/-- A permutation of `Fin m` is determined by the weighted sum `∑ i, i * m ^ g i`. -/
theorem perm_eq_of_weightedSum_eq {m : ℕ} {g g' : Equiv.Perm (Fin m)}
    (h : ∑ i : Fin m, (i : ℕ) * m ^ (g i : ℕ) = ∑ i : Fin m, (i : ℕ) * m ^ (g' i : ℕ)) :
    g = g' := by
  have hre : ∀ g : Equiv.Perm (Fin m),
      ∑ i : Fin m, (i : ℕ) * m ^ (g i : ℕ) = ∑ j : Fin m, (g.symm j : ℕ) * m ^ (j : ℕ) := by
    intro g
    rw [← Equiv.sum_comp g.symm (fun i => (i : ℕ) * m ^ (g i : ℕ))]
    simp
  rw [hre, hre] at h
  have := digits_sum_injective (fun j => (g.symm j).isLt) (fun j => (g'.symm j).isLt) h
  have hs : g.symm = g'.symm := Equiv.ext fun j => Fin.ext (congrFun this j)
  simpa using congrArg Equiv.symm hs

/-- A permutation of `Fin m` other than the identity has a descent. -/
theorem exists_descent_of_ne_one {m : ℕ} {g : Equiv.Perm (Fin m)} (hg : g ≠ 1) :
    ∃ k, ∃ hk : k + 1 < m, g ⟨k + 1, hk⟩ < g ⟨k, by omega⟩ := by
  by_contra h
  push Not at h
  apply hg
  have hmono : StrictMono g := by
    cases m with
    | zero => exact fun a => a.elim0
    | succ n =>
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      have hle := h i.val (by have := i.isLt; omega)
      have hne : g i.castSucc ≠ g i.succ :=
        g.injective.ne (Fin.ne_of_lt Fin.castSucc_lt_succ)
      exact lt_of_le_of_ne hle hne
  have hid : (g : Fin m → Fin m) = id :=
    (StrictMono.range_inj_of_wellFoundedLT hmono strictMono_id).mp
      (by rw [g.surjective.range_eq, Set.range_id])
  ext i
  simp [hid]

/-- A permutation of `Fin m` other than the reversal has an ascent. -/
theorem exists_ascent_of_ne_rev {m : ℕ} {g : Equiv.Perm (Fin m)} (hg : g ≠ Fin.revPerm) :
    ∃ k, ∃ hk : k + 1 < m, g ⟨k, by omega⟩ < g ⟨k + 1, hk⟩ := by
  have hg' : Fin.revPerm * g ≠ 1 := by
    intro h
    apply hg
    have hrr : (Fin.revPerm : Equiv.Perm (Fin m)) * Fin.revPerm = 1 := by
      ext i
      simp
    have := congrArg (fun x => Fin.revPerm * x) h
    simp only [mul_one, ← mul_assoc, hrr, one_mul] at this
    exact this
  obtain ⟨k, hk, hlt⟩ := exists_descent_of_ne_one hg'
  refine ⟨k, hk, ?_⟩
  simpa [Fin.rev_lt_rev] using hlt

end Digits

section Segment

open scoped NNReal

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The entries `ϖ^(m^j)` of the separating block scalar. -/
def separatingEntries (m : ℕ) : Fin m → F.Carrierˣ :=
  fun j => LocalFactor.PadicAbelian.uniformizerUnit T ^ (m ^ (j : ℕ))

/-- The normalized absolute value `q⁻¹` of the uniformizer, as a real number. -/
def uniformizerAbs : ℝ :=
  ((T.normalizedAbsUnits (LocalFactor.PadicAbelian.uniformizerUnit T) : ℝ≥0) : ℝ)

theorem uniformizerAbs_pos : 0 < uniformizerAbs T :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr
    (T.normalizedAbsUnits (LocalFactor.PadicAbelian.uniformizerUnit T)).ne_zero)

theorem uniformizerAbs_lt_one : uniformizerAbs T < 1 := by
  change T.normalizedAbs T.uniformizer < 1
  rw [T.normalizedAbs_uniformizer, zpow_neg_one]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast T.residueCardinality_gt_one)

/-- The scalar by which the separating block scalar acts on a transported
tensor of the segment factors, as a function of the block map `g`. Block `i`
carries `ν^i A`, whose scalar character is `ω ⊗ ν^i`. -/
def segmentScalar (ω : F.Carrierˣ →* ℂˣ) (r m : ℕ) (g : Fin m → Fin m) : ℂ :=
  ∏ i : Fin m, (((ω * (T.determinantPowerCharacter r ((i : ℕ) : ℝ)).comp
    GeneralLinear.scalar) (separatingEntries T m (g i)) : ℂˣ) : ℂ)

theorem segmentScalar_eq (ω : F.Carrierˣ →* ℂˣ) (r m : ℕ) (g : Equiv.Perm (Fin m)) :
    segmentScalar T ω r m g = (∏ j, (ω (separatingEntries T m j) : ℂ)) *
      ((uniformizerAbs T ^ (r * ∑ i : Fin m, (i : ℕ) * m ^ (g i : ℕ)) : ℝ) : ℂ) := by
  unfold segmentScalar
  simp only [MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply,
    T.coe_determinantPowerCharacter_scalar]
  rw [Finset.prod_mul_distrib, Equiv.prod_comp g (fun j => (ω (separatingEntries T m j) : ℂ))]
  congr 1
  have hterm : ∀ i : Fin m,
      ((T.normalizedAbsUnits (separatingEntries T m (g i)) : ℝ≥0) : ℝ) ^
          ((r : ℝ) * ((i : ℕ) : ℝ)) =
        uniformizerAbs T ^ (m ^ (g i : ℕ) * (r * (i : ℕ))) := by
    intro i
    have h1 : ((T.normalizedAbsUnits (separatingEntries T m (g i)) : ℝ≥0) : ℝ) =
        uniformizerAbs T ^ (m ^ (g i : ℕ)) := by
      simp [separatingEntries, uniformizerAbs, map_pow, Units.val_pow_eq_pow_val]
    rw [h1, show (r : ℝ) * ((i : ℕ) : ℝ) = ((r * (i : ℕ) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, ← pow_mul]
  simp only [hterm]
  have hsum : ∑ i : Fin m, m ^ (g i : ℕ) * (r * (i : ℕ)) =
      r * ∑ i : Fin m, (i : ℕ) * m ^ (g i : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [← Complex.ofReal_prod, Finset.prod_pow_eq_pow_sum, hsum]

/-- The segment scalars of distinct block permutations are distinct. -/
theorem segmentScalar_injective (ω : F.Carrierˣ →* ℂˣ) {r : ℕ} (hr : 0 < r) (m : ℕ)
    {g g' : Equiv.Perm (Fin m)}
    (h : segmentScalar T ω r m g = segmentScalar T ω r m g') : g = g' := by
  rw [segmentScalar_eq, segmentScalar_eq] at h
  have hK : (∏ j, (ω (separatingEntries T m j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Units.ne_zero _
  have h' := mul_left_cancel₀ hK h
  have h'' := Complex.ofReal_injective h'
  have hpow := (pow_right_strictAnti₀ (uniformizerAbs_pos T) (uniformizerAbs_lt_one T)).injective h''
  exact perm_eq_of_weightedSum_eq (Nat.eq_of_mul_eq_mul_left hr hpow)

end Segment

end Langlands.SegmentFullJacquet
