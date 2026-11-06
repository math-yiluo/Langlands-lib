import Langlands.Representation.RankinSelberg.UnequalRankDeterminantSlices
import Langlands.Representation.RankinSelberg.UnequalRankZeroRowIntegrandContinuityProof
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.Whittaker.ModelKirillovStatement

/-!
# Laurent-valued block-zero JPSS integrals for compactly supported Whittaker functions

If the restriction `g ↦ W(diag(g, I))` of a Whittaker function of the larger
group is compactly supported modulo `N`, every block-zero unequal-rank zeta
integral is a Laurent polynomial in `q^(-s)` for all `s`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

section LeadingBlock

variable {F : Type uF} [Field F]

/-- The leading `(n+1) × (n+1)` block of a square matrix of size `n + d + 1`. -/
def leadingBlock (n d : ℕ) (M : Matrix (Fin (n + d + 1)) (Fin (n + d + 1)) F) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  M.submatrix (Fin.castLE (by omega)) (Fin.castLE (by omega))

private theorem castLE_range {n d : ℕ} (l : Fin (n + d + 1))
    (hl : l ∉ Set.range (Fin.castLE (show n + 1 ≤ n + d + 1 by omega))) :
    n + 1 ≤ l.val := by
  by_contra h
  exact hl ⟨⟨l.val, by omega⟩, rfl⟩

/-- Right multiplication by `diag(g, I_d)` multiplies the leading block by `g`. -/
theorem leadingBlock_mul_appendIdentity (n d : ℕ)
    (M : Matrix (Fin (n + d + 1)) (Fin (n + d + 1)) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    leadingBlock n d (M * (appendIdentity n d g).val) = leadingBlock n d M * g.val := by
  ext i j
  simp only [leadingBlock, Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective (Fin.castLE (by omega)) (Fin.castLE_injective _)
  · intro l hl
    have hl' := castLE_range l hl
    rw [appendIdentity_entry]
    have hj : (Fin.castLE (show n + 1 ≤ n + d + 1 by omega) j).val < n + 1 := by
      simp [j.isLt]
    have hne : l ≠ Fin.castLE (show n + 1 ≤ n + d + 1 by omega) j := by
      intro h
      rw [h] at hl'
      omega
    simp [show ¬ l.val < n + 1 by omega, hne]
  · intro l
    rw [appendIdentity_entry]
    simp [l.isLt, j.isLt]

/-- Left multiplication by `diag(g, I_d)` multiplies the leading block by `g`. -/
theorem leadingBlock_appendIdentity_mul (n d : ℕ)
    (M : Matrix (Fin (n + d + 1)) (Fin (n + d + 1)) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    leadingBlock n d ((appendIdentity n d g).val * M) = g.val * leadingBlock n d M := by
  ext i j
  simp only [leadingBlock, Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective (Fin.castLE (by omega)) (Fin.castLE_injective _)
  · intro l hl
    have hl' := castLE_range l hl
    rw [appendIdentity_entry]
    simp [show ¬ l.val < n + 1 by omega, i.isLt]
  · intro l
    rw [appendIdentity_entry]
    simp [l.isLt, i.isLt]

/-- The leading block is multiplicative when the right factor is upper triangular. -/
theorem leadingBlock_mul_of_upperTriangular (n d : ℕ)
    (M U : Matrix (Fin (n + d + 1)) (Fin (n + d + 1)) F)
    (hU : ∀ i j, j < i → U i j = 0) :
    leadingBlock n d (M * U) = leadingBlock n d M * leadingBlock n d U := by
  ext i j
  simp only [leadingBlock, Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective (Fin.castLE (by omega)) (Fin.castLE_injective _)
  · intro l hl
    have hl' := castLE_range l hl
    rw [hU l _ (by rw [Fin.lt_def]; simp; omega), mul_zero]
  · intro l
    rfl

@[simp] theorem leadingBlock_one (n d : ℕ) :
    leadingBlock n d (1 : Matrix (Fin (n + d + 1)) (Fin (n + d + 1)) F) = 1 := by
  ext i j
  simp [leadingBlock, Matrix.one_apply, Fin.ext_iff]

end LeadingBlock

section CompactSupport

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]

/-- If `diag(g, I_d) = u c` with `u` upper unipotent and `c` in a fixed compact set,
then `g` lies in `N_(n+1) C'` for one compact set `C'` depending only on that set. -/
theorem exists_compact_appendIdentity_support (n d : ℕ)
    (C : Set (Langlands.GeneralLinear (n + d + 1) F)) (hC : IsCompact C) :
    ∃ C' : Set (Langlands.GeneralLinear (n + 1) F), IsCompact C' ∧
      ∀ (g : Langlands.GeneralLinear (n + 1) F) (u c : Langlands.GeneralLinear (n + d + 1) F),
        (∀ i j, j < i → u.val i j = 0) → (∀ i, u.val i i = 1) → c ∈ C →
        appendIdentity n d g = u * c →
        ∃ v : upperUnipotent (n + 1) F, ∃ c' ∈ C', g = v.val * c' := by
  classical
  let β := leadingBlock (F := F) n d
  let E : Langlands.GeneralLinear (n + d + 1) F →
      Matrix (Fin (n + 1)) (Fin (n + 1)) F × (Matrix (Fin (n + 1)) (Fin (n + 1)) F)ᵐᵒᵖ :=
    fun c => (β c.val, MulOpposite.op (β (c⁻¹ : Langlands.GeneralLinear (n + d + 1) F).val))
  have hE : Continuous E :=
    (Units.continuous_val.matrix_submatrix _ _).prodMk
      (MulOpposite.continuous_op.comp (Units.continuous_coe_inv.matrix_submatrix _ _))
  refine ⟨Units.embedProduct _ ⁻¹' (E '' C),
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.image hE), ?_⟩
  intro g u c hu1 hu2 hc hgu
  let uN : upperUnipotent (n + d + 1) F := ⟨u, hu1, hu2⟩
  have hu1' : ∀ i j, j < i → (u⁻¹ : Langlands.GeneralLinear (n + d + 1) F).val i j = 0 :=
    (uN⁻¹).property.1
  have hu2' : ∀ i, (u⁻¹ : Langlands.GeneralLinear (n + d + 1) F).val i i = 1 :=
    (uN⁻¹).property.2
  have hcv : c = u⁻¹ * appendIdentity n d g := by rw [hgu, inv_mul_cancel_left]
  have hci : c⁻¹ = appendIdentity n d g⁻¹ * u := by
    rw [hcv, mul_inv_rev, inv_inv, map_inv]
  let v : Langlands.GeneralLinear (n + 1) F :=
    { val := β u.val
      inv := β (u⁻¹ : Langlands.GeneralLinear (n + d + 1) F).val
      val_inv := by
        rw [← leadingBlock_mul_of_upperTriangular n d _ _ hu1', ← Units.val_mul,
          mul_inv_cancel, Units.val_one, leadingBlock_one]
      inv_val := by
        rw [← leadingBlock_mul_of_upperTriangular n d _ _ hu1, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, leadingBlock_one] }
  have hvN : v ∈ upperUnipotent (n + 1) F := by
    refine ⟨fun i j hij => hu1 _ _ ?_, fun i => hu2 _⟩
    rw [Fin.lt_def] at hij ⊢
    simpa using hij
  refine ⟨⟨v, hvN⟩, v⁻¹ * g, ⟨c, hc, ?_⟩, by simp⟩
  change E c = ((v⁻¹ * g).val, MulOpposite.op ((v⁻¹ * g)⁻¹).val)
  have h1 : β c.val = β (u⁻¹ : Langlands.GeneralLinear (n + d + 1) F).val * g.val := by
    rw [hcv, Units.val_mul]
    exact leadingBlock_mul_appendIdentity n d _ g
  have h2 : β (c⁻¹ : Langlands.GeneralLinear (n + d + 1) F).val = (g⁻¹).val * β u.val := by
    rw [hci, Units.val_mul]
    exact leadingBlock_appendIdentity_mul n d _ g⁻¹
  simp only [E, h1, h2, mul_inv_rev, inv_inv, Units.val_mul]
  rfl

omit [IsTopologicalRing F] [T1Space F] in
/-- `g ↦ diag(g, I_d)` is continuous. -/
private theorem continuous_appendIdentity' (n d : ℕ) :
    Continuous (appendIdentity (F := F) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (GeneralLinear.rankInclusionContinuous 1).continuous.comp ih

end CompactSupport

section Mirabolic

variable {F : Type uF} [Field F]

/-- For a positive identity block, `diag(g, I_(d+1))` has last row `(0, …, 0, 1)`. -/
theorem appendIdentity_succ_lastRow (n d : ℕ) (g : Langlands.GeneralLinear (n + 1) F)
    (a : Fin (n + (d + 1) + 1)) :
    (appendIdentity n (d + 1) g).val (Fin.last (n + (d + 1))) a =
      if a = Fin.last (n + (d + 1)) then 1 else 0 := by
  rw [appendIdentity_entry]
  have hlast : ¬ (Fin.last (n + (d + 1))).val < n + 1 := by
    simp only [Fin.val_last]
    omega
  simp only [hlast, ↓reduceDIte]
  exact if_congr eq_comm rfl rfl

end Mirabolic

section Laurent

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {n : ℕ} (k : ℕ)

local instance zeroBlockTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance zeroBlockValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance zeroBlockLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance zeroBlockT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance zeroBlockQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) :=
  borel (LeftUnipotentQuotient n F.Carrier)
local instance zeroBlockQuotientBorel :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- The residue cardinality is positive. -/
theorem zeroBlock_residueCardinality_pos : 0 < qF :=
  zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one

/-- Integration against the point mass on the zero-row matrix space is evaluation. -/
theorem integral_dirac_zeroRows
    {m : ℕ} [MeasurableSpace (Matrix (Fin 0) (Fin m) F.Carrier)]
    (f : Matrix (Fin 0) (Fin m) F.Carrier → ℂ) :
    ∫ x, f x ∂(Measure.dirac 0) = f 0 := by
  have hf : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
  rw [hf, integral_const]
  simp

/-- If `g ↦ W(diag(g, I))` is supported in `N C` for a compact `C` of the larger
group, every block-zero integral is one Laurent polynomial in `q^(-s)`,
evaluated at the spectral point, for every complex `s`. -/
theorem exists_laurent_unequalRankIntegral_zero
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier)) [IsFiniteMeasureOnCompacts μ]
    [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F.Carrier)]
    (W : WhittakerFunctions ψ (n + (0 + k + 1))) (W' : InverseWhittakerFunctions ψ n)
    (hcont : ∀ s : ℂ, Continuous (unequalRankIntegrand ψ abv 0 k W W' s 0))
    (C : Set (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier)) (hC : IsCompact C)
    (hsupp : ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      W.val (appendIdentity n (0 + k + 1) g) ≠ 0 →
      ∃ u c : Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier,
        (∀ i j, j < i → u.val i j = 0) ∧ (∀ i, u.val i i = 1) ∧ c ∈ C ∧
          appendIdentity n (0 + k + 1) g = u * c) :
    ∃ L : LaurentCoefficients, ∀ s : ℂ,
      unequalRankIntegral ψ abv 0 k μ (Measure.dirac 0) W W' s =
        laurentEval (spectralUnit (zeroBlock_residueCardinality_pos F) s) L := by
  classical
  let T := F.canonicalTopologicalData
  have : T2Space (LeftUnipotentQuotient n F.Carrier) :=
    leftQuotient_t2Space _ UpperUnipotent.isClosed
  obtain ⟨C', hC', hC'supp⟩ := exists_compact_appendIdentity_support n (0 + k + 1) C hC
  let K : Set (LeftUnipotentQuotient n F.Carrier) := Quotient.mk _ '' C'
  have hK : IsCompact K := hC'.image continuous_quotient_mk'
  let f : ℂ → LeftUnipotentQuotient n F.Carrier → ℂ :=
    fun s => unequalRankIntegrand ψ abv 0 k W W' s 0
  have hKsupp : ∀ s, ∀ q, q ∉ K → f s q = 0 := by
    intro s q hq
    induction q using Quotient.inductionOn with
    | h g =>
      change unequalRankIntegrand ψ abv 0 k W W' s 0 (Quotient.mk _ g) = 0
      rw [unequalRankIntegrand_mk, unequalRankMatrix_zero_rows]
      by_contra hne
      have hW : W.val (appendIdentity n (0 + k + 1) g) ≠ 0 := fun h =>
        hne (by rw [h, zero_mul, zero_mul])
      obtain ⟨u, c, hu1, hu2, hc, hgu⟩ := hsupp g hW
      obtain ⟨v, c', hc', hg⟩ := hC'supp g u c hu1 hu2 hc hgu
      apply hq
      refine ⟨c', hc', Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)⟩
      rw [hg, mul_inv_cancel_right]
      exact v.property
  let S : Set ℤ := determinantOrder T n '' K
  have hS : S.Finite := (hK.image (continuous_determinantOrder T n)).finite_of_discrete
  let c : ℤ → ℂ := fun m => ∫ q in determinantSlice T n m, f 0 q ∂μ
  refine ⟨∑ m ∈ hS.toFinset, LaurentPolynomial.C (c m) * LaurentPolynomial.T m, ?_⟩
  intro s
  have hint : Integrable (f s) μ :=
    (hcont s).integrable_of_hasCompactSupport (HasCompactSupport.intro hK (hKsupp s))
  have hsum := hasSum_setIntegral_determinantSlice T μ hint
  have hslice : ∀ m : ℤ, ∫ q in determinantSlice T n m, f s q ∂μ =
      c m * spectralPoint qF s ^ m := by
    intro m
    rw [setIntegral_congr_fun (measurableSet_determinantSlice T n m)
      (fun q hq => unequalRankIntegrand_eq_mul_spectralPoint_zpow F 0 k ψ W W' m q hq s 0),
      integral_mul_const]
  have hzero : ∀ m ∉ hS.toFinset, ∫ q in determinantSlice T n m, f s q ∂μ = 0 := by
    intro m hm
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro q hq
    apply hKsupp s q
    intro hqK
    exact hm (hS.mem_toFinset.mpr ⟨q, hqK, hq⟩)
  have hval := hsum.unique (hasSum_sum_of_ne_finset_zero hzero)
  have hinner : unequalRankIntegral ψ abv 0 k μ (Measure.dirac 0) W W' s =
      ∫ q, f s q ∂μ := by
    unfold unequalRankIntegral
    simp_rw [integral_dirac_zeroRows F]
    rfl
  rw [hinner, hval, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hslice, map_mul, laurentEval_C, laurentEval_T, coe_spectralUnit]

/-- A mirabolic test function restricted along `g ↦ diag(g, I_(k+1))` is continuous. -/
theorem continuous_appendIdentity_of_mirabolicTest (ψ : UnitaryAdditiveCharacter F.Carrier)
    (φ : WhittakerFunctions ψ (n + (0 + k + 1)))
    (hφ : IsMirabolicTestFunction ψ (n + (0 + k + 1)) φ) :
    Continuous (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      φ.val (appendIdentity n (0 + k + 1) g)) := by
  obtain ⟨⟨K, hK⟩, -⟩ := hφ
  have he := continuous_appendIdentity' (F := F.Carrier) n (0 + k + 1)
  apply IsLocallyConstant.continuous
  apply (IsLocallyConstant.iff_exists_open _).2
  intro g
  refine ⟨(fun h => appendIdentity n (0 + k + 1) (g⁻¹ * h)) ⁻¹'
      (K : Set (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier)),
    K.isOpen.preimage (he.comp (continuous_const.mul continuous_id)), by simp, ?_⟩
  intro h hh
  have hmul : appendIdentity n (0 + k + 1) h =
      appendIdentity n (0 + k + 1) g * appendIdentity n (0 + k + 1) (g⁻¹ * h) := by
    rw [← map_mul, mul_inv_cancel_left]
  change φ.val _ = φ.val _
  rw [hmul]
  exact hK _ _ (appendIdentity_succ_lastRow n (0 + k) g)
    (appendIdentity_succ_lastRow n (0 + k) _) hh

/-- Mirabolic compact support of `φ` gives the support hypothesis of
`exists_laurent_unequalRankIntegral_zero` along `g ↦ diag(g, I_(k+1))`. -/
theorem exists_compact_appendIdentity_of_mirabolicTest
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (φ : WhittakerFunctions ψ (n + (0 + k + 1)))
    (hφ : IsMirabolicTestFunction ψ (n + (0 + k + 1)) φ) :
    ∃ C : Set (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier), IsCompact C ∧
      ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
        φ.val (appendIdentity n (0 + k + 1) g) ≠ 0 →
        ∃ u c : Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier,
          (∀ i j, j < i → u.val i j = 0) ∧ (∀ i, u.val i i = 1) ∧ c ∈ C ∧
            appendIdentity n (0 + k + 1) g = u * c := by
  obtain ⟨-, C, hC, hsupp⟩ := hφ
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨u, c, hc, hgu⟩ :=
    hsupp _ (appendIdentity_succ_lastRow n (0 + k) g) hg
  exact ⟨u.val, c, u.property.1, u.property.2, hc, hgu⟩

/-- If every vector of the larger coefficient model is a mirabolic test function
and the smaller representation is smooth, every rational value of the block-zero
family is the image of a Laurent polynomial. -/
theorem exists_laurent_of_mem_unequalRankValuesAt_zero [MeasurableSpace F.Carrier]
    {r : ℕ} (hr : r = n + (0 + k + 1))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier)) [IsFiniteMeasureOnCompacts μ]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W) (hσ : IsSmooth σ)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ)
    (hπ : ∀ f : (coefficientModel π ℓ).toSubmodule, IsMirabolicTestFunction ψ r f.val) :
    ∀ R ∈ unequalRankValuesAt 0 k hr qF ψ abv μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ',
      ∃ L : LaurentCoefficients, laurentToRatFunc L = R := by
  subst hr
  rintro R ⟨f, f', hR⟩
  have hf' : Continuous f'.val.val := by
    obtain ⟨v, rfl⟩ := modelMap_surjective σ ℓ' f'
    exact (Langlands.matrixCoefficient_isLocallyConstant σ ℓ'.val v (hσ v)).continuous
  have hdet : Continuous (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      abv (Matrix.det g.val)) :=
    (NNReal.continuous_coe.comp F.canonicalTopologicalData.continuous_normalizedAbsHom).comp
      Units.continuous_val.matrix_det
  have hcont : ∀ s : ℂ, Continuous (unequalRankIntegrand ψ abv 0 k f.val f'.val s 0) := by
    intro s
    have hweight : Continuous (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
        determinantWeight abv g (s - ((0 + k + 1 : ℕ) : ℂ) / 2)) := by
      apply (Complex.continuous_ofReal.comp hdet).cpow continuous_const
      intro g
      exact Complex.ofReal_mem_slitPlane.mpr
        ((normalizedAbsoluteValue F.canonicalTopologicalData).pos g.det_ne_zero)
    apply (leftQuotient_isOpenQuotientMap
      (upperUnipotent (n + 1) F.Carrier)).isQuotientMap.continuous_iff.mpr
    change Continuous (fun g => f.val.val (unequalRankMatrix 0 k g 0) * f'.val.val g *
      determinantWeight abv g (s - ((0 + k + 1 : ℕ) : ℂ) / 2))
    simp only [unequalRankMatrix_zero_rows]
    exact ((continuous_appendIdentity_of_mirabolicTest F k ψ f.val (hπ f)).mul hf').mul
      hweight
  obtain ⟨C, hC, hsupp⟩ := exists_compact_appendIdentity_of_mirabolicTest F k ψ f.val (hπ f)
  obtain ⟨L, hL⟩ := exists_laurent_unequalRankIntegral_zero F k ψ μ f.val f'.val hcont C hC hsupp
  refine ⟨L, HasRationalContinuation.unique
    F.canonicalTopologicalData.residueCardinality_gt_one ⟨0, fun s _ => ?_⟩ hR⟩
  have hx := laurentToRatFunc_regular_and_eval
    (spectralUnit (zeroBlock_residueCardinality_pos F) s) L
  rw [coe_spectralUnit] at hx
  refine ⟨hx.1, ?_⟩
  rw [hx.2]
  change unequalRankIntegral ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) f.val f'.val s = _
  rw [rectangularMeasure_zero_rows, hL]

end Laurent

end Langlands.RankinSelberg
