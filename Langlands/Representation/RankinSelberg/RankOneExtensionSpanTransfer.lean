import Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonStatement
import Langlands.Representation.RankinSelberg.RankOneExtensionAnalyticData
import Langlands.Group.GL.RankReindex
import Langlands.Representation.RankinSelberg.WhittakerRankCast

/-!
# Transfer layer for the strict rank-one extension span comparison

The bookkeeping half of JPSS (1983), Lemma (5.5): from a pointwise identity
`Ψ_ind(s) = c Ψ_base(s)`, with `c ≠ 0` and the induced integral absolutely
convergent on a right half-plane, deduce the inclusion of the Laurent spans of
the actual zeta values. The rank equations of `unequalRankZetaValuesAt` are
unpacked through an explicit rank cast of Whittaker functions, and the casts are
evaluated on the concrete block matrices of `RankOneExtensionAnalyticData`.
No analytic comparison is proved here.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW uW₂

section RankCast

variable {F : Type uF} [Field F] [TopologicalSpace F] (ψ : UnitaryAdditiveCharacter F)

/-- Transport a Whittaker function along an equality of ranks. -/
abbrev rankCastWhittaker {m m' : ℕ} (h : m = m') (W : WhittakerFunctions ψ m) :
    WhittakerFunctions ψ m' :=
  InducedTailIntermediate.whittakerRankCast ψ h W

/-- The transported function reads its argument through the entry-preserving
reindex along the equality of matrix sizes. -/
theorem rankCastWhittaker_apply {m m' : ℕ} (h : m = m') (W : WhittakerFunctions ψ m)
    (g : Langlands.GeneralLinear (m' + 1) F) :
    (rankCastWhittaker ψ h W).val g =
      W.val ((reindex (R := F) (finCongr (congrArg (· + 1) h))).symm g) := by
  subst h
  rfl

@[simp] theorem rankCastWhittaker_rfl {m : ℕ} (W : WhittakerFunctions ψ m) :
    rankCastWhittaker ψ (rfl : m = m) W = W :=
  rfl

end RankCast

section ZetaValues

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Membership in the transported block zeta values, with the Whittaker function
kept at the large rank `r` and cast to the block rank. -/
theorem mem_unequalRankZetaValuesAt_iff {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (j k : ℕ) (hr : r = n + (j + k + 1)) [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (R : RationalFunctions) :
    R ∈ unequalRankZetaValuesAt j k hr q ψ abv μ ν π σ ↔
      ∃ W₀ ∈ whittakerSet ψ r π, ∃ W' ∈ inverseWhittakerSet ψ n σ,
        (∃ a : ℝ, ∀ s : ℂ, a < s.re →
          UnequalRankConverges ψ abv j k μ ν (rankCastWhittaker ψ hr W₀) W' s) ∧
        HasRationalContinuation q
          (unequalRankIntegral ψ abv j k μ ν (rankCastWhittaker ψ hr W₀) W') R := by
  subst hr
  rfl

end ZetaValues

section SpanGlue

/-- If every value of `S` has a nonzero constant multiple in `T`, the Laurent span
of `S` lies in that of `T`. -/
theorem zetaSpan_le_of_forall_exists_const_mul {S T : Set RationalFunctions}
    (h : ∀ R ∈ S, ∃ c : ℂ, c ≠ 0 ∧ RatFunc.C c * R ∈ T) : zetaSpan S ≤ zetaSpan T := by
  refine Submodule.span_le.2 fun R hR => ?_
  obtain ⟨c, hc, hT⟩ := h R hR
  have hmem : LaurentPolynomial.C c⁻¹ • (RatFunc.C c * R) ∈ zetaSpan T :=
    Submodule.smul_mem _ _ (mem_zetaSpan hT)
  rwa [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_C, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hc, map_one, one_mul] at hmem

/-- A function agreeing with `c * f` on a right half-plane continues to `C c * R`
whenever `f` continues to `R`. -/
theorem hasRationalContinuation_of_eq_const_mul {q : ℕ} {f g : ℂ → ℂ} {R : RationalFunctions}
    (c : ℂ) (a : ℝ) (hfg : ∀ s : ℂ, a < s.re → g s = c * f s)
    (h : HasRationalContinuation q f R) :
    HasRationalContinuation q g (RatFunc.C c * R) := by
  obtain ⟨b, hb⟩ := hasRationalContinuation_const_mul c h
  refine ⟨max a b, fun s hs => ?_⟩
  obtain ⟨hd, he⟩ := hb s (lt_of_le_of_lt (le_max_right a b) hs)
  exact ⟨hd, (hfg s (lt_of_le_of_lt (le_max_left a b) hs)).trans he⟩

end SpanGlue

section PointwiseTransfer

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]

/-- The general transfer: if every convergent zeta integral of the first block is,
on a right half-plane, a nonzero constant multiple of an absolutely convergent zeta
integral of the second block for the same large representation, then the Laurent
span of the first zeta values lies in that of the second. -/
theorem zetaSpan_unequalRankZetaValuesAt_le_of_pointwise {n n' r : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient n' F)]
    (j k j' k' : ℕ) (hr : r = n + (j + k + 1)) (hr' : r = n' + (j' + k' + 1))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    [MeasurableSpace (Matrix (Fin j') (Fin (n' + 1)) F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (μ' : Measure (LeftUnipotentQuotient n' F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (ν' : Measure (Matrix (Fin j') (Fin (n' + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (σ' : Representation ℂ (Langlands.GeneralLinear (n' + 1) F) W₂)
    (H : ∀ W₀ ∈ whittakerSet ψ r π, ∀ W' ∈ inverseWhittakerSet ψ n σ,
      (∃ a : ℝ, ∀ s : ℂ, a < s.re →
        UnequalRankConverges ψ abv j k μ ν (rankCastWhittaker ψ hr W₀) W' s) →
      ∃ W₁ ∈ whittakerSet ψ r π, ∃ W'' ∈ inverseWhittakerSet ψ n' σ',
        ∃ c : ℂ, c ≠ 0 ∧ ∃ a' : ℝ, ∀ s : ℂ, a' < s.re →
          UnequalRankConverges ψ abv j' k' μ' ν' (rankCastWhittaker ψ hr' W₁) W'' s ∧
          unequalRankIntegral ψ abv j' k' μ' ν' (rankCastWhittaker ψ hr' W₁) W'' s =
            c * unequalRankIntegral ψ abv j k μ ν (rankCastWhittaker ψ hr W₀) W' s) :
    zetaSpan (unequalRankZetaValuesAt j k hr q ψ abv μ ν π σ) ≤
      zetaSpan (unequalRankZetaValuesAt j' k' hr' q ψ abv μ' ν' π σ') := by
  refine zetaSpan_le_of_forall_exists_const_mul fun R hR => ?_
  obtain ⟨W₀, hW₀, W', hW', hconv, hR⟩ :=
    (mem_unequalRankZetaValuesAt_iff j k hr q ψ abv μ ν π σ R).1 hR
  obtain ⟨W₁, hW₁, W'', hW'', c, hc, a', h⟩ := H W₀ hW₀ W' hW' hconv
  refine ⟨c, hc, (mem_unequalRankZetaValuesAt_iff j' k' hr' q ψ abv μ' ν' π σ' _).2
    ⟨W₁, hW₁, W'', hW'', ⟨a', fun s hs => (h s hs).1⟩, ?_⟩⟩
  exact hasRationalContinuation_of_eq_const_mul c a' (fun s hs => (h s hs).2) hR

end PointwiseTransfer

section StatementShape

/-- The transfer in the shape of `RankOneExtensionSpanComparisonStatement`, with the
trailing index `k` and both rank equations arbitrary; the statement is the instance
`k = r - t - 2` with its proofs `hrBase` and `hrInd`. The only extra premise is the
pointwise comparison of the actual zeta integrals: every convergent block-one
integral of `π × σ₁` is, on a right half-plane, a nonzero constant multiple of an
absolutely convergent block-zero integral of `π` against the lower induction. -/
theorem rankOneExtensionSpanComparison_of_pointwise
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (hrB : r = t + (1 + k + 1)) (hrI : r = (1 + t) + (0 + k + 1)) :
    let χlift : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier)
        (ULift.{uW} ℂ) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
        (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient (1 + t) F.Carrier) := ⟨rfl⟩
    ∀ (μbase : Measure (LeftUnipotentQuotient t F.Carrier))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F.Carrier)),
      (∀ W₀ ∈ whittakerSet ψ r π, ∀ W' ∈ inverseWhittakerSet ψ t σ₁,
        (∃ a : ℝ, ∀ s : ℂ, a < s.re →
          UnequalRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData) 1 k
            μbase (rectangularMeasure ν.val 1 (t + 1)) (rankCastWhittaker ψ hrB W₀) W' s) →
        ∃ W₁ ∈ whittakerSet ψ r π,
          ∃ W'' ∈ inverseWhittakerSet ψ (1 + t) (rankOneExtensionLowerInduced F t χlift σ₁),
          ∃ c : ℂ, c ≠ 0 ∧ ∃ a' : ℝ, ∀ s : ℂ, a' < s.re →
            UnequalRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData) 0 k
              μind (rectangularMeasure ν.val 0 ((1 + t) + 1))
              (rankCastWhittaker ψ hrI W₁) W'' s ∧
            unequalRankIntegral ψ (normalizedAbsoluteValue F.canonicalTopologicalData) 0 k
                μind (rectangularMeasure ν.val 0 ((1 + t) + 1))
                (rankCastWhittaker ψ hrI W₁) W'' s =
              c * unequalRankIntegral ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
                1 k μbase (rectangularMeasure ν.val 1 (t + 1))
                (rankCastWhittaker ψ hrB W₀) W' s) →
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := t) 1 k hrB
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μbase
        (rectangularMeasure ν.val 1 (t + 1)) π σ₁) ≤
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := 1 + t) 0 k hrI
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μind
        (rectangularMeasure ν.val 0 ((1 + t) + 1)) π
        (rankOneExtensionLowerInduced F t χlift σ₁)) := by
  intro χlift
  let := F.canonicalTopologicalData.topology
  let := borel F.Carrier
  let := borel (LeftUnipotentQuotient t F.Carrier)
  let := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
  intro μbase μind H
  exact zetaSpan_unequalRankZetaValuesAt_le_of_pointwise 1 k 0 k hrB hrI
    F.canonicalTopologicalData.residueCardinality ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData) μbase μind
    (rectangularMeasure ν.val 1 (t + 1)) (rectangularMeasure ν.val 0 ((1 + t) + 1)) π σ₁
    _ H

end StatementShape

section Matrices

variable {K : Type uF} [Field K]

/-- Numeric entries of the standard rank inclusion `g ↦ diag(g, I_d)`. -/
theorem rankInclusion_entry (n d : ℕ) (g : Langlands.GeneralLinear n K)
    (i j : Fin (n + d)) :
    rankInclusion d g i j =
      if hi : i.val < n then
        if hj : j.val < n then g ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
      else if i = j then 1 else 0 := by
  change blockSum (g, 1) i j = _
  cases i using Fin.addCases <;> cases j using Fin.addCases <;>
    all_goals (simp [Fin.ext_iff, Matrix.one_apply]; try omega)

/-- Numeric entries of the lower block `[m, 0; x, a]` in `GL(1 + (t + 1))`. -/
theorem rankOneExtensionLowerBlock_entry (t : ℕ) (m : Langlands.GeneralLinear (t + 1) K)
    (x : Fin (t + 1) → K) (a : Kˣ) (i j : Fin (1 + (t + 1))) :
    rankOneExtensionLowerBlock t m x a i j =
      if hi : i.val < t + 1 then
        if hj : j.val < t + 1 then m ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
      else if hj : j.val < t + 1 then x ⟨j.val, hj⟩ else a.val := by
  obtain ⟨i, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective i
  obtain ⟨j, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective j
  rw [rankOneExtensionLowerBlock_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp [rankOneExtensionCellCoordinates, Fin.is_le]
  · simp [rankOneExtensionCellCoordinates, Fin.val_eq_zero, not_lt.2 (Fin.is_le i)]
  · simp [rankOneExtensionCellCoordinates, Fin.val_eq_zero, not_lt.2 (Fin.is_le j)]
  · simp [rankOneExtensionCellCoordinates, Fin.val_eq_zero]

/-- The lower block factors as `[m, 0; x, 1] * [1, 0; 0, a]`. -/
theorem rankOneExtensionLowerBlock_eq_mul (t : ℕ) (m : Langlands.GeneralLinear (t + 1) K)
    (x : Fin (t + 1) → K) (a : Kˣ) :
    rankOneExtensionLowerBlock t m x a =
      rankOneExtensionLowerBlock t m x 1 * rankOneExtensionLowerBlock t 1 0 a := by
  simp only [rankOneExtensionLowerBlock]
  rw [← map_mul]
  congr 1
  apply Units.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.mul_apply, Matrix.one_apply]

/-- The embedded lower block factors in the same way. -/
theorem rankOneExtensionEmbeddedLowerBlock_eq_mul (t k : ℕ)
    (m : Langlands.GeneralLinear (t + 1) K) (x : Fin (t + 1) → K) (a : Kˣ) :
    rankOneExtensionEmbeddedLowerBlock t k m x a =
      rankOneExtensionEmbeddedLowerBlock t k m x 1 *
        rankOneExtensionEmbeddedLowerBlock t k 1 0 a := by
  simp only [rankOneExtensionEmbeddedLowerBlock]
  rw [← map_mul, ← rankOneExtensionLowerBlock_eq_mul]

/-- The block-one JPSS matrix `[g, 0, 0; x, 1, 0; 0, 0, I_(k+1)]`, read at the rank
`(1 + (t + 1)) + k` of the embedded lower block, is that block with `a = 1`. -/
theorem reindex_symm_unequalRankMatrix_one (t k : ℕ)
    (h : (1 + (t + 1)) + k + 1 = t + (1 + k + 1) + 1)
    (g : Langlands.GeneralLinear (t + 1) K) (x : Matrix (Fin 1) (Fin (t + 1)) K) :
    (reindex (R := K) (finCongr h)).symm (unequalRankMatrix 1 k g x) =
      rankOneExtensionEmbeddedLowerBlock t k g (x 0) 1 := by
  apply Units.ext
  ext i j
  obtain ⟨x₀, rfl⟩ : ∃ x₀ : Fin (t + 1) → K, x = Matrix.of fun _ => x₀ :=
    ⟨x 0, by ext y z; rw [Subsingleton.elim y 0]; rfl⟩
  rw [reindex_finCongr_symm_apply, unequalRankMatrix_val]
  simp only [Matrix.add_apply, appendIdentity_entry, rectangularEntries, Fin.val_cast,
    rankOneExtensionEmbeddedLowerBlock, rankInclusion_entry, rankOneExtensionLowerBlock_entry,
    Fin.ext_iff, Fin.val_mk, Matrix.of_apply, Units.val_one]
  split_ifs
  all_goals first | rfl | omega | simp_all

/-- The diagonal inclusion `diag(g, I_(k+1))` from the block-zero side, after the
rank cast `1 + (t + 1) = (1 + t) + 1`, is the standard rank inclusion. -/
theorem reindex_symm_appendIdentity_reindex (t k : ℕ)
    (h : (1 + (t + 1)) + k + 1 = (1 + t) + (0 + k + 1) + 1)
    (hc : 1 + (t + 1) = (1 + t) + 1) (g : Langlands.GeneralLinear (1 + (t + 1)) K) :
    (reindex (R := K) (finCongr h)).symm
        (appendIdentity (1 + t) (0 + k + 1) (reindex (R := K) (finCongr hc) g)) =
      rankInclusion (k + 1) g := by
  apply Units.ext
  ext i j
  rw [reindex_finCongr_symm_apply, appendIdentity_entry]
  simp only [reindex_finCongr_apply, rankInclusion_entry, Fin.val_cast, Fin.cast_mk,
    Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

/-- The determinant weight is unchanged by the entry-preserving reindex. -/
theorem determinantWeight_reindex_finCongr (abv : AbsoluteValue K ℝ) {m n : ℕ}
    (h : m = n) (g : Langlands.GeneralLinear m K) (s : ℂ) :
    determinantWeight abv (reindex (R := K) (finCongr h) g) s = determinantWeight abv g s := by
  subst h
  rfl

end Matrices

section Integrands

variable {K : Type uF} [Field K] [TopologicalSpace K] (ψ : UnitaryAdditiveCharacter K)

/-- The cast Whittaker function on the block-one matrix is the original function on
the embedded lower block with `a = 1`. -/
theorem rankCastWhittaker_unequalRankMatrix_one {t k : ℕ}
    (hrB : (1 + (t + 1)) + k = t + (1 + k + 1))
    (W : WhittakerFunctions ψ ((1 + (t + 1)) + k))
    (g : Langlands.GeneralLinear (t + 1) K) (x : Matrix (Fin 1) (Fin (t + 1)) K) :
    (rankCastWhittaker ψ hrB W).val (unequalRankMatrix 1 k g x) =
      W.val (rankOneExtensionEmbeddedLowerBlock t k g (x 0) 1) := by
  rw [rankCastWhittaker_apply, reindex_symm_unequalRankMatrix_one]

/-- The cast Whittaker function on the block-zero diagonal matrix of a cast element
of `GL(1 + (t + 1))` is the original function on its standard rank inclusion. -/
theorem rankCastWhittaker_appendIdentity_reindex {t k : ℕ}
    (hrI : (1 + (t + 1)) + k = (1 + t) + (0 + k + 1))
    (hc : 1 + (t + 1) = (1 + t) + 1)
    (W : WhittakerFunctions ψ ((1 + (t + 1)) + k))
    (g : Langlands.GeneralLinear (1 + (t + 1)) K) :
    (rankCastWhittaker ψ hrI W).val
        (appendIdentity (1 + t) (0 + k + 1) (reindex (R := K) (finCongr hc) g)) =
      W.val (rankInclusion (k + 1) g) := by
  rw [rankCastWhittaker_apply, reindex_symm_appendIdentity_reindex]

/-- The lower-block instance: the block-zero matrix of `B(m, x, a)` gives the
embedded lower block. -/
theorem rankCastWhittaker_appendIdentity_lowerBlock {t k : ℕ}
    (hrI : (1 + (t + 1)) + k = (1 + t) + (0 + k + 1))
    (hc : 1 + (t + 1) = (1 + t) + 1)
    (W : WhittakerFunctions ψ ((1 + (t + 1)) + k))
    (m : Langlands.GeneralLinear (t + 1) K) (x : Fin (t + 1) → K) (a : Kˣ) :
    (rankCastWhittaker ψ hrI W).val
        (appendIdentity (1 + t) (0 + k + 1)
          (reindex (R := K) (finCongr hc) (rankOneExtensionLowerBlock t m x a))) =
      W.val (rankOneExtensionEmbeddedLowerBlock t k m x a) :=
  rankCastWhittaker_appendIdentity_reindex ψ hrI hc W _

variable (abv : AbsoluteValue K ℝ)

/-- The block-one integrand under the rank cast:
`W(diag([g, 0; x, 1], I_(k+1))) W'(g) |det g|^(s - (k + 2)/2)`. -/
theorem unequalRankIntegrand_rankCast_one_mk {t k : ℕ}
    (hrB : (1 + (t + 1)) + k = t + (1 + k + 1))
    (W : WhittakerFunctions ψ ((1 + (t + 1)) + k)) (W' : InverseWhittakerFunctions ψ t)
    (s : ℂ) (x : Matrix (Fin 1) (Fin (t + 1)) K) (g : Langlands.GeneralLinear (t + 1) K) :
    unequalRankIntegrand ψ abv 1 k (rankCastWhittaker ψ hrB W) W' s x (Quotient.mk _ g) =
      W.val (rankOneExtensionEmbeddedLowerBlock t k g (x 0) 1) * W'.val g *
        determinantWeight abv g (s - ((1 + k + 1 : ℕ) : ℂ) / 2) := by
  rw [unequalRankIntegrand_mk, rankCastWhittaker_unequalRankMatrix_one]

/-- The block-zero integrand under the rank cast, at a cast element of
`GL(1 + (t + 1))`: `W(diag(g, I_(k+1))) W''(g) |det g|^(s - (k + 1)/2)`. -/
theorem unequalRankIntegrand_rankCast_zero_mk {t k : ℕ}
    (hrI : (1 + (t + 1)) + k = (1 + t) + (0 + k + 1))
    (hc : 1 + (t + 1) = (1 + t) + 1)
    (W : WhittakerFunctions ψ ((1 + (t + 1)) + k))
    (W'' : InverseWhittakerFunctions ψ (1 + t)) (s : ℂ)
    (x : Matrix (Fin 0) (Fin ((1 + t) + 1)) K) (g : Langlands.GeneralLinear (1 + (t + 1)) K) :
    unequalRankIntegrand ψ abv 0 k (rankCastWhittaker ψ hrI W) W'' s x
        (Quotient.mk _ (reindex (R := K) (finCongr hc) g)) =
      W.val (rankInclusion (k + 1) g) * W''.val (reindex (R := K) (finCongr hc) g) *
        determinantWeight abv g (s - ((0 + k + 1 : ℕ) : ℂ) / 2) := by
  rw [unequalRankIntegrand_mk, unequalRankMatrix_zero_rows,
    rankCastWhittaker_appendIdentity_reindex, determinantWeight_reindex_finCongr]

end Integrands

end Langlands.RankinSelberg
