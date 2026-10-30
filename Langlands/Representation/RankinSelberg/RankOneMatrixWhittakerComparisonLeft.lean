import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonValues
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero
import Langlands.Representation.RankinSelberg.WhittakerRankCast

/-!
# Rank-one character zeta values at actual rank at least two

For `σ` on `GL_(m+2)` the rank-one character zeta values of `σ × 1` are the
unequal-rank values with `j = 0` and gap `k = m`, written for the relabelled
representation `σ ∘ characterPairRank m` and integrated against the unit point
mass on the zero-row matrix space. This file removes that packaging: for `σ` of
Whittaker type and a nonzero standard functional `ℓ`, these values are exactly the
reduced values `rankOneModelValues` of the `GL₁` integrals
`∫ W(diag(det g, 1, …, 1)) |det g|^(s - (m+1)/2) dg` over the coefficient model of
`ℓ`, for every compatible quotient measure.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

section PointMass

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The product of a measure with the unit point mass is the pushforward along the
section `x ↦ (x, b)`. Unlike `Measure.prod_dirac`, no σ-finiteness is assumed. -/
theorem measure_prod_dirac_eq_map (μ : Measure α) (b : β) :
    μ.prod (Measure.dirac b) = μ.map (fun x => (x, b)) := by
  ext s hs
  rw [Measure.prod_apply hs, Measure.map_apply measurable_prodMk_right hs,
    ← lintegral_indicator_one (measurable_prodMk_right hs)]
  refine lintegral_congr fun x => ?_
  rw [Measure.dirac_apply' _ (measurable_prodMk_left hs)]
  rfl

/-- A product with a measurable space with one point is measurably the first factor. -/
def prodUniqueMeasurableEquiv [Unique β] : α × β ≃ᵐ α where
  toEquiv := Equiv.prodUnique α β
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_prodMk_right

/-- Integrability against the product with the point mass of a one-point space is
integrability of the restriction to the section through that point. -/
theorem integrable_prod_dirac_iff [Unique β] (μ : Measure α) (b : β) (f : α × β → ℂ) :
    Integrable f (μ.prod (Measure.dirac b)) ↔ Integrable (fun x => f (x, b)) μ := by
  obtain rfl : b = default := Subsingleton.elim _ _
  rw [measure_prod_dirac_eq_map]
  exact integrable_map_equiv (prodUniqueMeasurableEquiv (α := α) (β := β)).symm f

end PointMass

section Reindex

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Relabelling the rank of a representation along an equality of ranks transports
its all-functional Whittaker set by the corresponding rank cast. -/
theorem whittakerSet_comp_reindex (ψ : UnitaryAdditiveCharacter F) {N M : ℕ} (h : N = M)
    (σ : Representation ℂ (Langlands.GeneralLinear (M + 1) F) V) :
    whittakerSet ψ N (σ.comp (reindex (finCongr (congrArg (· + 1) h))).toMonoidHom) =
      InducedTailIntermediate.whittakerRankCast ψ h.symm '' whittakerSet ψ M σ := by
  subst h
  have hσ : σ.comp (reindex (finCongr (congrArg (· + 1) (rfl : N = N)))).toMonoidHom = σ := by
    apply MonoidHom.ext
    intro g
    change σ (reindex (finCongr rfl) g) = σ g
    rw [reindex_finCongr_rfl]
    rfl
  rw [hσ]
  exact (Set.image_id' _).symm

omit [TopologicalSpace F] in
/-- The block inclusion `g ↦ diag(g, I_(m+1))` with no rectangular rows, read in
`GL_(m+2)` through the identity relabelling `characterPairRank m`, is the diagonal
matrix with entries `g₀₀, 1, …, 1`. -/
theorem characterPairRank_appendIdentity_val (m : ℕ) (g : Langlands.GeneralLinear (0 + 1) F) :
    (characterPairRank m (appendIdentity 0 (0 + m + 1) g)).val =
      Matrix.diagonal (Fin.cons (g.val 0 0) fun _ => 1) := by
  ext i j
  change appendIdentity 0 (0 + m + 1) g (Fin.cast (by omega) i) (Fin.cast (by omega) j) = _
  rw [appendIdentity_entry]
  simp only [Fin.val_cast, Matrix.diagonal_apply]
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
      rw [dite_eq_left (by simp), dite_eq_right (by simp), ite_eq_right (Fin.succ_ne_zero j).symm]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      rw [dite_eq_right (by simp), ite_eq_right (by rw [Fin.cast_inj]; exact Fin.succ_ne_zero i),
        ite_eq_right (Fin.succ_ne_zero i)]
    | succ j =>
      rw [dite_eq_right (by simp)]
      by_cases hij : i = j
      · subst hij
        simp
      · rw [ite_eq_right (by rw [Fin.cast_inj]; exact fun h => hij (Fin.succ_injective _ h)),
          ite_eq_right (fun h => hij (Fin.succ_injective _ h))]

omit [TopologicalSpace F] in
/-- `rankOneEmbedding m g = diag(det g, 1, …, 1)` is the diagonal matrix with entries
`g₀₀, 1, …, 1`. -/
theorem rankOneEmbedding_val (m : ℕ) (g : Langlands.GeneralLinear (0 + 1) F) :
    (rankOneEmbedding m g).val = Matrix.diagonal (Fin.cons (g.val 0 0) fun _ => 1) := by
  rw [rankOneEmbedding, Iwasawa.diagonalUnits_val]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero =>
    rw [Fin.cons_zero, Fin.cons_zero, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_fin_one]
  | succ i => simp

omit [TopologicalSpace F] in
/-- The unequal-rank block inclusion with no rectangular rows, followed by the
identity relabelling `characterPairRank m`, is `rankOneEmbedding m`. -/
theorem characterPairRank_appendIdentity (m : ℕ) (g : Langlands.GeneralLinear (0 + 1) F) :
    characterPairRank m (appendIdentity 0 (0 + m + 1) g) = rankOneEmbedding m g :=
  Units.ext ((characterPairRank_appendIdentity_val m g).trans (rankOneEmbedding_val m g).symm)

end Reindex

section Integrand

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Scaling the model vector scales the rank-one model integrand. -/
theorem rankOneModelIntegrand_smul (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {m : ℕ} (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V)
    (ℓ : glFunctionals ψ (m + 1) σ) (c : ℂ)
    (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) (s : ℂ) :
    rankOneModelIntegrand ψ abv σ ℓ (c • w) s =
      fun g => c * rankOneModelIntegrand ψ abv σ ℓ w s g := by
  funext g
  change (c • glModelFunction ψ (m + 1) σ ℓ w) (rankOneEmbedding m g) * _ = _
  rw [Pi.smul_apply, smul_eq_mul, rankOneModelIntegrand, mul_assoc]

/-- The unequal-rank integrand of the relabelled representation, for a rank-cast
Whittaker function and a constant inverse Whittaker function `c`, is `c` times the
rank-one integrand `W(diag(det g, 1, …, 1)) |det g|^(s - (m+1)/2)`. -/
theorem unequalRankIntegrand_whittakerRankCast (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (m : ℕ) (h : m + 1 = 0 + (0 + m + 1))
    (W : WhittakerFunctions ψ (m + 1)) (W' : InverseWhittakerFunctions ψ 0) (c : ℂ)
    (hc : ∀ g, W'.val g = c) (s : ℂ) (x : Matrix (Fin 0) (Fin (0 + 1)) F)
    (g : Langlands.GeneralLinear (0 + 1) F) :
    unequalRankIntegrand ψ abv 0 m (InducedTailIntermediate.whittakerRankCast ψ h W) W' s x
        (Quotient.mk _ g) =
      c * (W.val (rankOneEmbedding m g) *
        determinantWeight abv g (s - ((m + 1 : ℕ) : ℂ) / 2)) := by
  rw [unequalRankIntegrand_mk, unequalRankMatrix_zero_rows,
    InducedTailIntermediate.whittakerRankCast_apply, hc]
  have hk : ((0 + m + 1 : ℕ) : ℂ) = ((m + 1 : ℕ) : ℂ) := by
    rw [Nat.zero_add]
  rw [hk]
  change W.val (characterPairRank m (appendIdentity 0 (0 + m + 1) g)) * c * _ = _
  rw [characterPairRank_appendIdentity]
  ring

end Integrand

section Comparison

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [MeasurableSpace (Langlands.GeneralLinear (0 + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (0 + 1) F)]
  [MeasurableSpace (upperUnipotent (0 + 1) F)] [BorelSpace (upperUnipotent (0 + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- For `σ` of Whittaker type on `GL_(m+2)` with a nonzero standard functional `ℓ`,
the rank-one character zeta values of `σ × 1` are exactly the reduced values
`rankOneModelValues` over the coefficient model of `ℓ`, integrated against
`generalLinearHaar F 0`, for every compatible quotient measure. -/
theorem characterZetaValues_one_succ_eq (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {m : ℕ}
    {σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V}
    (hσ : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) σ)
    (ℓ : glFunctionals ψ (m + 1) σ) (hℓ : ℓ.val ≠ 0)
    (μ : Measure (LeftUnipotentQuotient 0 F))
    (hμ : IsCompatible (upperUnipotent (0 + 1) F) (generalLinearHaar F 0)
      (unipotentHaar F 0) μ) :
    characterZetaValues q ψ abv μ (1 : Fˣ →* ℂˣ) (m + 1) σ =
      rankOneModelValues q ψ abv (generalLinearHaar F 0) σ ℓ := by
  obtain rfl := eq_rankOneQuotientHaar_of_isCompatible F μ hμ
  let _ : MeasurableSpace (Matrix (Fin 0) (Fin (0 + 1)) F) := ⊤
  let _ : Unique (Matrix (Fin 0) (Fin (0 + 1)) F) := Pi.uniqueOfIsEmpty _
  have hdisc : DiscreteMeasurableSpace (Matrix (Fin 0) (Fin (0 + 1)) F) :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hN : 0 + (0 + m + 1) = m + 1 := by omega
  have hrank : characterPairRank (F := F) m = reindex (finCongr (congrArg (· + 1) hN)) := rfl
  -- Convergence and value of the packaged integral, for a rank-cast Whittaker function
  -- and a constant inverse Whittaker function.
  have hconv : ∀ (W : WhittakerFunctions ψ (m + 1)) (W' : InverseWhittakerFunctions ψ 0)
      (c : ℂ), (∀ g, W'.val g = c) → ∀ s : ℂ,
      UnequalRankConverges ψ abv 0 m (rankOneQuotientHaar F) (Measure.dirac 0)
          (InducedTailIntermediate.whittakerRankCast ψ hN.symm W) W' s ↔
        Integrable (fun g => c * (W.val (rankOneEmbedding m g) *
          determinantWeight abv g (s - ((m + 1 : ℕ) : ℂ) / 2))) (generalLinearHaar F 0) := by
    intro W W' c hc s
    rw [UnequalRankConverges, integrable_prod_dirac_iff]
    refine (integrable_map_equiv rankOneQuotientHomeomorph.symm.toMeasurableEquiv _).trans ?_
    refine integrable_congr (Filter.Eventually.of_forall fun g => ?_)
    exact unequalRankIntegrand_whittakerRankCast ψ abv m hN.symm W W' c hc s 0 g
  have hint : ∀ (W : WhittakerFunctions ψ (m + 1)) (W' : InverseWhittakerFunctions ψ 0)
      (c : ℂ), (∀ g, W'.val g = c) →
      unequalRankIntegral ψ abv 0 m (rankOneQuotientHaar F) (Measure.dirac 0)
          (InducedTailIntermediate.whittakerRankCast ψ hN.symm W) W' =
        fun s => ∫ g, c * (W.val (rankOneEmbedding m g) *
          determinantWeight abv g (s - ((m + 1 : ℕ) : ℂ) / 2)) ∂generalLinearHaar F 0 := by
    intro W W' c hc
    funext s
    rw [unequalRankIntegral]
    simp only [integral_dirac]
    rw [integral_rankOneQuotientHaar]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
      unequalRankIntegrand_whittakerRankCast ψ abv m hN.symm W W' c hc s 0 g)
  have hset : whittakerSet ψ (0 + (0 + m + 1)) (σ.comp (characterPairRank m).toMonoidHom) =
      InducedTailIntermediate.whittakerRankCast ψ hN.symm ''
        (coefficientModel σ ℓ).toSubmodule := by
    rw [hrank, whittakerSet_comp_reindex ψ hN σ, whittakerSet_eq_of_isOfWhittakerType hσ ℓ hℓ]
  ext R
  change R ∈ unequalRankValuesOf q ψ abv 0 m (rankOneQuotientHaar F) (Measure.dirac 0)
      (whittakerSet ψ (0 + (0 + m + 1)) (σ.comp (characterPairRank m).toMonoidHom))
      (inverseWhittakerSet ψ 0 (rankOneCharacter 1)) ↔ _
  rw [hset]
  constructor
  · rintro ⟨_, ⟨W, hW, rfl⟩, W', hW', ⟨a, ha⟩, hR⟩
    obtain ⟨c, hc⟩ := (mem_inverseWhittakerSet_rankOneCharacter_one_iff ψ W').1 hW'
    let w₀ : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule := ⟨W, hW⟩
    refine ⟨c • w₀, ⟨a, fun s hs => ?_⟩, ?_⟩
    · rw [rankOneModelIntegrand_smul]
      exact (hconv W W' c hc s).1 (ha s hs)
    · rw [hint W W' c hc] at hR
      convert hR using 2 with s
      rw [rankOneModelIntegrand_smul]
      rfl
  · rintro ⟨w, ⟨a, ha⟩, hR⟩
    have h1 : ∀ g, (constInverseWhittaker ψ 1).val g = 1 := fun _ => rfl
    refine ⟨_, ⟨w.val, w.property, rfl⟩, constInverseWhittaker ψ 1,
      (mem_inverseWhittakerSet_rankOneCharacter_one_iff ψ _).2 ⟨1, h1⟩,
      ⟨a, fun s hs => ?_⟩, ?_⟩
    · rw [hconv w.val _ 1 h1]
      simp only [one_mul]
      exact ha s hs
    · rw [hint w.val _ 1 h1]
      simp only [one_mul]
      exact hR

end Comparison

end Langlands.RankinSelberg
