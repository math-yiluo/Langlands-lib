import Langlands.Group.GL.ReindexCongr
import Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement
import Langlands.Representation.RankinSelberg.EqualRankLastRowReductionProof
import Langlands.Representation.Whittaker.TwoBlockExtensionAssemblyProof
import Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityProof
import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.Representation.Whittaker.CoefficientRightStabilizer
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.RankinSelberg.PairLFactor
import Langlands.Representation.RankinSelberg.RankOneExtensionSpanTransfer
import Langlands.Representation.Induction.BlockEquivalence

/-!
# Equal-rank rank-one extension Laurent-span comparison: proof
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW uV' uU

section CharacterChange

/-- Equal characters give the same coefficient functions. -/
theorem exists_mem_coefficientModel_of_character_eq {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {N : Subgroup G} {θ θ' : N →* ℂˣ} (h : θ = θ') {ρ : Representation ℂ G V}
    (ℓ : functionals N θ ρ) (f : (equivariantFunctions N θ).toSubmodule)
    (hf : f ∈ (coefficientModel ρ ℓ).toSubmodule) :
    ∃ (ℓ' : functionals N θ' ρ) (f' : (equivariantFunctions N θ').toSubmodule),
      f' ∈ (coefficientModel ρ ℓ').toSubmodule ∧ f'.val = f.val := by
  subst h
  exact ⟨ℓ, f, hf, rfl⟩

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A Whittaker function for `ψ⁻¹ = ψ.scale (-1)` is an inverse Whittaker
function for `ψ`. -/
theorem exists_inverseWhittakerSet_of_scale_neg_one (ψ : UnitaryAdditiveCharacter F)
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {W : WhittakerFunctions (ψ.scale (-1)) n} (hW : W ∈ whittakerSet (ψ.scale (-1)) n π) :
    ∃ W' ∈ inverseWhittakerSet ψ n π, W'.val = W.val := by
  obtain ⟨ℓ, hℓ⟩ := hW
  obtain ⟨ℓ', f', hf', hval⟩ :=
    exists_mem_coefficientModel_of_character_eq (standardCharacter_scale_neg_one ψ n) ℓ W hℓ
  exact ⟨f', ⟨ℓ', hf'⟩, hval⟩

/-- An inverse Whittaker function for `ψ` is a Whittaker function for
`ψ.scale (-1)`. -/
theorem exists_whittakerSet_scale_neg_one (ψ : UnitaryAdditiveCharacter F)
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {W : InverseWhittakerFunctions ψ n} (hW : W ∈ inverseWhittakerSet ψ n π) :
    ∃ W' ∈ whittakerSet (ψ.scale (-1)) n π, W'.val = W.val := by
  obtain ⟨ℓ, hℓ⟩ := hW
  obtain ⟨ℓ', f', hf', hval⟩ :=
    exists_mem_coefficientModel_of_character_eq (standardCharacter_scale_neg_one ψ n).symm
      ℓ W hℓ
  exact ⟨f', ⟨ℓ', hf'⟩, hval⟩

end CharacterChange

section Restriction

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- Restriction of an inverse Whittaker function along `h ↦ diag(h, 1)`. -/
def corankOneRestrict (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (W' : InverseWhittakerFunctions ψ (n + 1)) : InverseWhittakerFunctions ψ n :=
  ⟨fun h => W'.val (rankInclusion 1 h), by
    intro u g
    change W'.val (rankInclusion 1 (u.val * g)) =
      ((inverseStandardCharacter ψ n u : ℂˣ) : ℂ) * W'.val (rankInclusion 1 g)
    rw [map_mul]
    change W'.val ((corankOneUnipotent u).val * rankInclusion 1 g) = _
    rw [W'.property]
    change (((standardCharacter ψ (n + 1) (corankOneUnipotent u))⁻¹ : ℂˣ) : ℂ) * _ = _
    rw [corankOne_standardCharacter]
    rfl⟩

@[simp] theorem corankOneRestrict_val (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (W' : InverseWhittakerFunctions ψ (n + 1)) (h : Langlands.GeneralLinear (n + 1) F) :
    (corankOneRestrict ψ W').val h = W'.val (rankInclusion 1 h) := rfl

end Restriction

section Convergence

/-- A product with a Dirac measure is a pushforward, with no finiteness
assumption on the first factor. -/
theorem prod_dirac_eq_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (y : β) : μ.prod (Measure.dirac y) = μ.map (fun x => (x, y)) := by
  rw [Measure.prod_def]
  simp_rw [Measure.map_dirac' measurable_prodMk_left]
  exact Measure.bind_dirac_eq_map μ measurable_prodMk_right

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]

/-- The block `j = k = 0` convergence with the unit-mass rectangular measure is
corank-one convergence. -/
theorem corankOneConverges_of_unequalRankConverges_zero_zero
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (h : UnequalRankConverges ψ abv 0 0 μ (Measure.dirac 0) W W' s) :
    CorankOneConverges ψ abv μ W W' s := by
  unfold UnequalRankConverges at h
  rw [prod_dirac_eq_map] at h
  have h' := h.comp_measurable (measurable_prodMk_right (m := inferInstance))
  unfold CorankOneConverges
  refine h'.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Function.comp_apply, unequalRankIntegrand_zero_zero]

end Convergence

section Weight

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The half power of the determinant combines with the corank-one weight. -/
theorem half_mul_determinantWeight {n : ℕ} (g : Langlands.GeneralLinear (n + 1) F.Carrier)
    (s : ℂ) :
    (Real.rpow (T.normalizedAbs (Matrix.det g.val)) ((1 : ℝ) / 2) : ℂ) *
        determinantWeight (normalizedAbsoluteValue T) g (s - 1 / 2 - 1 / 2) =
      determinantWeight (normalizedAbsoluteValue T) g (s - 1 / 2) := by
  have hdet : Matrix.det g.val ≠ 0 := g.isUnit.map Matrix.detMonoidHom |>.ne_zero
  have hpos : 0 < T.normalizedAbs (Matrix.det g.val) := by
    rcases (T.normalizedAbs_nonneg (Matrix.det g.val)).lt_or_eq with h | h
    · exact h
    · exact absurd ((T.normalizedAbs_eq_zero_iff _).1 h.symm) hdet
  set a := T.normalizedAbs (Matrix.det g.val) with ha
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  unfold determinantWeight
  change ((a ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * (a : ℂ) ^ (s - 1 / 2 - 1 / 2) = (a : ℂ) ^ (s - 1 / 2)
  rw [Complex.ofReal_cpow hpos.le, ← Complex.cpow_add _ _ ha0]
  congr 1
  push_cast
  ring

end Weight

section Transport

/-- Replacing the second member of a pair family by an equivalent representation,
blockwise. -/
def pairFamilyEquivRight {R : Type*} [CommRing R] {a b : ℕ} {U : Type uW}
    [AddCommGroup U] [Module ℂ U] {U₂ U₂' : Type uW} [AddCommGroup U₂] [Module ℂ U₂]
    [AddCommGroup U₂'] [Module ℂ U₂']
    (ρ₁ : Representation ℂ (Langlands.GeneralLinear a R) U)
    {ρ₂ : Representation ℂ (Langlands.GeneralLinear b R) U₂}
    {ρ₂' : Representation ℂ (Langlands.GeneralLinear b R) U₂'} (e : ρ₂.Equiv ρ₂') :
    ∀ i : Fin 2, (Shahidi.pairFamily ρ₁ ρ₂ i).Equiv (Shahidi.pairFamily ρ₁ ρ₂' i)
  | 0 => Representation.Equiv.refl ρ₁
  | 1 => e

/-- Conjugation by `ULift.moduleEquiv.symm` is equivalent to the original
representation. -/
def conjULiftEquiv {G : Type*} [Monoid G] {U : Type uW} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G U) :
    ρ.Equiv (((ULift.moduleEquiv : ULift.{uV'} U ≃ₗ[ℂ] U).symm.conjRingEquiv.toMonoidHom).comp
      ρ) :=
  Representation.Equiv.mk (ULift.moduleEquiv.symm) fun g => by
    ext v
    rfl

end Transport

section Extension

variable {p : ℕ} [Fact p.Prime]

/-- JPSS Proposition 9.1 with a rank-one first block, read in the
inverse-character model of the induction of the unlifted pair `(χ, σ₁)`. -/
theorem exists_inverseWhittaker_twoBlockExtension
    (h91 : Whittaker.TwoBlockWhittakerExtensionStatement.{uF, 0, uW})
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (t : ℕ) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ₁) :
    letI := F.canonicalTopologicalData.topology
    ∀ W₁ ∈ inverseWhittakerSet ψ t σ₁, ∀ Φ₀ : SchwartzBruhat (Fin (t + 1) → F.Carrier),
      ∃ W' ∈ inverseWhittakerSet ψ (1 + t) (F.canonicalNormalizedProductInduced
          (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
          (Shahidi.pairFamily
            ((ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
              (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) :
                Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) (ULift.{uW} ℂ))
            σ₁)),
        ∀ g : Langlands.GeneralLinear (t + 1) F.Carrier,
          W'.val (GeneralLinear.reindex (finCongr (by omega : t + 1 + 1 = 1 + t + 1))
              (rankInclusion 1 g)) =
            W₁.val g * Φ₀ (lastRow g) *
              (Real.rpow (F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val))
                ((1 : ℝ) / 2) : ℂ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro W₁ hW₁ Φ₀
  have hσ' : IsOfWhittakerType t (standardCharacter (ψ.scale (-1)) t) σ₁ := by
    rw [standardCharacter_scale_neg_one]
    exact (isOfWhittakerType_standard_iff_inverse ψ σ₁).1 hσ
  have hχ := rankOneCharacter_isOfWhittakerType p F (ψ.scale (-1)) χ
  obtain ⟨W₂, hW₂, hW₂val⟩ := exists_whittakerSet_scale_neg_one ψ hW₁
  obtain ⟨Wξ, hWξ, hWξval⟩ := h91 p F (ψ.scale (-1)) 0 t
    (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) σ₁ hχ hσ' W₂ hW₂ Φ₀
  obtain ⟨W', hW', hW'val⟩ := exists_inverseWhittakerSet_of_scale_neg_one ψ hWξ
  refine ⟨W', (Set.ext_iff.1 (inverseWhittakerSet_eq_of_equiv ψ
    (F.canonicalTopologicalData.normalizedProductInducedEquiv
      (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
      (pairFamilyEquivRight _ (conjULiftEquiv.{uW, 0} σ₁)))) W').2 hW', fun g => ?_⟩
  refine (congrFun hW'val _).trans ((hWξval g).trans ?_)
  rw [hW₂val]
  norm_num

end Extension

section Core

variable {p : ℕ} [Fact p.Prime]

/-- The span comparison at a general induced rank `m = t + 1`, from the
last-row reduction, the zero-row cutoff and a supplied extension of inverse
Whittaker functions of `σ₁` to inverse Whittaker functions of `I`. -/
theorem equalRankSpanComparison_core (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    (t m : ℕ) (hm : t + 1 = m)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {U : Type uU} [AddCommGroup U] [Module ℂ U]
    (π : Representation ℂ (Langlands.GeneralLinear (t + 2) F.Carrier) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (I : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) U)
    (hC : EqualRankLastRowReductionStatement F F.canonicalTopologicalData t)
    (hπ : letI := F.canonicalTopologicalData.topology; IsSmooth π)
    (hI : letI := F.canonicalTopologicalData.topology; IsSmooth I)
    (hext : letI := F.canonicalTopologicalData.topology
      ∀ W₁ ∈ inverseWhittakerSet ψ t σ₁, ∀ Φ₀ : SchwartzBruhat (Fin (t + 1) → F.Carrier),
        ∃ W' ∈ inverseWhittakerSet ψ m I, ∀ g : Langlands.GeneralLinear (t + 1) F.Carrier,
          W'.val (GeneralLinear.reindex (finCongr (by omega : t + 1 + 1 = m + 1))
              (rankInclusion 1 g)) =
            W₁.val g * Φ₀ (lastRow g) *
              (Real.rpow (F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val))
                ((1 : ℝ) / 2) : ℂ)) :
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
    letI := borel (Langlands.GeneralLinear (m + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (m + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (m + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (m + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient m F.Carrier)
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)],
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier m)],
    ∀ (μbase : Measure (LeftUnipotentQuotient t F.Carrier))
      (μind : Measure (LeftUnipotentQuotient m F.Carrier)),
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μbase →
      IsCompatible (upperUnipotent (m + 1) F.Carrier)
        (generalLinearHaar F.Carrier m) (unipotentHaar F.Carrier m) μind →
        zetaSpan (unequalRankZetaValuesAt (r := t + 1) (n := t) 0 0 rfl
          F.canonicalTopologicalData.residueCardinality ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) μbase
          (rectangularMeasure ν 0 (t + 1)) π σ₁) ≤
        zetaSpan (equalRankZetaValues (n := m)
          F.canonicalTopologicalData.residueCardinality ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) μind
          (hm ▸ π : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) V) I) := by
  subst hm
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  let := borel (Langlands.GeneralLinear (t + 1 + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (t + 1 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1 + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (t + 1 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (t + 1) F.Carrier)
  intro _ _ μbase μind hbase hind
  refine zetaSpan_le_of_forall_exists_const_mul fun R hR => ?_
  obtain ⟨Wπ, ⟨ℓ, hℓ⟩, W₁, hW₁, ⟨a, ha⟩, hRc⟩ := hR
  obtain ⟨Φ₀, -, hcut⟩ := zeroRowLastRowCutoff p F F.canonicalTopologicalData t 0 ψ V π hπ ℓ
    ⟨Wπ, hℓ⟩
  obtain ⟨W', ⟨ℓ', hℓ'⟩, hW'val⟩ := hext W₁ hW₁ Φ₀
  simp only [reindex_finCongr_self] at hW'val
  obtain ⟨J, hJ, ⟨hJW, hJW'⟩, -⟩ := Whittaker.exists_compactOpen_glCoefficientRightStabilizer
    F F.canonicalTopologicalData (t + 1) ψ V U π I hπ hI ℓ ℓ' ⟨Wπ, hℓ⟩ ⟨W', hℓ'⟩
  obtain ⟨-, -, -, -, ⟨Φ, hΦ⟩, -⟩ := lastRowCompactOrbit F F.canonicalTopologicalData (t + 1) J hJ
  obtain ⟨c, hc, hcW⟩ := hC μind μbase hind hbase J hJ
  have hint : ∀ s : ℂ, corankOneIntegrand (n := t) ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) Wπ (corankOneRestrict ψ W')
        (s - 1 / 2) =
      corankOneIntegrand (n := t) ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        Wπ W₁ s := by
    intro s
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [corankOneIntegrand_mk, corankOneIntegrand_mk, corankOneRestrict_val, hW'val g,
        ← half_mul_determinantWeight F.canonicalTopologicalData g s]
      have hg : Wπ.val (rankInclusion 1 g) * Φ₀ (lastRow g) = Wπ.val (rankInclusion 1 g) :=
        hcut g
      calc _ = (Wπ.val (rankInclusion 1 g) * Φ₀ (lastRow g)) * W₁.val g *
            ((Real.rpow (F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val))
                ((1 : ℝ) / 2) : ℂ) *
              determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
                (s - 1 / 2 - 1 / 2)) := by ring
        _ = _ := by rw [hg]
  have hred := fun s => hcW ψ Wπ W' (corankOneRestrict ψ W') Φ hJW hJW' (fun _ => rfl) hΦ s
  refine ⟨(c : ℂ), Complex.ofReal_ne_zero.2 hc.ne', ?_⟩
  refine ⟨Wπ, ⟨ℓ, hℓ⟩, W', ⟨ℓ', hℓ'⟩, Φ, ⟨a, fun s hs => ?_⟩, ?_⟩
  · have h1 := ha s hs
    rw [rectangularMeasure_zero_rows] at h1
    have h2 := corankOneConverges_of_unequalRankConverges_zero_zero ψ _ μbase Wπ W₁ s h1
    refine (hred s).1.2 ?_
    unfold CorankOneConverges
    rw [hint s]
    exact h2
  · have heq : equalRankIntegral ψ (normalizedAbsoluteValue F.canonicalTopologicalData) μind
        Wπ W' Φ = fun s => (c : ℂ) * corankOneIntegral ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) μbase Wπ W₁ s := by
      funext s
      rw [(hred s).2]
      unfold corankOneIntegral
      rw [hint s]
    have hzero : unequalRankIntegral ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        0 0 μbase (Measure.dirac 0) Wπ W₁ =
        corankOneIntegral ψ (normalizedAbsoluteValue F.canonicalTopologicalData) μbase Wπ W₁ :=
      funext fun s => unequalRankIntegral_zero_zero ψ _ μbase Wπ W₁ s
    rw [heq]
    apply hasRationalContinuation_const_mul
    rw [rectangularMeasure_zero_rows, hzero] at hRc
    exact hRc

end Core

/-- The span comparison from JPSS Proposition 9.1 and the last-row reduction
`equalRankLastRowReduction`. -/
theorem equalRankRankOneExtensionSpanComparison_of
    (h91 : Whittaker.TwoBlockWhittakerExtensionStatement.{uF, 0, uW}) :
    EqualRankRankOneExtensionSpanComparisonStatement.{uF, uV, uW} := by
  intro p _ F ψ ν t V _ _ W _ _ π σ₁ χ hπ hσ χlift
  let := F.canonicalTopologicalData.topology
  intro _ _ μbase μind hbase hind hrn
  exact equalRankSpanComparison_core F ψ ν t (1 + t) hrn π σ₁
    (F.canonicalNormalizedProductInduced
      (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
      (Shahidi.pairFamily χlift σ₁))
    (equalRankLastRowReduction F F.canonicalTopologicalData t) hπ.1.1
    (F.canonicalTopologicalData.isSmooth_normalizedProductInduced _ _)
    (exists_inverseWhittaker_twoBlockExtension h91 F ψ t σ₁ χ hσ) μbase μind hbase hind

/-- The span comparison from p-adic row Fourier surjectivity, through the
published conditional proof `Whittaker.twoBlockWhittakerExtension_of_rowFourierSurjectivity`
of JPSS Proposition 9.1. -/
theorem equalRankRankOneExtensionSpanComparison_of_rowFourierSurjectivity
    (hsurj : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (d : ℕ),
      HarmonicAnalysis.PadicRowFourierSurjectivityStatement F F.canonicalTopologicalData d) :
    EqualRankRankOneExtensionSpanComparisonStatement.{uF, uV, uW} :=
  equalRankRankOneExtensionSpanComparison_of
    (Whittaker.twoBlockWhittakerExtension_of_rowFourierSurjectivity.{uF, 0, uW} hsurj)

/-- The equal-rank rank-one extension Laurent-span comparison, from the
published proof `HarmonicAnalysis.padicRowFourierSurjectivity`. -/
theorem equalRankRankOneExtensionSpanComparison :
    EqualRankRankOneExtensionSpanComparisonStatement.{uF, uV, uW} :=
  equalRankRankOneExtensionSpanComparison_of_rowFourierSurjectivity
    (fun _ _ F d =>
      HarmonicAnalysis.padicRowFourierSurjectivity F F.canonicalTopologicalData d)

end Langlands.RankinSelberg
