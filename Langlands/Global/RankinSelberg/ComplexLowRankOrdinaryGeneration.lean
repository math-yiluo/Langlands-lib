import Langlands.Global.RankinSelberg.ComplexAdjacentRankOneGaussian
import Langlands.Global.RankinSelberg.ComplexGodementContinuedModel
import Langlands.Global.RankinSelberg.ComplexLocalPolynomialGaussian
import Langlands.Global.RankinSelberg.ComplexOrdinaryStandardGeneration
import Langlands.Global.RankinSelberg.ComplexRankZeroGaussianGeneration

/-! # Equal and adjacent complex ordinary generation with smaller rank one -/

noncomputable section

open MeasureTheory Set MvPolynomial
open scoped Matrix Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ArchimedeanLocal ComplexAdjacentUnfolding
open ComplexCompactProfileFamily (characterList)
open ComplexGodement (characterList_cons addedCharacter retainedCharacters translateTest)
open ComplexGodementContinuedModel (complexGodementContinuedModel)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementColumnProduct (columnProduct columnProduct_apply leadingColumns lastColumn)
open ComplexJacquet (ComplexMatrixPolynomialIndex complexMatrixPolynomialCoordinates
  complexMatrixPolynomialGaussian complexLocalPolynomialGaussian complexUnitaryInverseTranspose)
open ComplexJacquetContinuation (complexJacquetNonzero continuedJacquet)
open ComplexJacquetMultiplicityOne (exists_characterList complexJacquetMultiplicityOne)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.LocalFactor.ComplexTate (gaussian)
open Langlands.GodementJacquet (complexSelfDualMeasure_neg_scale)
open ComplexCharacterChange (changeQuotientMeasure complexUnequalFiniteSum_scale)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

local notation "G" => Langlands.GeneralLinear 1 ℂ
local notation "G₂" => Langlands.GeneralLinear 2 ℂ
local notation "Rect" => Matrix (Fin 1) (Fin 2) ℂ
local notation "Column" => Matrix (Fin 2) (Fin 1) ℂ
local notation "Vec" => Fin 1 → ℂ
local notation "Kc" => unitaryCompact ℂ 2
local notation "gap" => Nat.lt_succ_self 0

private theorem gaussian_neg (k : ℤ) (z : ℂ) :
    gaussian k (-z) = (-1 : ℂ) ^ k.natAbs * gaussian k z := by
  unfold gaussian
  simp only [map_neg, norm_neg]
  split_ifs
  · rw [show -(starRingEnd ℂ z) = (-1 : ℂ) * starRingEnd ℂ z by ring, mul_pow]
    ring
  · rw [show -z = (-1 : ℂ) * z by ring, mul_pow]
    ring

private theorem splitRowTransform_neg_one (φ : 𝓢(Vec, ℂ)) (z : ℂ) :
    splitRowTransform (-1 : ℂˣ) φ (fun _ => z) = splitRowTransform (1 : ℂˣ) φ (fun _ => -z) := by
  rw [splitRowTransform_apply, splitRowTransform_apply, complexSelfDualMeasure_neg_scale]
  unfold splitRowPlus
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    complexScaledCharacter_apply, Units.val_neg, Units.val_one, one_mul,
    neg_mul, Finset.sum_neg_distrib]

private def angularColumn (k : ℤ) (i : Fin 2) : MvPolynomial (ComplexMatrixPolynomialIndex 2 1) ℂ :=
  (if 0 ≤ k then X (.inr (i, 0)) else X (.inl (i, 0))) ^ k.natAbs

private theorem eval_angularColumn (k : ℤ) (i : Fin 2) (Y : Column) :
    aeval (complexMatrixPolynomialCoordinates Y) (angularColumn k i) =
      if 0 ≤ k then starRingEnd ℂ (Y i 0) ^ k.natAbs else Y i 0 ^ k.natAbs := by
  by_cases hk : 0 ≤ k <;> simp [angularColumn, hk, complexMatrixPolynomialCoordinates]

private theorem pureTateTest_finite (j k : ℤ) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun u : Kc =>
      translateTest u.val (columnProduct (rankOneSquareGaussian j) (rankOneRowGaussian k)))) := by
  let t : ℝ := 2 * Real.pi
  let P := C ((Real.pi : ℂ)⁻¹ * (Real.pi : ℂ)⁻¹) * angularColumn j 0 * angularColumn k 1
  let F : Column → ℂ := complexMatrixPolynomialGaussian t P
  have he (X : Rect) : columnProduct (rankOneSquareGaussian j) (rankOneRowGaussian k) X = F Xᵀ := by
    rw [columnProduct_apply, rankOneSquareGaussian_apply, rankOneRowGaussian_apply]
    have hx : (leadingColumns X) 0 0 = X 0 0 := rfl
    have hy : (lastColumn X) 0 = X 0 1 := rfl
    rw [hx, hy]
    change gaussian j (X 0 0) * gaussian k (X 0 1) =
      aeval (complexMatrixPolynomialCoordinates (Xᵀ)) P *
        Complex.exp (-((t * (∑ i : Fin 2, ∑ l : Fin 1, ‖Xᵀ i l‖ ^ 2) : ℝ) : ℂ))
    simp only [P, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, eval_angularColumn,
      Matrix.transpose_apply, Fin.sum_univ_one, Fin.sum_univ_two]
    simp only [gaussian]
    have hExp : Complex.exp (-((t * (‖X 0 0‖ ^ 2 + ‖X 0 1‖ ^ 2) : ℝ) : ℂ)) =
        Complex.exp (-2 * (Real.pi : ℂ) * (‖X 0 0‖ : ℂ) ^ 2) *
          Complex.exp (-2 * (Real.pi : ℂ) * (‖X 0 1‖ : ℂ) ^ 2) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast [t]
      ring
    rw [hExp]
    split_ifs <;> ring
  let A := Submodule.span ℂ (range fun u : Kc => fun Y : Column => F (u.val⁻¹.val * Y))
  let : FiniteDimensional ℂ A := (complexLocalPolynomialGaussian (m := 2) (n := 1) t P).2.1
  let transposePullback : (Column → ℂ) →ₗ[ℂ] (Rect → ℂ) := LinearMap.funLeft ℂ ℂ Matrix.transpose
  apply Submodule.finiteDimensional_of_le (S₂ := A.map transposePullback)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨u, rfl⟩
  let v := complexUnitaryInverseTranspose 2 u
  refine ⟨fun Y => F (v.val⁻¹.val * Y), Submodule.subset_span ⟨v, rfl⟩, ?_⟩
  have hv : v.val⁻¹.val = u.val.valᵀ := by
    change ((inverseTranspose 2 ℂ u.val)⁻¹).val = _
    rw [← map_inv]
    rfl
  funext X
  change F (v.val⁻¹.val * Xᵀ) = columnProduct (rankOneSquareGaussian j) (rankOneRowGaussian k) (X * u.val.val)
  rw [he, Matrix.transpose_mul, hv]

private theorem nonzero_rankOneWhittaker (c : ComplexCharacterData) (a : ℂˣ) :
    ∃ W : complexWhittakerModel 0 [c] a, W.val ≠ 0 := by
  obtain ⟨l, p, hp⟩ := exists_characterList [c] (by simp : [c].length = 1)
  rw [← hp]
  let μ := complexSelfDualMeasure (-a)
  obtain ⟨f, hf⟩ := complexJacquetNonzero 0 μ (-a) l p
  have hR := (complexJacquetMultiplicityOne 0 μ (-a) l p).2
  rw [neg_neg] at hR
  refine ⟨⟨continuedJacquet μ (-a) l p f, hR.symm ▸ ⟨f, rfl⟩⟩, ?_⟩
  intro h
  exact hf (congrFun h 1)

private theorem rankOneQuotient_sFinite (D : ComplexQuotientMeasureData 0) : SFinite D.measure := by
  let e := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) 1
  let : SecondCountableTopology G := e.secondCountableTopology
  let : LocallyCompactSpace G := e.locallyCompactSpace
  have : SigmaCompactSpace (Langlands.RankinSelberg.LeftUnipotentQuotient 0 ℂ) := by
    have h := Langlands.QuotientIntegration.leftQuotient_isOpenQuotientMap (Langlands.GeneralLinear.upperUnipotent 1 ℂ)
    apply isSigmaCompact_univ_iff.mp
    rw [← range_eq_univ.mpr h.surjective]
    exact isSigmaCompact_range h.continuous
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  infer_instance

private theorem adjacent_standard (D : ComplexQuotientMeasureData 0) (d c e : ComplexCharacterData)
    (hI : IsIrreducibleGKModule (complexStandardRep 2 [d, c]) (complexStandardLie 2 [d, c])) :
    HasFiniteOrdinaryNormalizationSum (complexOrdinaryUnequalTest gap [d, c] [e] 1 D)
      (complexPairLFactor [d, c] [e]) := by
  let a : ℂˣ := -1
  obtain ⟨U, hU⟩ := nonzero_rankOneWhittaker c (-a)
  obtain ⟨V, hV⟩ := nonzero_rankOneWhittaker e a
  let j := (d.mul e).weight
  let k := (c.mul e).weight
  let φ := rankOneRowGaussian (-k)
  let Φ := rankOneSquareGaussian j
  let Ψ := columnProduct Φ φ
  let C : ℂ := Complex.I ^ k.natAbs * (-1 : ℂ) ^ k.natAbs
  have hC : C ≠ 0 := mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  have hφ (z : ℂ) : splitRowTransform a φ (fun _ => z) = C * gaussian k z := by
    dsimp only [a, φ, C]
    rw [splitRowTransform_neg_one, splitRowTransform_one_rankOneRowGaussian,
      neg_neg, Int.natAbs_neg, gaussian_neg, mul_assoc]
  let : SFinite D.measure := rankOneQuotient_sFinite D
  obtain ⟨b, σ, hb, hZ⟩ := complexAdjacentRankOneGaussianProduct D a d c e U V hU hV φ C hC hφ
  let W (g : G₂) := continuedValue D.groupHaar (complexSelfDualMeasure a) d a (operatorToEntry Ψ) U.val g 0
  obtain ⟨l, p, hl⟩ := exists_characterList [d, c] (by simp : [d, c].length = 2)
  have hl' : addedCharacter l p :: retainedCharacters l p = [d, c] := (characterList_cons l p).symm.trans hl
  obtain ⟨hd, hc⟩ := List.cons.inj hl'
  have hI' : IsIrreducibleGKModule (complexStandardRep 2 (characterList l p))
      (complexStandardLie 2 (characterList l p)) := hl.symm ▸ hI
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.IsMulRightInvariant := complexAdjacent_groupHaar_rightInvariant D
  let U' : complexWhittakerModel 0 (retainedCharacters l p) (-a) := ⟨U.val, hc.symm ▸ U.2⟩
  have hW : W ∈ complexWhittakerModel 1 [d, c] 1 := by
    have hm := complexGodementContinuedModel (r := 0) D.groupHaar (complexSelfDualMeasure a) a l p hI'
      Ψ (pureTateTest_finite j (-k)) U'
    simpa only [hd, hl, U', W, a, neg_neg] using hm
  let W' : complexWhittakerModel 1 [d, c] 1 := b⁻¹ • ⟨W, hW⟩
  let i : complexWhittakerModel 1 [d, c] 1 × complexWhittakerModel 0 [e] (-1) := (W', V)
  refine ⟨1, fun _ => i, fun _ => ⟨fun _ => 1, fun _ _ => analyticAt_const, ⟨σ, fun s hs => ?_⟩⟩,
    fun _ => Fin.sum_univ_one _⟩
  change complexUnequalIntegral gap D (b⁻¹ • W) V.val s = _
  have hInt : complexUnequalIntegral gap D (b⁻¹ • W) V.val s = b⁻¹ * complexUnequalIntegral gap D W V.val s := by
    simp only [complexUnequalIntegral, ArchimedeanLocal.unequalIntegral, ArchimedeanLocal.unequalIntegrand,
      Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  rw [hInt, hZ s hs, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]

/-- The full ordinary generation conclusions for the complex pairs `GL₂ × GL₁` and `GL₁ × GL₁`. -/
def ComplexLowRankOrdinaryGenerationStatement : Prop :=
  (∀ (d e : List ComplexCharacterData), d.length = 2 → e.length = 1 →
    IsIrreducibleGKModule (complexStandardRep 2 d) (complexStandardLie 2 d) →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData 0),
      HasCoveringOrdinaryNormalizations (complexOrdinaryUnequalTest gap d e a D) (complexPairLFactor d e) ∧
      ((a = 1 ∨ a = -1) → HasFiniteOrdinaryNormalizationSum
        (complexOrdinaryUnequalTest gap d e a D) (complexPairLFactor d e))) ∧
  (∀ (d e : List ComplexCharacterData), d.length = 1 → e.length = 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData 0),
      HasFiniteOrdinaryNormalizationSum (complexOrdinaryEqualTest 0 d e a D) (complexPairLFactor d e))

theorem complexLowRankOrdinaryGeneration : ComplexLowRankOrdinaryGenerationStatement := by
  constructor
  · intro d e hd he hI a D
    obtain ⟨d₀, ds, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < d.length)
    have hds : ds.length = 1 := by simpa only [List.length_cons, Nat.succ_inj] using hd
    obtain ⟨d₁, rfl⟩ := List.length_eq_one_iff.mp hds
    obtain ⟨e₀, rfl⟩ := List.length_eq_one_iff.mp he
    have hStd := adjacent_standard (changeQuotientMeasure a D) d₀ d₁ e₀ hI
    refine ⟨complexUnequalCoverage_of_standard gap rfl rfl a D hStd.covering, ?_⟩
    intro ha
    have hn : ‖(a : ℂ)‖ = 1 := by rcases ha with rfl | rfl <;> simp
    exact complexUnequalFiniteSum_scale gap a hn D hStd
  · intro d e hd he a D
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hd
    obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp he
    obtain ⟨W, hW⟩ := nonzero_rankOneWhittaker c a
    obtain ⟨V, hV⟩ := nonzero_rankOneWhittaker c' (-a)
    have hW' : complexWhittakerModel 0 [c] a ≠ ⊥ := fun h => hW ((Submodule.mem_bot ℂ).mp (h ▸ W.2))
    have hV' : complexWhittakerModel 0 [c'] (-a) ≠ ⊥ := fun h => hV ((Submodule.mem_bot ℂ).mp (h ▸ V.2))
    obtain ⟨⟨U, U', Φ⟩, N, hN⟩ := (ComplexRankZero.complexRankZeroGaussianGeneration
      [c] [c'] rfl rfl a D).2 hW' hV'
    exact ⟨1, fun _ => (U, U', Φ.val), fun _ => N, fun s => by simpa only [Fin.sum_univ_one] using hN s⟩

end Langlands.Global.RankinSelbergGlobal
