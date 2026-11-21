import Langlands.Global.RankinSelberg.ComplexAdjacentJacquetStripGrowth
import Langlands.Global.RankinSelberg.ComplexGodementGaussianColumnSplit

/-! # Complex adjacent-rank strip growth for Gaussian-polynomial tests -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry operatorToEntry_apply)
open ComplexGodement (characterWeight)
open ComplexGodementAddedCharacter (continuedValue rightTest rightTest_apply)
open ComplexGodementColumnChange (columnIntegral integrable_column iteratedKernel complexGodementColumnChange)
open ComplexGodementGaussianPolynomial (Coordinates gaussianPolynomial columnGaussianPolynomial
  complexGodementGaussianColumnSplit)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 2) ℂ
local notation "Kc" => unitaryCompact ℂ (r + 1)
local notation "N" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 2)) ℂ
local notation "Vec" => Fin (r + 1) → ℂ
local notation "gap" => Nat.lt_succ_self r
local notation "columnProd" => ComplexGodementColumnProduct.columnProduct

private def godementTest (D : ComplexQuotientMeasureData r) (a : ℂˣ)
    (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (U : G → ℂ) (g : G') : ℂ :=
  continuedValue D.groupHaar (complexSelfDualMeasure a) d a (operatorToEntry Φ) U g 0

private theorem godementTest_sum {l : ℕ} (D : ComplexQuotientMeasureData r) (a : ℂˣ)
    (d : ComplexCharacterData) (Φ : Fin l → 𝓢(Rect, ℂ)) {ds : List ComplexCharacterData}
    (U : complexWhittakerModel r ds (-a)) (g : G') :
    godementTest D a d (∑ j, Φ j) U.val g = ∑ j, godementTest D a d (Φ j) U.val g := by
  let μ := complexSelfDualMeasure a
  let χ := complexScaledCharacter a
  let Ψ (j : Fin l) := rightTest g (operatorToEntry (Φ j))
  let Ψsum := rightTest g (operatorToEntry (∑ j, Φ j))
  have hΨ (X : Rect) : Ψsum X = ∑ j, Ψ j X := by
    simp only [Ψsum, Ψ, rightTest_apply, operatorToEntry_apply, sum_apply]
  have hColumn (h : G) : columnIntegral χ μ Ψsum h = ∑ j, columnIntegral χ μ (Ψ j) h := by
    simp only [columnIntegral, hΨ, Finset.sum_mul]
    exact integral_finsetSum Finset.univ (fun j _ => integrable_column χ μ (Ψ j) h)
  let t : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2) + 0
  have hKernel : iteratedKernel χ μ d Ψsum U.val t =
      fun h => ∑ j, iteratedKernel χ μ d (Ψ j) U.val t h := by
    funext h
    simp only [iteratedKernel, hColumn, Finset.sum_mul]
  have hInt (j : Fin l) : Integrable (iteratedKernel χ μ d (Ψ j) U.val t) D.groupHaar :=
    (complexGodementColumnChange r ds (-a) D.groupHaar D.groupHaar_isHaar χ μ d
      (Ψ j) (partialSchwartz a μ (Ψ j)) (partialSchwartz_apply a μ (Ψ j)) U).1 t
  simp only [godementTest, continuedValue]
  change _ * (∫ h, iteratedKernel χ μ d Ψsum U.val t h ∂D.groupHaar) = _
  rw [hKernel, integral_finsetSum Finset.univ (fun j _ => hInt j), Finset.mul_sum]

private theorem gaussianTest_columnSplit (D : ComplexQuotientMeasureData r)
    (a : ℂˣ) (d : ComplexCharacterData) {ds : List ComplexCharacterData}
    (U : complexWhittakerModel r ds (-a)) (p : MvPolynomial (Coordinates (r + 1) (r + 2)) ℂ) :
    ∃ (l : ℕ) (Φ : Fin l → 𝓢(Mat, ℂ)) (φ : Fin l → 𝓢(Vec, ℂ)),
      (∀ g, godementTest D a d (gaussianPolynomial p) U.val g =
        ∑ j, godementTest D a d (columnProd (Φ j) (φ j)) U.val g) ∧
      ∀ j, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kc =>
        fun A : Mat => Φ j (k.val⁻¹.val * A))) := by
  obtain ⟨l, matPolys, colPolys, hsplit, hΦ⟩ := complexGodementGaussianColumnSplit (r + 1) p
  refine ⟨l, fun j => gaussianPolynomial (matPolys j), fun j => columnGaussianPolynomial (colPolys j),
    fun g => ?_, hΦ⟩
  rw [hsplit]
  exact godementTest_sum D a d _ U g

private theorem splitTest_rightIntegrable (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (a : ℂˣ) (d : ComplexCharacterData) {ds es : List ComplexCharacterData}
    (hds : ds.length = r + 1) (hes : es.length = r + 1)
    (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ))
    (U : complexWhittakerModel r ds (-a)) (V : complexWhittakerModel r es a) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexUnequalIntegrand gap (godementTest D a d (columnProd Φ φ) U.val)
        V.val s) D.measure := by
  let e := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (r + 1)
  let : LocallyCompactSpace G := e.locallyCompactSpace
  let : SecondCountableTopology G := e.secondCountableTopology
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.IsMulRightInvariant := complexAdjacent_groupHaar_rightInvariant D
  obtain ⟨σ, hσ⟩ := complexAdjacentSplitIntegrals D a d 0 Φ φ ds es hds hes U V
  let W := godementTest D a d (columnProd Φ φ) U.val
  let c : ℂ := d.character ((-1 : ℂˣ) ^ (r + 1))
  let ψ := splitRowTransform a φ
  have hW (g : G) : W (padGL (Nat.le_succ (r + 1)) g) =
      c * characterWeight d ((r : ℂ) / 2 + 1 / 2) (determinant g) *
        ∫ h, Φ (h * g).val * ψ (Langlands.RankinSelberg.lastRow h⁻¹) *
          U.val h⁻¹ * characterWeight d ((r : ℂ) / 2) (determinant h) ∂D.groupHaar := by
    simpa only [W, godementTest, c, ψ, splitRowTransform_apply, zero_add] using
      complexAdjacentSplitRestriction D.groupHaar (complexSelfDualMeasure a) d a Φ φ U.val 0 g
  refine ⟨σ, fun s hs => ?_⟩
  have hInt := (hσ s hs).1
  simp only [zero_add] at hInt
  exact (complexAdjacentAbsoluteUnfolding D D.groupHaar d ((r : ℂ) / 2) s Φ ψ (-a)
    U.val V.val W c (fun u g => complexWhittakerModel_left_equivariant U.2 u.val u.2 g)
    (fun u g => by simpa only [neg_neg] using
      complexWhittakerModel_left_equivariant V.2 u.val u.2 g) hW hInt).1

/-- The original ordinary kernel of a Gaussian-polynomial Godement value is
absolutely integrable on a right half-plane for any second model vector. -/
def ComplexAdjacentGaussianRightIntegrableStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (a : ℂˣ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData),
    ds.length = r + 1 → es.length = r + 1 →
  ∀ (U : complexWhittakerModel r ds (-a)) (V : complexWhittakerModel r es a)
    (p : MvPolynomial (Coordinates (r + 1) (r + 2)) ℂ),
    let W (g : G') := continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (gaussianPolynomial p)) U.val g 0
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (complexUnequalIntegrand gap W V s) D.measure

theorem complexAdjacentGaussian_rightIntegrable :
    ComplexAdjacentGaussianRightIntegrableStatement (r := r) := by
  intro D _ a d ds es hds hes U V p W
  obtain ⟨l, Φ, φ, hW, _⟩ := gaussianTest_columnSplit D a d U p
  choose σ hσ using fun j => splitTest_rightIntegrable D a d hds hes (Φ j) (φ j) U V
  obtain ⟨β, hβ⟩ := (Set.finite_range σ).bddAbove
  refine ⟨β, fun s hs => ?_⟩
  have hSplit (g : G') : W g = ∑ j, godementTest D a d (columnProd (Φ j) (φ j)) U.val g := hW g
  have hI : complexUnequalIntegrand gap W V s = fun q =>
      ∑ j, complexUnequalIntegrand gap (godementTest D a d (columnProd (Φ j) (φ j)) U.val)
        V s q := by
    funext q
    simp only [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, hSplit, Finset.sum_mul]
  rw [hI]
  exact integrable_finsetSum Finset.univ fun j _ =>
    hσ j s ((hβ (Set.mem_range_self j)).trans_lt hs)

private def HasIntegrableStripNormalization {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (L : ℂ → ℂ) (I : ℂ → X → ℂ) : Prop :=
  ∃ A : ℂ → ℂ, Differentiable ℂ A ∧ HasStripExponentialGrowth A ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (I s) μ ∧ (∫ x, I s x ∂μ) = A s * L s

private theorem finiteSumStripGrowth {l : ℕ} {A : Fin l → ℂ → ℂ}
    (hA : ∀ j, HasStripExponentialGrowth (A j)) :
    HasStripExponentialGrowth (fun s => ∑ j, A j s) := by
  intro a b
  choose C K T hC hK hB using fun j => hA j a b
  refine ⟨∑ j, C j, ∑ j, K j, ∑ j, |T j|, Finset.sum_nonneg (fun j _ => hC j),
    Finset.sum_nonneg (fun j _ => hK j), fun s ha hb hs => (norm_sum_le _ _).trans ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hTj : T j ≤ ∑ i, |T i| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (T i)) hj)
  have hKj : K j ≤ ∑ i, K i := Finset.single_le_sum (fun i _ => hK i) hj
  exact (hB j s ha hb (hTj.trans hs)).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKj (abs_nonneg _))) (hC j))

private theorem hasIntegrableStripNormalization_sum {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {L : ℂ → ℂ} {l : ℕ} {I : Fin l → ℂ → X → ℂ}
    (hI : ∀ j, HasIntegrableStripNormalization μ L (I j)) :
    HasIntegrableStripNormalization μ L (fun s x => ∑ j, I j s x) := by
  choose A hAd hAg σ hσ using hI
  obtain ⟨β, hβ⟩ := (Set.finite_range σ).bddAbove
  refine ⟨fun s => ∑ j, A j s, Differentiable.fun_sum (fun j _ => hAd j),
    finiteSumStripGrowth hAg, β, fun s hs => ?_⟩
  have hJ (j : Fin l) := hσ j s ((hβ (Set.mem_range_self j)).trans_lt hs)
  have hAbs : ∀ j ∈ (Finset.univ : Finset (Fin l)), Integrable (I j s) μ :=
    fun j _ => (hJ j).1
  refine ⟨integrable_finsetSum Finset.univ hAbs, ?_⟩
  rw [integral_finsetSum Finset.univ hAbs, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => (hJ j).2

/-- Standard Gaussian-polynomial Godement tests give adjacent ordinary continuations
of exponential strip growth once the smaller equal-rank tests have that property. -/
def ComplexAdjacentGaussianStripGrowthStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (κ : Measure Kc) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (es : Fin (r + 1) → ComplexCharacterData),
    ds.length = r + 1 →
  ∀ (U : complexWhittakerModel r ds (-a)) (V : complexWhittakerModel r (List.ofFn es) a)
    (p : MvPolynomial (Coordinates (r + 1) (r + 2)) ℂ),
    (∀ (V₁ : complexWhittakerModel r (List.ofFn es) a) (ψ : 𝓢(Vec, ℂ)),
      ∃ A : OrdinaryIntegralNormalization (complexEqualIntegral D U V₁ ψ)
        (fun s => ((complexPairLFactor ds (List.ofFn es)).denominator s)⁻¹),
        HasStripExponentialGrowth A.value) →
    let W (g : G') := continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (gaussianPolynomial p)) U.val g 0
    ∃ R : OrdinaryIntegralNormalization (complexUnequalIntegral gap D W V)
      (fun s => ((complexPairLFactor (d :: ds) (List.ofFn es)).denominator s)⁻¹),
      HasStripExponentialGrowth R.value ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (complexUnequalIntegrand gap W V s) D.measure

theorem complexAdjacentGaussianStripGrowth : ComplexAdjacentGaussianStripGrowthStatement (r := r) := by
  intro D _ κ _ _ a d ds es hds U V p hA W
  let L (s : ℂ) := ((complexPairLFactor (d :: ds) (List.ofFn es)).denominator s)⁻¹
  let I (v : G → ℂ) := complexUnequalIntegrand gap W v
  let P (v : G → ℂ) := HasIntegrableStripNormalization D.measure L (I v)
  obtain ⟨l, Φ, φ, hsplit, hΦ⟩ := gaussianTest_columnSplit D a d U p
  let W₁ (j : Fin l) := godementTest D a d (columnProd (Φ j) (φ j)) U.val
  have hW (g : G') : W g = ∑ j, W₁ j g := hsplit g
  have hI (v : G → ℂ) : I v = fun s q => ∑ j, complexUnequalIntegrand gap (W₁ j) v s q := by
    funext s q
    simp only [I, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, hW, Finset.sum_mul]
  have h0 : P 0 := by
    refine ⟨0, differentiable_const _, fun _ _ => ⟨0, 0, 0, le_rfl, le_rfl, by simp⟩,
      0, fun s _ => ?_⟩
    have hI0 : I 0 s = 0 := by
      funext q
      simp [I, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand]
    simp [hI0]
  have hadd (v v' : G → ℂ) (hv : P v) (hv' : P v') : P (v + v') := by
    let J : Fin 2 → ℂ → Q → ℂ := ![I v, I v']
    have hJ (j : Fin 2) : HasIntegrableStripNormalization D.measure L (J j) := by
      fin_cases j
      · exact hv
      · exact hv'
    have he : I (v + v') = fun s q => ∑ j, J j s q := by
      funext s q
      simp [I, J, Fin.sum_univ_two, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
        mul_add, add_mul]
    change HasIntegrableStripNormalization D.measure L (I (v + v'))
    rw [he]
    exact hasIntegrableStripNormalization_sum hJ
  have hImage (B : complexStandardKFinite (r + 1) (List.ofFn es) →ₗ[ℂ] (G → ℂ))
      (hB : IsComplexWhittakerIntertwiner r (List.ofFn es) a B)
      (f : complexStandardKFinite (r + 1) (List.ofFn es)) : P (B f) := by
    let v : complexWhittakerModel r (List.ofFn es) a :=
      ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
    change HasIntegrableStripNormalization D.measure L (I (B f))
    rw [hI]
    apply hasIntegrableStripNormalization_sum
    intro j
    obtain ⟨R, hRg⟩ := complexAdjacentJacquetStripGrowth D κ a d ds es hds U B hB f
      (Φ j) (φ j) (hΦ j) (fun v' => hA v' (splitRowTransform a (φ j)))
    obtain ⟨τ, hτ⟩ := R.eq_on_right
    obtain ⟨σ, hσ⟩ := splitTest_rightIntegrable D a d hds List.length_ofFn (Φ j) (φ j) U v
    exact ⟨R.value, fun s => ((R.analytic s (mem_univ _)).differentiableAt), hRg,
      max σ τ, fun s hs => ⟨hσ s ((le_max_left σ τ).trans_lt hs),
        hτ s ((le_max_right σ τ).trans_lt hs)⟩⟩
  have hP : P V.val := by
    have hv := V.2
    unfold complexWhittakerModel at hv
    refine Submodule.iSup_induction _ hv (motive := P) ?_ h0 hadd
    intro B v hv
    refine Submodule.iSup_induction _ hv (motive := P) ?_ h0 hadd
    rintro hB _ ⟨f, rfl⟩
    exact hImage B hB f
  obtain ⟨A, hAd, hAg, σ, hσ⟩ := hP
  exact ⟨⟨A, fun z _ => hAd.analyticAt z, ⟨σ, fun s hs => (hσ s hs).2⟩⟩,
    hAg, σ, fun s hs => (hσ s hs).1⟩

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
