import Langlands.Global.RankinSelberg.ComplexOrdinaryPolynomialKernel
import Langlands.Global.RankinSelberg.RealAdjacentSeparatedPolynomial
import Langlands.Global.RankinSelberg.RealGodementStandardGaussians
import Langlands.Global.RankinSelberg.RealStandardGaussianFourier
import Langlands.Representation.Archimedean.RealTemperedFormProof

/-! # Real adjacent polynomial normalization in a strong chamber -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal Langlands.Archimedean Langlands.Archimedean.GramFormula
open Langlands.Archimedean.PartialJacquet
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean Langlands.RankinSelberg
open RealGodement RealGodementGaussianPolynomial
open RealGodementProfiles (characterList)
open RealJacquetFrobenius (charData)

attribute [local instance] archimedeanEquationRealGLMeasurable archimedeanEquationRealGLBorel
  archimedeanEquationRealNMeasurable archimedeanEquationRealNBorel
  archimedeanEquationRealQMeasurable archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "m" => (r + 1 : ℕ)
local notation "n" => (r + 2 : ℕ)
local notation "H" => Langlands.GeneralLinear m ℝ
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "Rect" => Matrix (Fin m) (Fin n) ℝ
local notation "Poly" => MvPolynomial (Coordinates m n) ℂ
local notation "gap" => Nat.lt_succ_self r
local notation "L[" ds "," es "]" => fun s : ℂ => ((realPairLFactor ds es).denominator s)⁻¹

private def ordinaryKernel (V : H → ℂ) : (G → ℂ) →ₗ[ℂ] (ℂ → LeftUnipotentQuotient r ℝ → ℂ) where
  toFun W := realUnequalIntegrand gap W V
  map_add' W W' := funext (realUnequalIntegrand_add' W W' V)
  map_smul' b W := funext (realUnequalIntegrand_smul' b W V)

/-- Central covariance makes dilation of a rectangular polynomial Gaussian test to the
standard scale multiply its principal-series section by a nonzero scalar. -/
theorem sectionValue_standardMatrixTest (μ : Measure H) (c : RealCharacterData)
    (ds : List RealBlock) (f : H → ℂ) (Q : Poly)
    (hf : sectionValue μ c f (gaussianPolynomial Q) ∈ principalSeries ℝ n (realPositionCharacter ds)) :
    ∃ b : ℂ, b ≠ 0 ∧
      sectionValue μ c f (standardMatrixTest Q) = b • sectionValue μ c f (gaussianPolynomial Q) := by
  let a : ℝˣ := standardGaussianDilation
  let z : G := GeneralLinear.scalar a
  let e : Fin n → ℝˣ := fun _ => a
  let χ := principalSeriesCharacter ℝ n (realPositionCharacter ds) e
  let M := determinantWeight c ((m : ℂ) / 2) z
  have hM : M ≠ 0 := ((Group.isUnit z).map (determinantWeight c ((m : ℂ) / 2))).ne_zero
  have hχ : χ ≠ 0 := by
    unfold χ principalSeriesCharacter
    refine Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (RealTemperedForm.realPositionCharacter_ne_zero' ds i _) ?_
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (e i).ne_zero))))
  refine ⟨χ / M, div_ne_zero hχ hM, funext fun g => ?_⟩
  have he : GeneralLinear.Iwasawa.diagonalUnits e = z := by
    apply Units.ext
    rfl
  have hS := hf.2 e 1 g
  simp only [he, Subgroup.coe_one, mul_one] at hS
  have hz : g * z = z * g := (Matrix.GeneralLinearGroup.scalar_commute a g).symm
  have hT := sectionValue_mul_right μ c f (gaussianPolynomial Q) g z
  rw [hz, hS] at hT
  have hDil (Y : Rect) : Y * z.val = Real.sqrt Real.pi • Y := by
    change Y * Matrix.diagonal (fun _ : Fin n => Real.sqrt Real.pi) = _
    ext i j
    rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
  have hTest : (fun Y => gaussianPolynomial Q (Y * z.val)) = (standardMatrixTest Q : Rect → ℂ) :=
    funext fun Y => by rw [hDil, standardMatrixTest, standardGaussianDilate_apply]
  rw [hTest] at hT
  change χ * sectionValue μ c f (gaussianPolynomial Q) g =
    M * sectionValue μ c f (standardMatrixTest Q) g at hT
  change sectionValue μ c f (standardMatrixTest Q) g =
    (χ / M) * sectionValue μ c f (gaussianPolynomial Q) g
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hM).2
  rw [mul_comm]
  exact hT.symm

/-- The adjacent polynomial conclusion for canonical values in the chamber where the
larger character list is strictly dominant and Godement section integration converges. -/
def RealAdjacentPolynomialChamberStatement : Prop :=
  ∀ (D : RealQuotientMeasureData r) (a : ℝˣ), |(a : ℝ)| = 1 → RealEqualPolynomialAtRank r (-a) →
    ∀ (P : Fin n → Fin 2) (Z : Fin n → ℂ), Z ∈ realSpectralChamber (r + 1) →
    (∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent
      (characterList (Fin.tail P) (Fin.tail Z))) m i ≤
      (charData (P 0) (Z 0)).exponent.re + ((m : ℝ) + 1) / 2) →
    ∀ (fs : List RealCharacterData), fs.length = m →
    ∀ (B : Automorphic.realStandardKFinite m (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
      IsRealUniformWhittakerIntertwiner r (fs.map RealBlock.character) a B →
    ∀ (v : Automorphic.realStandardKFinite m (fs.map RealBlock.character))
      (u : Automorphic.realStandardKFinite n (characterList P Z)),
      realUnequalIntegrand gap (canonicalJacquetMap a P Z u) (B v) ∈
        polynomialOrdinaryKernels D.measure L[characterList P Z, fs.map RealBlock.character]

set_option maxHeartbeats 1400000 in
theorem realAdjacentPolynomialChamber : RealAdjacentPolynomialChamberStatement (r := r) := by
  intro D a ha hEqual P Z hZ hc fs hfs B hB v u
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let c := charData (P 0) (Z 0)
  let cs := List.ofFn fun i : Fin m => charData (Fin.tail P i) (Fin.tail Z i)
  let ds := characterList (Fin.tail P) (Fin.tail Z)
  let es := fs.map RealBlock.character
  let ds' := characterList P Z
  have hList : ds' = RealBlock.character c :: ds := characterList_succ P Z
  let V := Automorphic.realStandardKFinite n ds'
  have hV : V = kFiniteFunctions (principalSeries ℝ n (realPositionCharacter (RealBlock.character c :: ds)))
      (unitaryCompact ℝ n) := by
    change Automorphic.realStandardKFinite n (characterList P Z) = _
    rw [realStandardKFinite_characterList, characterList_succ P Z]
  let J := canonicalJacquetMap a P Z
  let S := (polynomialOrdinaryKernels D.measure L[ds', es]).comap (ordinaryKernel (B v))
  let T := (S.comap J).map V.subtype
  change J u ∈ S
  have hDom : IsStrictlyDominant (realPositionExponent (RealBlock.character c :: ds)) (r + 1) := by
    have h := isStrictlyDominant_characterList P hZ
    rwa [characterList_succ P Z] at h
  have hZt : Fin.tail Z ∈ realSpectralChamber r := fun i => hZ i.succ
  have hvModel : B v ∈ realUniformWhittakerModel r es a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)
  have hvReg := realUniformWhittakerRegularity r es a (B v) hvModel
  have hgen : gaussianSections μ c ds ⊆ T := by
    rintro _ ⟨Q, f, hf, rfl⟩
    have hfps : f ∈ principalSeries ℝ m (realPositionCharacter ds) := hf.1
    have hft : f ∈ Automorphic.realStandardKFinite m ds := by
      rw [realStandardKFinite_characterList]
      exact hf
    let U := canonicalJacquetMap a (Fin.tail P) (Fin.tail Z) ⟨f, hft⟩
    have hU : U = additiveJacquetIntegral a f := canonicalJacquetMap_agrees a (Fin.tail P) hZt ⟨f, hft⟩
    have hUm := canonicalJacquetMap_mem_uniformModel a (Fin.tail P) (Fin.tail Z) ⟨f, hft⟩
    let unscaled (q : Poly) : G → ℂ := sectionValue μ c f (gaussianPolynomial q)
    let scaled (q : Poly) : G → ℂ := sectionValue μ c f (standardMatrixTest q)
    have hMem (q : Poly) : unscaled q ∈ V := by
      rw [hV]
      exact gaussianSection_mem_kFinite μ c ds hfps hc q
    have hScale (q : Poly) : ∃ b : ℂ, b ≠ 0 ∧ scaled q = b • unscaled q := by
      have h := hMem q
      rw [hV] at h
      exact sectionValue_standardMatrixTest μ c _ f q h.1
    have hScaled (q : Poly) : scaled q ∈ V := by
      obtain ⟨b, _, hb⟩ := hScale q
      rw [hb]
      exact V.smul_mem b (hMem q)
    let A (q : Poly) : V := ⟨scaled q, hScaled q⟩
    have hEq (q : Poly) : J (A q) = realAdjacentGodementCoefficient D a (standardMatrixTest q) U c := by
      funext g
      change canonicalJacquetMap a P Z (A q) g = _
      rw [canonicalJacquetMap_agrees a P hZ, hU]
      exact (realGodementSchwartzJoint r D a c ds f hfps hDom hc (standardMatrixTest q) g).2
    have hTerm (d : Coordinates m n →₀ ℕ) : J (A (MvPolynomial.monomial d (Q.coeff d))) ∈ S := by
      let p := MvPolynomial.monomial (leadingExponents d) (Q.coeff d)
      let F := standardMatrixTest p
      let φ := standardColumnTest fun i => d (i, Fin.last m)
      have hsplit : standardMatrixTest (MvPolynomial.monomial d (Q.coeff d)) = realColumnProduct F φ :=
        standardMatrixTest_monomial d (Q.coeff d)
      let W := J (A (MvPolynomial.monomial d (Q.coeff d)))
      have hW : W = realAdjacentGodementCoefficient D a (realColumnProduct F φ) U c :=
        (hEq _).trans (congrArg (fun L => realAdjacentGodementCoefficient D a L U c) hsplit)
      have hWm : W ∈ realUniformWhittakerModel (r + 1) ds' (-a) :=
        canonicalJacquetMap_mem_uniformModel a P Z _
      have hWr := realUniformWhittakerRegularity (r + 1) ds' (-a) W hWm
      obtain ⟨σ, hσ, -⟩ := realUnequalPairConvergence (r + 1) r gap D (-a) W (B v) hWr.1 hWr.2
        (by simpa only [neg_neg] using hvReg.1) hvReg.2
      obtain ⟨N, R, hR⟩ := realAdjacentSeparatedPolynomial D a hEqual c cs fs List.length_ofFn hfs
        U hUm B hB v F (scalePolynomial p) (standardMatrixTest_eq_squarePolynomialGaussian p) φ
        (realStandardGaussianFourier a ha φ (standardColumnTest_isGaussianPolynomialRow _))
      change realUnequalIntegrand gap W (B v) ∈ polynomialOrdinaryKernels D.measure L[ds', es]
      rw [hList, hW]
      apply mem_polynomialOrdinaryKernels_of_normalization N R hR
      have hI := hσ
      rw [hW] at hI
      exact ⟨σ, fun s hs => hI s hs⟩
    have hDecomp : A Q = ∑ d ∈ Q.support, A (MvPolynomial.monomial d (Q.coeff d)) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change sectionValue μ c f (standardMatrixTest Q) = ∑ d ∈ Q.support,
        sectionValue μ c f (standardMatrixTest (MvPolynomial.monomial d (Q.coeff d)))
      rw [standardMatrixTest_sum_monomials Q]
      exact sectionValue_finset_sum Q.support μ c ds hfps hc _
    have hJ : J (A Q) ∈ S := by
      rw [hDecomp, map_sum]
      exact S.sum_mem fun d _ => hTerm d
    obtain ⟨b, hb, he⟩ := hScale Q
    have hA : A Q = b • (⟨unscaled Q, hMem Q⟩ : V) := Subtype.ext he
    rw [hA, map_smul] at hJ
    have hI := S.smul_mem b⁻¹ hJ
    rw [smul_smul, inv_mul_cancel₀ hb, one_smul] at hI
    exact ⟨⟨unscaled Q, hMem Q⟩, hI, rfl⟩
  have hspan := realGodementGaussianSpanning m μ c ds hc
  have hu : u.val ∈ T := (Submodule.span_le.mpr hgen) (by rw [hspan, ← hV]; exact u.2)
  obtain ⟨w, hw, he⟩ := hu
  have hwu : w = u := Subtype.ext he
  exact hwu ▸ hw

end Langlands.Global.RankinSelbergGlobal.RealJacquet
