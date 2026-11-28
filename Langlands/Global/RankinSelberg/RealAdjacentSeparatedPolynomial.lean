import Langlands.Global.RankinSelberg.RealCompactSquarePolynomial
import Langlands.Global.RankinSelberg.RealOrthogonalCompactProjection
import Langlands.Global.RankinSelberg.RealRankOnePolynomial

/-! # Polynomial normalization of separated real adjacent tests -/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal RealGodement
open RealEqualPolynomialGeneration (GaussianEqualTest IsGaussianPolynomialRow gaussianEqualIntegral)
open RealSquarePolynomialGaussian
open RealGodementGaussianPolynomial (Coordinates)

attribute [local instance] archimedeanEquationRealGLMeasurable archimedeanEquationRealGLBorel
  archimedeanEquationRealNMeasurable archimedeanEquationRealNBorel
  archimedeanEquationRealQMeasurable archimedeanEquationRealQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "H" => Langlands.GeneralLinear m ℝ
local notation "O" => Matrix.unitaryGroup (Fin m) ℝ
local notation "Mat" => Matrix (Fin m) (Fin m) ℝ
local notation "Row" => Fin m → ℝ
local notation "L[" ds "," es "]" => fun s : ℂ => ((realPairLFactor ds es).denominator s)⁻¹

/-- Splitting the first inducing character splits the real reciprocal pair factor. -/
theorem reciprocalPair_cons (c : RealBlock) (ds es : List RealBlock) (s : ℂ) :
    L[c :: ds, es] s = L[[c], es] s * L[ds, es] s := by
  have h : realPairBlocks (c :: ds) es = realPairBlocks [c] es ++ realPairBlocks ds es := by
    simp [realPairBlocks]
  simp only [realPairLFactor, h, realLFactor_append, ReciprocalEntire.denominator_mul, mul_inv_rev,
    mul_comm]

/-- With polynomiality of smaller equal tests, the unfolded adjacent real integral of a
standard square test and a standard row test normalizes to a polynomial. -/
def RealAdjacentUnfoldedPolynomialStatement : Prop :=
  ∀ (D : RealQuotientMeasureData r) (a : ℝˣ), RealEqualPolynomialAtRank r (-a) →
    ∀ (c : RealCharacterData) (cs fs : List RealCharacterData), cs.length = m → fs.length = m →
    ∀ (U : H → ℂ), U ∈ realUniformWhittakerModel r (cs.map RealBlock.character) (-a) →
    ∀ (B : Automorphic.realStandardKFinite m (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
      IsRealUniformWhittakerIntertwiner r (fs.map RealBlock.character) a B →
    ∀ (f : Automorphic.realStandardKFinite m (fs.map RealBlock.character))
      (F : 𝓢(Mat, ℂ)) (p : MvPolynomial (Coordinates m m) ℂ),
      (F : Mat → ℂ) = squarePolynomialGaussian p →
    ∀ (φ : 𝓢(Row, ℂ)), IsGaussianPolynomialRow Real.pi φ →
      ∃ (β : ℝ) (P : Polynomial ℂ), ∀ s : ℂ, β < s.re →
        realAdjacentUnfoldedIntegral D c.character.toMonoidHom F φ U (B f) s =
          P.eval s * L[RealBlock.character c :: cs.map RealBlock.character, fs.map RealBlock.character] s

set_option maxHeartbeats 1400000 in
theorem realAdjacentUnfoldedPolynomial : RealAdjacentUnfoldedPolynomialStatement (r := r) := by
  intro D a hEqual c cs fs hcs hfs U hU B hB f F p hF φ hφ
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let ds := cs.map RealBlock.character
  let es := fs.map RealBlock.character
  let ν : Measure O := Measure.haar
  let iK : O →* H := Unitary.toUnits
  have hiK : Continuous iK := continuous_unitary_toUnits
  have hmem (k : O) : iK k ∈ unitaryCompact ℝ m := k.property
  have hsurj (g : H) (hg : g ∈ unitaryCompact ℝ m) : ∃ k : O, iK k = g :=
    ⟨⟨g.val, hg⟩, Units.ext rfl⟩
  have hFin : FiniteDimensional ℂ (Submodule.span ℂ (range fun k : O =>
      fun A : Mat => F ((iK k)⁻¹.val * A))) := by
    rw [hF]
    exact finiteDimensional_leftSquareGaussian iK hmem p
  obtain ⟨κ, hκ, hκfin, hRep⟩ := exists_realCompactMatrixWeight ν iK hiK c F F.continuous hFin
  choose v hv hV using fun g => realOrthogonalCompactProjectionPremise r es a κ hκ hκfin B hB f g
  obtain ⟨l, W, w, hW, hExp⟩ := realLocalCompactProjectionReduction (r := r) iK hiK hmem hsurj
    es a ν inferInstance κ hκ hκfin f B hB v hv (fun x g => hV g x)
  let C (j : Fin l) (g : H) : ℂ := ∫ k, w j k * (f : H → ℂ) (iK k * g) ∂ν
  have hM (j : Fin l) := realCompactSquarePolynomial (r := r) D.groupHaar iK hiK hmem ν
    (w j) (hW j).2 fs hfs c f.val f.2.1.1 F p hF
  choose β M hM using hM
  obtain ⟨β₀, hβ₀⟩ := (finite_range β).bddAbove
  have hVf : B f ∈ realUniformWhittakerModel r es a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  have hReg := realUniformWhittakerRegularity r ds (-a) U hU
  have hRegW (j : Fin l) := realUniformWhittakerRegularity r es a (W j) (hW j).1
  have hNeg : -(-a) = a := neg_neg a
  have hConv (j : Fin l) := (realEqualPairConvergence r D (-a) a U (W j) φ hReg.1 hReg.2
    (by simpa only [hNeg] using (hRegW j).1) (hRegW j).2)
  choose γ hγ using hConv
  obtain ⟨γ₀, hγ₀⟩ := (finite_range γ).bddAbove
  have hUr := splitModel_regular hU
  have hVr := splitModel_regular hVf
  obtain ⟨τ, hτ⟩ := realAdjacentUnfoldedIntegral_expansion D ν iK hiK
    (fun k => MaximalParabolicIntegration.abs_det_unitary ⟨iK k, hmem k⟩)
    κ hκ c F hFin hRep φ φ.continuous (RealEqualConvergence.hasRapidDecay_schwartz _) U (B f)
    hUr.2.1.continuous hVr.2.1.continuous (splitPair_invariant hUr hVr)
    (splitModel_gauge hU) (splitModel_growth hVf) l W C (fun x g => (hExp x g).1)
    ⟨γ₀, fun s hs j => (hγ j).1 s ((hγ₀ (mem_range_self j)).trans_lt hs)⟩
    ⟨β₀, fun s hs j => (hM j s ((hβ₀ (mem_range_self j)).trans_lt hs)).1⟩
  have hdr : realRank ds = m := by rw [realRank_map_character, hcs]
  have her : realRank es = m := by rw [realRank_map_character, hfs]
  let i (j : Fin l) : GaussianEqualTest r ds es (-a) Real.pi :=
    (⟨U, by rw [realWhittakerModels_eq r ds hdr]; exact hU⟩,
     ⟨W j, by rw [hNeg, realWhittakerModels_eq r es her]; exact (hW j).1⟩, ⟨φ, hφ⟩)
  have hN (j : Fin l) := hEqual cs fs hcs hfs D (i j)
  choose N Q hQ using hN
  choose α hα using fun j => (N j).eq_on_right
  obtain ⟨α₀, hα₀⟩ := (finite_range α).bddAbove
  refine ⟨max τ (max α₀ β₀), ∑ j, Q j * M j, fun s hs => ?_⟩
  rw [hτ s ((le_max_left _ _).trans_lt hs), Polynomial.eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hL : realEqualIntegral D U (W j) φ s = (Q j).eval s * L[ds, es] s := by
    have hj := (hα₀ (mem_range_self j)).trans_lt ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs))
    simpa only [hQ j, gaussianEqualIntegral, realOrdinaryEqualTest, i] using hα j s hj
  have hR := (hM j s ((hβ₀ (mem_range_self j)).trans_lt
      ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs)))).2
  change _ * (∫ z, realAdjacentMatrixWeight c.character.toMonoidHom F s z * C j z ∂D.groupHaar) = _
  rw [hL, hR, Polynomial.eval_mul, reciprocalPair_cons]
  ring

/-- The separated Godement coefficient has a polynomial normalized ordinary adjacent
integral whenever the transformed row is a standard polynomial Gaussian. -/
theorem realAdjacentSeparatedPolynomial (D : RealQuotientMeasureData r) (a : ℝˣ)
    (hEqual : RealEqualPolynomialAtRank r (-a)) (c : RealCharacterData) (cs fs : List RealCharacterData)
    (hcs : cs.length = m) (hfs : fs.length = m) (U : H → ℂ)
    (hU : U ∈ realUniformWhittakerModel r (cs.map RealBlock.character) (-a))
    (B : Automorphic.realStandardKFinite m (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ))
    (hB : IsRealUniformWhittakerIntertwiner r (fs.map RealBlock.character) a B)
    (f : Automorphic.realStandardKFinite m (fs.map RealBlock.character))
    (F : 𝓢(Mat, ℂ)) (p : MvPolynomial (Coordinates m m) ℂ)
    (hF : (F : Mat → ℂ) = squarePolynomialGaussian p)
    (φ : 𝓢(Row, ℂ)) (hφ : IsGaussianPolynomialRow Real.pi (realRowSchwartzFourier m a φ)) :
    let W := realAdjacentGodementCoefficient D a (realColumnProduct F φ) U c
    ∃ (N : OrdinaryIntegralNormalization (realUnequalIntegral (Nat.lt_succ_self r) D W (B f))
      L[RealBlock.character c :: cs.map RealBlock.character, fs.map RealBlock.character]) (P : Polynomial ℂ),
      N.value = P.eval := by
  intro W
  have hUd : ArchimedeanLocal.dualFunction m U ∈ realUniformWhittakerModel r
      (RealUniformWhittakerDual.dualCharacterBlocks cs) a := by
    simpa only [neg_neg] using RealUniformWhittakerDual.realUniformWhittakerCharacterDual r cs hcs (-a) U hU
  have hV : B f ∈ realUniformWhittakerModel r (fs.map RealBlock.character) a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  obtain ⟨σ, hσ⟩ := realAdjacentGodementHalfPlane D a c F φ _ _ _ U (B f) hU hUd hV
  obtain ⟨β, Q, hQ⟩ := realAdjacentUnfoldedPolynomial D a hEqual c cs fs hcs hfs U hU B hB f F p hF
    (realRowSchwartzFourier m a φ) hφ
  let P := Polynomial.C (realAdjacentWeylSign r c) * Q
  refine ⟨⟨P.eval, fun s _ => P.differentiable.analyticAt s, ⟨max σ β, fun s hs => ?_⟩⟩, P, rfl⟩
  rw [(hσ s ((le_max_left _ _).trans_lt hs)).1, hQ s ((le_max_right _ _).trans_lt hs)]
  simp only [P, Polynomial.eval_mul, Polynomial.eval_C, mul_assoc]

end Langlands.Global.RankinSelbergGlobal.RealJacquet
