import Langlands.Global.RankinSelberg.ComplexEqualContinuedGodementFamily
import Langlands.Global.RankinSelberg.ComplexEqualGaussianChamber
import Langlands.Global.RankinSelberg.ComplexLocalEqualGrowthStep
import Langlands.Global.RankinSelberg.ComplexLocalEqualMeromorphicReduction

/-! # Ordinary complex polynomial normalizations in equal and adjacent ranks -/

noncomputable section

open MeasureTheory Metric Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open ComplexEqualPolynomialGeneration (IsGaussianPolynomialRow)
open ComplexAdjacentUnfolding (canonicalChamberRemoval complexAdjacent_groupHaar_rightInvariant
  continuedValue_dilateMatrixTest differentiable_pairDenominator godementDilationMultiplier)
open ComplexGodement (addedCharacter characterList_cons gaussianGodementSections complexGodementGaussianSpanning
  godementSection shiftedCharacter smallerWeights smallerExponents retainedCharacters)
open ComplexGodementAddedCharacter (continuedValue continuedValue_eq_shiftedCharacter continuedValue_eq_signed_recursion)
open ComplexGodementGaussianPolynomial (Coordinates gaussianPolynomial standardMatrixTest standardGaussianDilation)
open ComplexCompactProfileFamily (characterList compactRestriction compactRestriction_isCompactProfile)
open ComplexJacquetChamberHolomorphic (chamber)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner
  continuedJacquet_mem_complexWhittakerModel complexJacquetSchwartzEvaluation
  exists_smallerQuotientData canonicalJacquetFamily canonicalJacquetFamily_properties
  continuedJacquetFamilies_apply continuedJacquet_eq_of_compactRestriction continuedJacquet_transferProfile
  transferProfile transferProfile_self)
open ComplexJacquetMultiplicityOne (complexJacquetMultiplicityOne exists_characterList)
open ComplexJacquet (complexEqualContinuedGodementFamily complexEqualGaussianChamber
  complexEqualIntegral_scale_left_of_eq complexLocalEqualFamily uniformSimpleRootBound_compact)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexWhittakerTranslatedMellin (compact_rightTranslate_uniformSimpleRootBound)
open ComplexUnequalFamily (HasLeftCharacter)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.Analysis.PolynomialFiberContinuation (polynomialFiberContinuation)
open Langlands.GeneralDirichlet (eqOn_halfPlane)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "scale" => (2 * Real.pi : ℝ)

private theorem polynomialAt_of_joint {F : ℂ × ℂ → ℂ} {S U : Set ℂ} {σ : ℝ}
    (hS : IsOpen S) (hSc : IsPreconnected S) (hU : IsOpen U) (hUne : U.Nonempty) (hUS : U ⊆ S)
    (hF : DifferentiableOn ℂ F (S ×ˢ {s : ℂ | σ < s.re}))
    (hPoly : ∀ z ∈ U, ∃ (P : Polynomial ℂ) (σ' : ℝ), ∀ s : ℂ, σ' < s.re → F (z, s) = P.eval s)
    (z : ℂ) (hz : z ∈ S) : ∃ P : Polynomial ℂ, ∀ s : ℂ, σ < s.re → F (z, s) = P.eval s := by
  have hParameter (s : ℂ) (hs : σ < s.re) : DifferentiableOn ℂ (fun z => F (z, s)) S := by
    have hm : MapsTo (fun z : ℂ => (z, s)) S (S ×ˢ {w : ℂ | σ < w.re}) :=
      fun _ hz => Set.mem_prod.mpr ⟨hz, hs⟩
    have he : Differentiable ℂ (fun z : ℂ => (z, s)) :=
      differentiable_id.prodMk (differentiable_const s)
    exact hF.comp he.differentiableOn hm
  have hSpectral (z : ℂ) (hz : z ∈ U) : DifferentiableOn ℂ (fun s => F (z, s)) {s : ℂ | σ < s.re} := by
    have hm : MapsTo (fun s : ℂ => (z, s)) {w : ℂ | σ < w.re} (S ×ˢ {w : ℂ | σ < w.re}) :=
      fun _ hs => Set.mem_prod.mpr ⟨hUS hz, hs⟩
    have he : Differentiable ℂ (fun s : ℂ => (z, s)) :=
      (differentiable_const z).prodMk differentiable_id
    exact hF.comp he.differentiableOn hm
  obtain ⟨N, hN⟩ := polynomialFiberContinuation S U hS hSc hU hUne hUS σ (fun z s => F (z, s))
    hParameter (fun z hz => by
      obtain ⟨P, σ', hP⟩ := hPoly z hz
      exact ⟨P, fun s hs => eqOn_halfPlane (hSpectral z hz) P.differentiable.differentiableOn hP hs⟩)
  obtain ⟨P, _, hP⟩ := hN z hz
  exact ⟨P, hP⟩

variable {r : ℕ}
local notation "m" => (r + 1 : ℕ)
local notation "n" => (r + 1 + 1 : ℕ)
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Row" => Fin n → ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "L" => Fin n → ℤ
local notation "P" => Fin n → ℂ
local notation "Q" => Fin m → ℂ
local notation "Std[" l "," p "]" => complexStandardKFinite n (characterList l p)

private def reciprocal (ds es : List ComplexCharacterData) (s : ℂ) :=
  ((complexPairLFactor ds es).denominator s)⁻¹

private def equalOrdinaryKernel (V : G → ℂ) (φ : 𝓢(Row, ℂ)) :
    (G → ℂ) →ₗ[ℂ] (ℂ → Langlands.RankinSelberg.LeftUnipotentQuotient (r + 1) ℂ → ℂ) where
  toFun W := complexEqualIntegrand W V φ
  map_add' W W' := by
    funext s q
    simp [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, add_mul]
  map_smul' c W := by
    funext s q
    simp [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, mul_assoc]

private theorem shiftedCharacter_zero (d : ComplexCharacterData) : shiftedCharacter d 0 = d := by
  rw [shiftedCharacter, add_zero, characterOfParams_eta]

private theorem equalGaussianContinued_polynomial (a : ℂˣ) (hAdj : ComplexAdjacentPolynomialAtRank r (-a))
    (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (d : ComplexCharacterData) (ds : List ComplexCharacterData) (hds : ds.length = m)
    (e : Fin n → ComplexCharacterData) (U : complexWhittakerModel r ds a)
    (B : complexStandardKFinite n (List.ofFn e) →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner (r + 1) (List.ofFn e) (-a) B)
    (f : complexStandardKFinite n (List.ofFn e)) (p : MvPolynomial (Coordinates m n) ℂ)
    (φ : 𝓢(Row, ℂ)) (hφ : IsGaussianPolynomialRow scale φ)
    (hU : ∀ (u : Langlands.GeneralLinear.upperUnipotent m ℂ) (g : H),
      U.val (u.val * g) = Langlands.GodementJacquet.traceCharacter a
        (Langlands.HarmonicAnalysis.unipotentFourierSum r u) * U.val g)
    (hUb : ComplexLocalConvergence.HasSimpleRootLogBound U.val) :
    let W (z : ℂ) (g : G) := continuedValue D₁.groupHaar (complexSelfDualMeasure (-a)) d (-a)
      (operatorToEntry (standardMatrixTest p)) U.val g z
    (∃ τ : ℝ, ∀ z : ℂ, τ < z.re → HasLeftCharacter a (W z)) →
    complexEqualIntegrand (W 0) (B f) φ ∈ polynomialOrdinaryKernels D.measure (reciprocal (d :: ds) (List.ofFn e)) := by
  intro W hInit
  let es := List.ofFn e
  let V : complexWhittakerModel (r + 1) es (-a) :=
    ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
  let Φ := operatorToEntry (standardMatrixTest p)
  obtain ⟨A, τ, σ, hA⟩ := complexEqualGaussianChamber a hAdj D D₁ d ds hds e U B hB f p φ hφ
  let R := |τ| + 3
  let S := ball (0 : ℂ) R
  obtain ⟨σ₀, hConv, hJ⟩ := complexEqualContinuedGodementFamily D D₁ a d ds es U V Φ φ hInit R
  let F (w : ℂ × ℂ) := (complexPairLFactor (shiftedCharacter d w.1 :: ds) es).denominator w.2 *
    complexEqualIntegral D (W w.1) V.val φ w.2
  have hDen : Differentiable ℂ (fun w : ℂ × ℂ => (complexPairLFactor (shiftedCharacter d w.1 :: ds) es).denominator w.2) := by
    obtain ⟨l, q, hq⟩ := exists_characterList ds hds
    obtain ⟨l', q', hq'⟩ := exists_characterList es List.length_ofFn
    let p₀ (w : ℂ × ℂ) : P := Fin.cons (d.exponent + w.1) q
    have hp₀ : Differentiable ℂ p₀ := by
      apply differentiable_pi.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact differentiable_fst.const_add d.exponent
      · exact differentiable_const _
    have he (w : ℂ × ℂ) : characterList (Fin.cons d.weight l) (p₀ w) = shiftedCharacter d w.1 :: ds := by
      rw [← hq]
      simp only [characterList, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, p₀, shiftedCharacter]
    simpa only [he, hq'] using differentiable_pairDenominator (Fin.cons d.weight l) l' p₀ (fun _ => q')
      hp₀ (differentiable_const q') Prod.snd differentiable_snd
  have hF : DifferentiableOn ℂ F (S ×ˢ {s : ℂ | σ₀ < s.re}) := hDen.differentiableOn.mul hJ
  let T := S ∩ {z : ℂ | τ < z.re}
  have hT : IsOpen T := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hTne : T.Nonempty := by
    let z₀ : ℂ := ((max τ 0 + 1 : ℝ) : ℂ)
    refine ⟨z₀, ?_, ?_⟩
    · change z₀ ∈ ball (0 : ℂ) R
      rw [mem_ball, dist_zero_right]
      have hv : 0 ≤ max τ 0 + 1 := by have := le_max_right τ 0; linarith
      rw [show z₀ = _ from rfl, Complex.norm_real, Real.norm_of_nonneg hv]
      have h := max_le (le_abs_self τ) (abs_nonneg τ)
      dsimp [R]
      linarith
    · change τ < z₀.re
      rw [show z₀ = _ from rfl, Complex.ofReal_re]
      linarith [le_max_left τ (0 : ℝ)]
  let c : ℂ := d.character ((-1 : ℂˣ) ^ m)
  have hPoly (z : ℂ) (hz : z ∈ T) : ∃ (A₁ : Polynomial ℂ) (b : ℝ),
      ∀ s : ℂ, b < s.re → F (z, s) = A₁.eval s := by
    let W₀ := Langlands.GodementJacquet.complexJacquetRecursion a D₁ Φ U.val
      (shiftedCharacter d z).character.toMonoidHom
    have hw (g : G) : c * W₀ g = W z g := by
      have h := continuedValue_eq_signed_recursion (-a) D₁ d Φ
        ((contMDiff_of_mem_complexWhittakerModel U.2).continuous)
        (fun u g => by simpa only [neg_neg] using hU u g) hUb g z
      simpa only [W₀, c, shiftedCharacter, neg_neg] using h.symm
    refine ⟨Polynomial.C c * A z, σ, fun s hs => ?_⟩
    have h := complexEqualIntegral_scale_left_of_eq D c W₀ (W z) V.val φ s hw
    change _ * complexEqualIntegral D (W z) V.val φ s = _
    rw [← h, Polynomial.eval_mul, Polynomial.eval_C]
    have hZ : (A z).eval s = (complexPairLFactor (shiftedCharacter d z :: ds) es).denominator s *
        complexEqualIntegral D W₀ V.val φ s := hA z s hz.2 hs
    rw [hZ]
    ring
  have hZero : (0 : ℂ) ∈ S := mem_ball_self (by dsimp [R]; positivity)
  obtain ⟨A₀, hA₀⟩ := polynomialAt_of_joint isOpen_ball (convex_ball _ _).isPreconnected hT hTne
    (fun _ hz => hz.1) hF hPoly 0 hZero
  obtain ⟨b, hb⟩ := complexPairLFactor_denominator_ne_zero (d :: ds) es
  refine ⟨A₀, max σ₀ b, fun s hs => ⟨hConv 0 hZero s ((le_max_left _ _).trans_lt hs), ?_⟩⟩
  have h := hA₀ s ((le_max_left _ _).trans_lt hs)
  have hL := hb s ((le_max_right _ _).trans_lt hs)
  change complexEqualIntegral D (W 0) V.val φ s =
    A₀.eval s * ((complexPairLFactor (d :: ds) es).denominator s)⁻¹
  change (complexPairLFactor (shiftedCharacter d 0 :: ds) es).denominator s *
    complexEqualIntegral D (W 0) V.val φ s = _ at h
  rw [shiftedCharacter_zero] at h
  rw [← h, mul_comm ((complexPairLFactor (d :: ds) es).denominator s), mul_assoc,
    mul_inv_cancel₀ hL, mul_one]

private def HasCanonicalEqualPolynomial (D : ComplexQuotientMeasureData (r + 1))
    (a : ℂˣ) (l : L) (p : P) (es : List ComplexCharacterData) (V : G → ℂ) (φ : 𝓢(Row, ℂ)) : Prop :=
  ∀ f : Std[l,p],
    let W := continuedJacquet (complexSelfDualMeasure (-a)) (-a) l p f
    complexEqualIntegrand W V φ ∈ polynomialOrdinaryKernels D.measure (reciprocal (characterList l p) es)

private theorem continued_standardMatrixTest (ν : Measure H) [ν.IsMulLeftInvariant]
    (a : ℂˣ) (d : ComplexCharacterData) (ds : List ComplexCharacterData) (hds : ds.length = m)
    (U : complexWhittakerModel r ds a) (A : MvPolynomial (Coordinates m n) ℂ) (g : G) (z : ℂ) :
    continuedValue ν (complexSelfDualMeasure (-a)) d (-a) (operatorToEntry (standardMatrixTest A)) U.val g z =
      godementDilationMultiplier r d ds standardGaussianDilation z *
        continuedValue ν (complexSelfDualMeasure (-a)) d (-a) (operatorToEntry (gaussianPolynomial A)) U.val g z := by
  let U' : complexWhittakerModel r ds (-(-a)) := ⟨U.val, by rw [neg_neg]; exact U.2⟩
  exact continuedValue_dilateMatrixTest ν (complexSelfDualMeasure (-a)) (-a) d hds U'
    standardGaussianDilation (gaussianPolynomial A) g z

set_option maxHeartbeats 1200000 in
private theorem gaussianContinued_left_on_halfPlane
    (D₁ : ComplexQuotientMeasureData r) (a : ℂˣ) (l : L) (p : P) (hp : p ∈ chamber (r + 1))
    (u : complexStandardKFinite m (retainedCharacters l p)) (A : MvPolynomial (Coordinates m n) ℂ) :
    let μ := complexSelfDualMeasure (-a)
    let U := continuedJacquet μ (-a) (smallerWeights l) (smallerExponents p) u
    let W (z : ℂ) (g : G) := continuedValue D₁.groupHaar μ (addedCharacter l p) (-a)
      (operatorToEntry (standardMatrixTest A)) U g z
    ∃ τ : ℝ, ∀ z : ℂ, τ < z.re → HasLeftCharacter a (W z) := by
  intro μ U W
  let ν := D₁.groupHaar
  let : ν.IsHaarMeasure := D₁.groupHaar_isHaar
  let : ν.IsMulRightInvariant := complexAdjacent_groupHaar_rightInvariant D₁
  let q := smallerExponents p
  let d := addedCharacter l p
  let ds := retainedCharacters l p
  have hU : U ∈ complexWhittakerModel r ds (-(-a)) :=
    continuedJacquet_mem_complexWhittakerModel μ (-a) (smallerWeights l) q u
  rw [neg_neg] at hU
  let U₀ : complexWhittakerModel r ds a := ⟨U, hU⟩
  have hq : q ∈ chamber r := by
    intro i
    simpa only [q, smallerExponents, Fin.castSucc_succ] using hp i.succ
  obtain ⟨M, hM⟩ := complexGodementGaussianSpanning (r := r) ν
    (fun i => characterOfParams (smallerWeights l i) (q i))
  obtain ⟨N, hN⟩ := complexJacquetSchwartzEvaluation (r := r) ν l q
  let ρ : ℂ := (((m : ℂ) + 1) / 2)
  refine ⟨max (q 0).re ((m : ℝ) + max M N - ρ.re) - (p 0).re, fun z hz v g => ?_⟩
  let pz : P := Fin.cons (p 0 + z) q
  have hTail : smallerExponents pz = q := Fin.tail_cons _ _
  have hdz : addedCharacter l pz = shiftedCharacter d z := rfl
  have hpz : pz ∈ chamber (r + 1) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (q 0).re < (p 0 + z).re
      rw [Complex.add_re]
      linarith [le_max_left (q 0).re ((m : ℝ) + max M N - ρ.re)]
    · simpa only [pz, Fin.castSucc_succ, Fin.cons_succ] using hq j
  have hb (k : ℕ) (hk : k ≤ max M N) : (m : ℝ) + k ≤ (pz 0 + ρ).re := by
    have hk' : (k : ℝ) ≤ max M N := by exact_mod_cast hk
    simp only [pz, Fin.cons_zero, Complex.add_re]
    linarith [le_max_right (q 0).re ((m : ℝ) + max M N - ρ.re)]
  let E := godementSection ν (addedCharacter l pz) (gaussianPolynomial A) u.val
  have hSpan : Submodule.span ℂ (gaussianGodementSections ν (addedCharacter l pz) ds) =
      complexStandardKFinite n (addedCharacter l pz :: ds) :=
    hM (addedCharacter l pz) (by
      simpa only [addedCharacter, characterOfParams_exponent] using hb M (le_max_left _ _))
  have he : E ∈ complexStandardKFinite n (addedCharacter l pz :: ds) := by
    rw [← hSpan]
    exact Submodule.subset_span ⟨(A, u), rfl⟩
  have he' : E ∈ Std[l,pz] := by
    rw [characterList_cons, show retainedCharacters l pz = ds from
      congrArg (characterList (smallerWeights l)) hTail]
    exact he
  let F : Std[l,pz] := ⟨E, he'⟩
  let uz : complexStandardKFinite m (retainedCharacters l pz) := ⟨u.val, by
    change u.val ∈ complexStandardKFinite m (characterList (smallerWeights l) (smallerExponents pz))
    rw [hTail]
    exact u.2⟩
  have hu : continuedJacquet μ (-a) (smallerWeights l) (smallerExponents pz) uz = U := by
    rw [continuedJacquet_eq_of_compactRestriction μ (-a) (smallerWeights l) q (smallerExponents pz) u uz rfl,
      hTail]
    rfl
  have hEval := hN pz hTail hpz (hb N (le_max_right _ _)) μ (-a) (gaussianPolynomial A) uz F rfl
  rw [hu, hdz] at hEval
  let C := godementDilationMultiplier r d ds standardGaussianDilation z
  have hW (x : G) : W z x = C * continuedJacquet μ (-a) l pz F x := by
    change continuedValue ν μ d (-a) (operatorToEntry (standardMatrixTest A)) U x z = _
    rw [continued_standardMatrixTest ν a d ds List.length_ofFn U₀ A x z]
    rw [continuedValue_eq_shiftedCharacter]
    exact congrArg (C * ·) (congrFun hEval x).symm
  rw [hW, hW]
  have hF := continuedJacquet_mem_complexWhittakerModel μ (-a) l pz F
  rw [complexWhittakerModel_left_equivariant hF v.val v.2 g, neg_neg]
  ring

set_option maxHeartbeats 1700000 in
private theorem canonicalEqualPolynomial_chamber (D : ComplexQuotientMeasureData (r + 1))
    (a : ℂˣ) (hAdj : ComplexAdjacentPolynomialAtRank r (-a))
    (l : L) (q : Q) (e : Fin n → ComplexCharacterData)
    (B : complexStandardKFinite n (List.ofFn e) →ₗ[ℂ] (G → ℂ))
    (hB : IsComplexWhittakerIntertwiner (r + 1) (List.ofFn e) (-a) B)
    (v : complexStandardKFinite n (List.ofFn e)) (φ : 𝓢(Row, ℂ)) (hφ : IsGaussianPolynomialRow scale φ) :
    ∃ M : ℕ, ∀ p : P, smallerExponents p = q → p ∈ chamber (r + 1) →
      (m : ℝ) + M ≤ (p 0 + (((m : ℂ) + 1) / 2)).re →
      HasCanonicalEqualPolynomial D a l p (List.ofFn e) (B v) φ := by
  let D₁ := Classical.choice (exists_smallerQuotientData (r := r))
  let ν := D₁.groupHaar
  let : ν.IsHaarMeasure := D₁.groupHaar_isHaar
  let : ν.IsMulRightInvariant := complexAdjacent_groupHaar_rightInvariant D₁
  obtain ⟨M, hM⟩ := complexGodementGaussianSpanning (r := r) ν
    (fun i => characterOfParams (smallerWeights l i) (q i))
  obtain ⟨N, hN⟩ := complexJacquetSchwartzEvaluation (r := r) ν l q
  refine ⟨max M N, fun p hq hp hb f => ?_⟩
  have hBound (k : ℕ) (hk : k ≤ max M N) :
      (m : ℝ) + k ≤ (p 0 + (((m : ℂ) + 1) / 2)).re :=
    (add_le_add le_rfl (by exact_mod_cast hk : (k : ℝ) ≤ (max M N : ℕ))).trans hb
  have hEval := hN p hq hp (hBound N (le_max_right _ _))
  subst q
  let d := addedCharacter l p
  let ds := retainedCharacters l p
  let μ := complexSelfDualMeasure (-a)
  let J := continuedJacquet μ (-a) l p
  let J₀ := continuedJacquet μ (-a) (smallerWeights l) (smallerExponents p)
  have hd : (m : ℝ) + M ≤ (d.exponent + (((m : ℂ) + 1) / 2)).re := by
    simpa only [d, addedCharacter, characterOfParams_exponent] using hBound M (le_max_left _ _)
  have hList : characterList l p = d :: ds := characterList_cons l p
  have hSpan : Submodule.span ℂ (gaussianGodementSections ν d ds) = Std[l,p] :=
    (hM d hd).trans (congrArg (complexStandardKFinite n) hList).symm
  let K := polynomialOrdinaryKernels D.measure (reciprocal (d :: ds) (List.ofFn e))
  let S := K.comap (equalOrdinaryKernel (B v) φ)
  let T := (S.comap J).map (Std[l,p]).subtype
  have hT : Submodule.span ℂ (gaussianGodementSections ν d ds) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨A, u⟩, rfl⟩
    let W₀ := godementSection ν d (gaussianPolynomial A) u.val
    have hW₀ : W₀ ∈ Std[l,p] := hSpan ▸
      (Submodule.subset_span (s := gaussianGodementSections ν d ds) ⟨(A, u), rfl⟩)
    let F : Std[l,p] := ⟨W₀, hW₀⟩
    refine ⟨F, ?_, rfl⟩
    have hU : J₀ u ∈ complexWhittakerModel r ds (-(-a)) :=
      continuedJacquet_mem_complexWhittakerModel μ (-a) (smallerWeights l) (smallerExponents p) u
    rw [neg_neg] at hU
    let U : complexWhittakerModel r ds a := ⟨J₀ u, hU⟩
    have hF : J F = fun g => continuedValue ν μ d (-a) (operatorToEntry (gaussianPolynomial A)) U.val g 0 :=
      hEval μ (-a) (gaussianPolynomial A) u F rfl
    have hUb := complexLocalWhittakerSimpleRootBound_of_uniformGrowth complexLocalWhittakerUniformGrowth
      r ds List.length_ofFn a U.val U.2
    let Wstd (g : G) := continuedValue ν μ d (-a) (operatorToEntry (standardMatrixTest A)) U.val g 0
    have hPol : complexEqualIntegrand Wstd (B v) φ ∈ K :=
      equalGaussianContinued_polynomial a hAdj D D₁ d ds List.length_ofFn e U B hB v A φ hφ
      (fun x g => complexWhittakerModel_left_equivariant U.2 x.val x.2 g) hUb
      (gaussianContinued_left_on_halfPlane D₁ a l p hp u A)
    let c := godementDilationMultiplier r d ds standardGaussianDilation 0
    have hc : c ≠ 0 := by
      unfold c godementDilationMultiplier ArchimedeanLocal.detPower
      exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (Complex.exp_ne_zero _)
    have he : Wstd = c • J F := by
      rw [hF]
      funext g
      exact continued_standardMatrixTest ν a d ds List.length_ofFn U A g 0
    change J F ∈ S
    have hS : c • J F ∈ S := by
      rw [← he]
      exact hPol
    have h := S.smul_mem c⁻¹ hS
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  have hf : f.val ∈ Submodule.span ℂ (gaussianGodementSections ν d ds) := hSpan.symm ▸ f.2
  obtain ⟨w, hw, hEq⟩ := hT hf
  change J w ∈ S at hw
  have h := (Subtype.ext hEq : w = f) ▸ hw
  change complexEqualIntegrand (J f) (B v) φ ∈
    polynomialOrdinaryKernels D.measure (reciprocal (characterList l p) (List.ofFn e))
  exact (congrArg (fun ds₀ => complexEqualIntegrand (J f) (B v) φ ∈
    polynomialOrdinaryKernels D.measure (reciprocal ds₀ (List.ofFn e))) hList).mpr h

set_option maxHeartbeats 1000000 in
private theorem canonicalEqualPolynomial_parameter (D : ComplexQuotientMeasureData (r + 1))
    (a : ℂˣ) (l k : L) (q : P) (V : complexWhittakerModel (r + 1) (characterList k q) (-a))
    (φ : 𝓢(Row, ℂ)) (p : ℂ → P) (hp : Differentiable ℂ p)
    (hInit : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ,
      HasCanonicalEqualPolynomial D a l (p z) (characterList k q) V.val φ) :
    HasCanonicalEqualPolynomial D a l (p 1) (characterList k q) V.val φ := by
  intro f
  let μ := complexSelfDualMeasure (-a)
  let ψ := compactRestriction f.val
  let J := canonicalJacquetFamily μ (-a) l ψ (compactRestriction_isCompactProfile f.2)
  let W (z : ℂ) := J (p z)
  have hW (z : ℂ) :
      W z = continuedJacquet μ (-a) l (p z) (transferProfile l (p 1) (p z) f) := by
    rw [continuedJacquet_transferProfile, continuedJacquetFamilies_apply]
  let S := ball (0 : ℂ) 3
  let S' := S ×ˢ (univ : Set ℂ)
  let es := characterList k q
  have hJ := canonicalJacquetFamily_properties μ (-a) l ψ (compactRestriction_isCompactProfile f.2)
  have hC := isCompact_closedBall (0 : ℂ) 3
  obtain ⟨N, hN⟩ := uniformSimpleRootBound_compact (hC.image hp.continuous) J hJ.2.2.1
  have hWb : HasUniformSimpleRootBound S' (fun x : ℂ × ℂ => W x.1) := by
    refine ⟨N, fun j => ?_⟩
    obtain ⟨C, hC, hb⟩ := hN j
    exact ⟨C, hC, fun x hx g => hb (p x.1) (mem_image_of_mem p (ball_subset_closedBall hx.1)) g⟩
  have hVb : HasUniformSimpleRootBound S' (fun _ => V.val) := by
    obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound V {1} isCompact_singleton
    refine ⟨N, fun j => ?_⟩
    obtain ⟨C, hC, hb⟩ := hN j
    exact ⟨C, hC, fun _ _ g => by simpa only [mul_one] using hb 1 (mem_singleton _) g⟩
  have hχ (z : ℂ) : HasLeftCharacter a (W z) := by
    rw [hW z]
    intro u g
    have hm := continuedJacquet_mem_complexWhittakerModel μ (-a) l (p z) (transferProfile l (p 1) (p z) f)
    rw [neg_neg] at hm
    exact complexWhittakerModel_left_equivariant hm u.val u.2 g
  obtain ⟨σ, hI, hD⟩ := complexLocalEqualFamily a D S' (fun x : ℂ × ℂ => W x.1) (fun _ => V.val)
    Prod.snd φ (isOpen_ball.prod isOpen_univ) differentiable_snd
    (fun x => hχ x.1) (fun _ u g => complexWhittakerModel_left_equivariant V.2 u.val u.2 g)
    (fun x => hJ.1 (p x.1)) (fun _ => (contMDiff_of_mem_complexWhittakerModel V.2).continuous)
    (fun g => ((hJ.2.1 g).comp (hp.comp differentiable_fst)).differentiableOn)
    (fun g => differentiableOn_const (V.val g)) hWb hVb
  let F (x : ℂ × ℂ) := (complexPairLFactor (characterList l (p x.1)) es).denominator x.2 *
    complexEqualIntegral D (W x.1) V.val φ x.2
  have hF : DifferentiableOn ℂ F (S ×ˢ {s : ℂ | σ < s.re}) := by
    have hL := differentiable_pairDenominator l k (p ∘ Prod.fst) (fun _ : ℂ × ℂ => q)
      (hp.comp differentiable_fst) (differentiable_const q) Prod.snd differentiable_snd
    exact hL.differentiableOn.mul (hD.mono (fun x hx => ⟨⟨hx.1, mem_univ x.2⟩, hx.2⟩))
  obtain ⟨δ, hδ, hδ'⟩ := hInit
  let U := ball (0 : ℂ) (min δ 3)
  have hUS : U ⊆ S := ball_subset_ball (min_le_right _ _)
  have hPoly (z : ℂ) (hz : z ∈ U) : ∃ (A : Polynomial ℂ) (τ : ℝ),
      ∀ s : ℂ, τ < s.re → F (z, s) = A.eval s := by
    have h := hδ' z (ball_subset_ball (min_le_left _ _) hz) (transferProfile l (p 1) (p z) f)
    change complexEqualIntegrand (continuedJacquet μ (-a) l (p z) (transferProfile l (p 1) (p z) f))
      V.val φ ∈ _ at h
    rw [← hW z] at h
    obtain ⟨A, τ, hA⟩ := h
    let K := (complexPairLFactor (characterList l (p z)) es).denominator
    obtain ⟨b, hb⟩ := complexPairLFactor_denominator_ne_zero (characterList l (p z)) es
    refine ⟨A, max τ b, fun s hs => ?_⟩
    have hEq : complexEqualIntegral D (W z) V.val φ s = A.eval s * (K s)⁻¹ :=
      (hA s ((le_max_left _ _).trans_lt hs)).2
    change K s * complexEqualIntegral D (W z) V.val φ s = _
    rw [hEq, mul_left_comm, mul_inv_cancel₀ (hb s ((le_max_right _ _).trans_lt hs)), mul_one]
  have hOne : (1 : ℂ) ∈ S := by simp [S, mem_ball, dist_zero_right]
  obtain ⟨A, hA⟩ := polynomialAt_of_joint isOpen_ball (convex_ball _ _).isPreconnected isOpen_ball
    ⟨0, mem_ball_self (lt_min hδ (by norm_num))⟩ hUS hF hPoly 1 hOne
  obtain ⟨b, hb⟩ := complexPairLFactor_denominator_ne_zero (characterList l (p 1)) es
  change complexEqualIntegrand (continuedJacquet μ (-a) l (p 1) f) V.val φ ∈ _
  rw [← transferProfile_self l (p 1) f, ← hW 1]
  refine ⟨A, max σ b, fun s hs => ⟨hI (1, s) ⟨⟨hOne, mem_univ s⟩, (le_max_left _ _).trans_lt hs⟩, ?_⟩⟩
  have hEq := hA s ((le_max_left _ _).trans_lt hs)
  let K := (complexPairLFactor (characterList l (p 1)) es).denominator
  change K s * complexEqualIntegral D (W 1) V.val φ s = _ at hEq
  change complexEqualIntegral D (W 1) V.val φ s = A.eval s * (K s)⁻¹
  rw [← hEq, mul_comm (K s), mul_assoc, mul_inv_cancel₀ (hb s ((le_max_right _ _).trans_lt hs)), mul_one]

/-- Polynomial normalization in adjacent ranks with the opposite trace scale implies
polynomial normalization of every standard Gaussian row test in the next equal rank. -/
def ComplexOrdinaryEqualPolynomialStepStatement : Prop :=
  ∀ (r : ℕ) (a : ℂˣ), ComplexAdjacentPolynomialAtRank r (-a) → ComplexEqualPolynomialAtRank (r + 1) a

set_option maxHeartbeats 1000000 in
theorem complexOrdinaryEqualPolynomialStep : ComplexOrdinaryEqualPolynomialStepStatement := by
  intro r a hAdj ds es hds hes D W V φ hφ
  obtain ⟨l, p, rfl⟩ := exists_characterList ds hds
  obtain ⟨k, q, rfl⟩ := exists_characterList es hes
  let μ := complexSelfDualMeasure (-a)
  let B := continuedJacquet μ (-a) l p
  let C := continuedJacquet μ a k q
  have hB : complexWhittakerModel (r + 1) (characterList l p) a = B.range := by
    have h := (complexJacquetMultiplicityOne (r + 1) μ (-a) l p).2
    rw [neg_neg] at h
    exact h
  have hC : complexWhittakerModel (r + 1) (characterList k q) (-a) = C.range :=
    (complexJacquetMultiplicityOne (r + 1) μ a k q).2
  obtain ⟨f, hf⟩ := (show W.val ∈ B.range from hB ▸ W.2)
  obtain ⟨v, hv⟩ := (show V.val ∈ C.range from hC ▸ V.2)
  have hAll : ∀ p₀ : Fin (r + 1 + 1) → ℂ,
      HasCanonicalEqualPolynomial D a l p₀ (characterList k q) V.val φ := by
    apply canonicalChamberRemoval
    · exact canonicalEqualPolynomial_parameter D a l k q V φ
    · intro q₀
      rw [← hv]
      exact canonicalEqualPolynomial_chamber D a hAdj l q₀ _ C (complexJacquetIntertwiner (r + 1) μ a k q) v φ hφ
  have h := hAll p f
  change complexEqualIntegrand (B f) V.val φ ∈ _ at h
  rw [hf] at h
  exact exists_ordinaryPolynomialNormalization_of_mem h

/-- At unit-modulus additive scale, standard Gaussian row tests in equal ranks and
all adjacent ordinary tests have polynomial normalization. -/
def ComplexOrdinaryPolynomialStatement : Prop :=
  ∀ (r : ℕ) (a : ℂˣ), ‖(a : ℂ)‖ = 1 → ComplexEqualPolynomialAtRank r a ∧ ComplexAdjacentPolynomialAtRank r a

theorem complexOrdinaryPolynomial : ComplexOrdinaryPolynomialStatement := by
  have hEqual (r : ℕ) : ∀ a : ℂˣ, ‖(a : ℂ)‖ = 1 → ComplexEqualPolynomialAtRank r a := by
    induction r with
    | zero => exact fun a _ => complexEqualPolynomialRankZero a
    | succ r ih =>
      intro a ha
      have ha' : ‖((-a : ℂˣ) : ℂ)‖ = 1 := by simpa only [Units.val_neg, norm_neg] using ha
      exact complexOrdinaryEqualPolynomialStep r a (complexOrdinaryAdjacentPolynomial r (-a) ha' (ih (-a) ha'))
  exact fun r a ha => ⟨hEqual r a ha, complexOrdinaryAdjacentPolynomial r a ha (hEqual r a ha)⟩

end Langlands.Global.RankinSelbergGlobal
