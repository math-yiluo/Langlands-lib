import Langlands.Global.RankinSelberg.RealAdjacentPolynomialChamber
import Langlands.Global.RankinSelberg.RealEqualUnfoldedPolynomial
import Langlands.Global.RankinSelberg.RealLocalEqualGeneratorTrace

/-! # Polynomial normalization of real equal-rank ordinary tests in the Godement chamber -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal Langlands.Archimedean Langlands.Archimedean.GramFormula
open Langlands.Archimedean.PartialJacquet Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg
open RealGodementProfiles (characterList)
open RealGodementGaussianPolynomial (Coordinates gaussianPolynomial standardMatrixTest)
open RealEqualPolynomialGeneration (IsGaussianPolynomialRow)
open RealJacquet (sectionValue_standardMatrixTest characterList_succ realStandardKFinite_characterList)
open RealJacquetFrobenius (charData)

attribute [local instance] archimedeanEquationRealGLMeasurable archimedeanEquationRealGLBorel
  archimedeanEquationRealNMeasurable archimedeanEquationRealNBorel
  archimedeanEquationRealQMeasurable archimedeanEquationRealQBorel

variable {t : ℕ}

local notation "m" => (t + 1 : ℕ)
local notation "n" => (t + 2 : ℕ)
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear n ℝ
local notation "Row" => Fin n → ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Poly" => MvPolynomial (Coordinates m n) ℂ
local notation "L[" ds "," es "]" => fun s : ℂ => ((realPairLFactor ds es).denominator s)⁻¹

private def equalOrdinaryKernel (V : H → ℂ) (φ : 𝓢(Row, ℂ)) :
    (H → ℂ) →ₗ[ℂ] (ℂ → LeftUnipotentQuotient (t + 1) ℝ → ℂ) where
  toFun W := realEqualIntegrand W V φ
  map_add' W W' := by
    funext s q
    simp only [realEqualIntegrand, ArchimedeanLocal.equalIntegrand, Pi.add_apply]
    ring
  map_smul' b W := by
    funext s q
    simp only [realEqualIntegrand, ArchimedeanLocal.equalIntegrand, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

private theorem realEqualGodementPolynomial (D : RealQuotientMeasureData t)
    (D' : RealQuotientMeasureData (t + 1)) (a : ℝˣ) (hAdj : RealAdjacentPolynomialAtRank t (-a))
    (e : Fin 2) (cs fs : List RealCharacterData) (hcs : cs.length = m) (hfs : fs.length = n)
    (U : G → ℂ) (hU : U ∈ realUniformWhittakerModel t (cs.map RealBlock.character) a)
    (B : Automorphic.realStandardKFinite n (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ))
    (hB : IsRealUniformWhittakerIntertwiner (t + 1) (fs.map RealBlock.character) (-a) B)
    (f : Automorphic.realStandardKFinite n (fs.map RealBlock.character))
    (p : Poly) (φ : 𝓢(Row, ℂ)) (hφ : IsGaussianPolynomialRow Real.pi φ) (τ σ : ℝ)
    (hJ : ∀ z s : ℂ, τ < z.re → σ < s.re →
      Integrable (equalUnfoldedKernel (charData e z) (equalSquareSchwartz (standardMatrixTest p) φ)
        U (B f) s) (D.measure.prod D'.groupHaar)) (z : ℂ) (hz : τ < z.re) (hz0 : 0 < z.re) :
    let W (g : H) := godementLeadingFamily D (-a) (standardMatrixTest p) U e g z
    ∃ (N : OrdinaryIntegralNormalization (realEqualIntegral D' W (B f) φ)
      L[RealBlock.character (charData e z) :: cs.map RealBlock.character, fs.map RealBlock.character])
      (P : Polynomial ℂ), N.value = P.eval := by
  intro W
  let d := charData e z
  let ds := cs.map RealBlock.character
  let es := fs.map RealBlock.character
  let Φ := standardMatrixTest p
  let Ψ := equalSquareSchwartz Φ φ
  obtain ⟨q, hq⟩ := equalSquareSchwartz_standardMatrixTest p φ hφ
  obtain ⟨P, β, hP⟩ := realEqualUnfoldedPolynomial D D' a hAdj e cs fs hcs hfs U hU B hB f Ψ q hq τ σ hJ
  have hU' : U ∈ realUniformWhittakerModel t ds (-(-a)) := by simpa only [neg_neg] using hU
  have hV : B f ∈ realUniformWhittakerModel (t + 1) es (-a) :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  have hLawV : KernelWhittakerLaw (-(-a)) (B f) := by
    simpa only [neg_neg] using kernelWhittakerLaw_of_mem_model (a := a) hV
  let R := equalRecursiveCoefficient (-a) D Φ U (kernelWhittakerLaw_of_mem_model hU') d
  obtain ⟨b, hb, hW⟩ := godementLeadingFamily_eq_recursive D (-a) Φ hU'
  let c : ℂ := (b : ℂ) * ((d.character (-1) : ℂ) ^ (t + 1))
  have hCoe : W = fun g => c * R g := funext (hW e z)
  obtain ⟨b', hb', hb'μ, -⟩ := realGodementColumnQuotient (t + 1) (-a) D'
  have hb'₀ : (b' : ℂ) ≠ 0 := by exact_mod_cast hb'.ne'
  let Q := Polynomial.C (c / (b' : ℂ)) * P z
  refine ⟨⟨Q.eval, fun s _ => Q.differentiable.analyticAt s, ⟨max σ β, fun s hs => ?_⟩⟩, Q, rfl⟩
  have hΨ : (Ψ : Mat → ℂ) = equalSquareTest Φ φ := funext (equalSquareSchwartz_apply Φ φ)
  have hI := hJ z s hz ((le_max_left _ _).trans_lt hs)
  change Integrable (equalUnfoldedKernel d Ψ U (B f) s) _ at hI
  rw [hΨ] at hI
  have hu := (realLocalEqualUnfolding (-a) D D' b' hb' hb'μ Φ φ U
    (kernelWhittakerLaw_of_mem_model hU') (B f) d s hLawV hI).2
  change (b' : ℂ) * realEqualIntegral D' R (B f) φ s = _ at hu
  rw [← hΨ] at hu
  change realEqualIntegral D' W (B f) φ s = Q.eval s * _
  dsimp only [Q]
  rw [hCoe, realEqualIntegral_const_mul, Polynomial.eval_mul, Polynomial.eval_C]
  have hE := hP z s hz hz0 ((le_max_right _ _).trans_lt hs)
  change (∫ x, equalUnfoldedKernel d Ψ U (B f) s x ∂(D.measure.prod D'.groupHaar)) =
    (P z).eval s * ((realPairLFactor (RealBlock.character d :: ds) es).denominator s)⁻¹ at hE
  rw [mul_assoc (c / (b' : ℂ)), ← hE, ← hu]
  field_simp [hb'₀]

/-- The ordinary equal-rank polynomial property for the larger canonical map at a fixed
spectral parameter and against a fixed opposite-character coefficient and row. -/
def HasCanonicalEqualPolynomial (D' : RealQuotientMeasureData (t + 1)) (a : ℝˣ)
    (P : Fin n → Fin 2) (Z : Fin n → ℂ) (es : List RealBlock) (V : H → ℂ) (φ : 𝓢(Row, ℂ)) : Prop :=
  ∀ u : Automorphic.realStandardKFinite n (characterList P Z),
    realEqualIntegrand (canonicalJacquetMap (-a) P Z u) V φ ∈ polynomialOrdinaryKernels D'.measure
      L[characterList P Z, es]

/-- For each fixed tail spectrum, sufficiently large leading real part in the strict
chamber gives the equal-rank polynomial property from the smaller adjacent-rank one. -/
def RealEqualPolynomialChamberStatement : Prop :=
  ∀ (D' : RealQuotientMeasureData (t + 1)) (a : ℝˣ), RealAdjacentPolynomialAtRank t (-a) →
    ∀ (P : Fin n → Fin 2) (fs : List RealCharacterData), fs.length = n →
    ∀ (B : Automorphic.realStandardKFinite n (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
      IsRealUniformWhittakerIntertwiner (t + 1) (fs.map RealBlock.character) (-a) B →
    ∀ (v : Automorphic.realStandardKFinite n (fs.map RealBlock.character))
      (φ : 𝓢(Row, ℂ)), IsGaussianPolynomialRow Real.pi φ →
    ∀ q : Fin m → ℂ, ∃ M : ℝ, ∀ Z : Fin n → ℂ, Fin.tail Z = q → Z ∈ realSpectralChamber (t + 1) →
      M ≤ (Z 0).re → HasCanonicalEqualPolynomial D' a P Z (fs.map RealBlock.character) (B v) φ

set_option maxHeartbeats 1700000 in
theorem realEqualPolynomialChamber : RealEqualPolynomialChamberStatement (t := t) := by
  intro D' a hAdj P fs hfs B hB v φ hφ q
  let D := (nonempty_realQuotientMeasureData t (-a)).some
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let es := fs.map RealBlock.character
  let ds := characterList (Fin.tail P) q
  let J₀ := canonicalJacquetMap (-a) (Fin.tail P) q
  obtain ⟨NW, hNW⟩ := (realGodementCanonicalModel t (-a) (Fin.tail P) q).2
  have hV : B v ∈ realUniformWhittakerModel (t + 1) es (-a) :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)
  have hVreg := realUniformWhittakerRegularity (t + 1) es (-a) (B v) hV
  have hVc : Continuous (B v) := (hVreg.1 []).2.1.continuous
  have hVu (u : GeneralLinear.upperUnipotent n ℝ) (g : H) : ‖B v (u.val * g)‖ = ‖B v g‖ := by
    have hv : B v (u.val * g) = realWhittakerCharacter (-a) u.val * B v g :=
      (hVreg.1 []).1 u.val u.2 g
    rw [hv, norm_mul, RealUnequalPairConvergence.norm_realWhittakerCharacter, one_mul]
  obtain ⟨NV, hNV⟩ := RealWhittakerGauge.exists_gauge_bound hVreg.1 hVreg.2
  obtain ⟨τ, σ, hJ⟩ := realLocalEqualUniformJointIntegrability D D' (2 * NW) NV
  let e (i : Fin m) := (m : ℝ) + normExponent (realPositionExponent ds) m i - ((m : ℝ) + 1) / 2
  obtain ⟨M, hM⟩ := (finite_range e).bddAbove
  refine ⟨max M (max τ 0 + 1), fun Z hZq hZ hMZ u => ?_⟩
  have hz : τ < (Z 0).re := by linarith [le_max_left τ (0 : ℝ), (le_max_right M _).trans hMZ]
  have hz0 : 0 < (Z 0).re := by linarith [le_max_right τ (0 : ℝ), (le_max_right M _).trans hMZ]
  have hc (i : Fin m) : (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      (charData (P 0) (Z 0)).exponent.re + ((m : ℝ) + 1) / 2 := by
    have hi := (hM (mem_range_self i)).trans ((le_max_left M _).trans hMZ)
    change _ ≤ (Z 0).re + _
    dsimp only [e] at hi
    linarith
  subst q
  let c := charData (P 0) (Z 0)
  let cs := List.ofFn fun i : Fin m => charData (Fin.tail P i) (Fin.tail Z i)
  let ds' := characterList P Z
  have hList : ds' = RealBlock.character c :: ds := characterList_succ P Z
  let V := Automorphic.realStandardKFinite n ds'
  have hVeq : V = kFiniteFunctions (principalSeries ℝ n (realPositionCharacter (RealBlock.character c :: ds)))
      (unitaryCompact ℝ n) := by
    change Automorphic.realStandardKFinite n (characterList P Z) = _
    rw [realStandardKFinite_characterList, characterList_succ P Z]
  let J := canonicalJacquetMap (-a) P Z
  let S := (polynomialOrdinaryKernels D'.measure L[ds', es]).comap (equalOrdinaryKernel (B v) φ)
  let T := (S.comap J).map V.subtype
  change J u ∈ S
  have hDom : IsStrictlyDominant (realPositionExponent (RealBlock.character c :: ds)) (t + 1) := by
    have h := isStrictlyDominant_characterList P hZ
    rwa [characterList_succ P Z] at h
  have hZt : Fin.tail Z ∈ realSpectralChamber t := fun i => hZ i.succ
  have hgen : gaussianSections μ c ds ⊆ T := by
    rintro _ ⟨p, f, hf, rfl⟩
    have hfps : f ∈ principalSeries ℝ m (realPositionCharacter ds) := hf.1
    have hft : f ∈ Automorphic.realStandardKFinite m ds := by
      rw [realStandardKFinite_characterList]
      exact hf
    let U := J₀ ⟨f, hft⟩
    have hU : U = additiveJacquetIntegral (-a) f :=
      canonicalJacquetMap_agrees (-a) (Fin.tail P) hZt ⟨f, hft⟩
    have hUm : U ∈ realUniformWhittakerModel t ds a := by
      simpa only [neg_neg] using canonicalJacquetMap_mem_uniformModel (-a) (Fin.tail P) (Fin.tail Z) ⟨f, hft⟩
    have hUc := ((realUniformWhittakerRegularity t ds a U hUm).1 []).2.1.continuous
    have hUbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin m → ℝ) (k : unitaryCompact ℝ m),
        ‖U (RealIwasawa.torus y * (k : G))‖ ≤ C * Real.exp (((2 * NW : ℕ) : ℝ) * ∑ i, |y i|) := by
      obtain ⟨C, hC, hC'⟩ := hNW ⟨f, hft⟩
      refine ⟨C * (2 * ((t : ℝ) + 1) ^ 2) ^ NW, mul_nonneg hC (by positivity), fun y k => ?_⟩
      have h := (hC' _).trans (mul_le_mul_of_nonneg_left
        (RealWhittakerGauge.realMatrixHeight_torus_mul_pow_le y k NW) hC)
      simpa only [mul_assoc] using h
    have hJp (z s : ℂ) (hz : τ < z.re) (hs : σ < s.re) :
        Integrable (equalUnfoldedKernel (charData (P 0) z) (equalSquareSchwartz (standardMatrixTest p) φ)
          U (B v) s) (D.measure.prod D'.groupHaar) := by
      obtain ⟨k, C, _, h⟩ := hJ U (B v) hUc hVc hUbound hNV hVu z.re s.re hz.le hs
      exact (h _ (charData (P 0) z) s rfl rfl).1
    let A := sectionValue μ c f (gaussianPolynomial p)
    let A' := sectionValue μ c f (standardMatrixTest p)
    have hAps := gaussianSection_mem_kFinite μ c ds hfps hc p
    have hA : A ∈ V := hVeq.symm ▸ hAps
    obtain ⟨b, hb, hScale⟩ := sectionValue_standardMatrixTest μ c _ f p hAps.1
    change A' = b • A at hScale
    have hA' : A' ∈ V := hScale.symm ▸ V.smul_mem b hA
    let w : V := ⟨A, hA⟩
    let w' : V := ⟨A', hA'⟩
    have hW : J w' = fun g => godementLeadingFamily D (-a) (standardMatrixTest p) U (P 0) g (Z 0) := by
      funext g
      change canonicalJacquetMap (-a) P Z w' g = _
      rw [canonicalJacquetMap_agrees (-a) P hZ, hU]
      exact (realGodementSchwartzJoint t D (-a) c ds f hfps hDom hc (standardMatrixTest p) g).2
    have hWm : J w' ∈ realUniformWhittakerModel (t + 1) ds' a := by
      simpa only [neg_neg] using canonicalJacquetMap_mem_uniformModel (-a) P Z w'
    have hWr := realUniformWhittakerRegularity (t + 1) ds' a (J w') hWm
    obtain ⟨σ', hσ', -⟩ := realEqualPairConvergence (t + 1) D' a a (J w') (B v) φ hWr.1 hWr.2 hVreg.1 hVreg.2
    obtain ⟨N, Q, hQ⟩ := realEqualGodementPolynomial D D' a hAdj (P 0) cs fs List.length_ofFn hfs
      U hUm B hB v p φ hφ τ σ hJp (Z 0) hz hz0
    have hI : J w' ∈ S := by
      change realEqualIntegrand (J w') (B v) φ ∈ polynomialOrdinaryKernels D'.measure L[ds', es]
      rw [hList, hW]
      apply mem_polynomialOrdinaryKernels_of_normalization N Q hQ
      rw [hW] at hσ'
      exact ⟨σ', fun s hs => hσ' s hs⟩
    have hw' : w' = b • w := Subtype.ext hScale
    rw [hw', map_smul] at hI
    have hw := S.smul_mem b⁻¹ hI
    rw [smul_smul, inv_mul_cancel₀ hb, one_smul] at hw
    exact ⟨w, hw, rfl⟩
  have hspan := realGodementGaussianSpanning m μ c ds hc
  have hu : u.val ∈ T := (Submodule.span_le.mpr hgen) (by rw [hspan, ← hVeq]; exact u.2)
  obtain ⟨w, hw, he⟩ := hu
  exact (Subtype.ext he : w = u) ▸ hw

end Langlands.Global.RankinSelbergGlobal.RealGodement
