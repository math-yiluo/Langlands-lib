import Langlands.Global.RankinSelberg.RealEqualPolynomialChamber
import Langlands.Global.RankinSelberg.RealOrdinaryAdjacentPolynomial

/-! # Polynomial normalization of real ordinary character-list tests -/

noncomputable section

open MeasureTheory Metric Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal Langlands.Archimedean Langlands.LocalFactor.Archimedean
open RealGodementProfiles RealUnequalFamily
open RealBlockParameters (Shape blockList differentiable_pairDenominator)
open RealLocalWhittaker (regularFunctions)
open RealJacquet (realChamberRemoval realOrdinaryAdjacentPolynomial IsRealCharacterList)
open RealEqualPolynomialGeneration (IsGaussianPolynomialRow)
open FunctionalEquationComparison.CompletedEquationAdapter (realPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationRealGLMeasurable archimedeanEquationRealGLBorel
  archimedeanEquationRealNMeasurable archimedeanEquationRealNBorel
  archimedeanEquationRealQMeasurable archimedeanEquationRealQBorel

variable {t : ℕ}
local notation "n" => (t + 2 : ℕ)
local notation "H" => Langlands.GeneralLinear n ℝ
local notation "Row" => Fin n → ℝ

set_option maxHeartbeats 950000 in
private theorem canonicalEqualPolynomial_parameter (D : RealQuotientMeasureData (t + 1))
    (a : ℝˣ) (P : Fin n → Fin 2) (es : List RealBlock) (V : H → ℂ)
    (hV : V ∈ realUniformWhittakerModel (t + 1) es (-a)) (φ : 𝓢(Row, ℂ))
    (p : ℂ → Fin n → ℂ) (hp : Differentiable ℂ p)
    (hInit : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ, HasCanonicalEqualPolynomial D a P (p z) es V φ) :
    HasCanonicalEqualPolynomial D a P (p 1) es V φ := by
  intro u
  let ψ := compactRestriction u.val
  have hψ : IsCompactProfile P ψ := isCompactProfile_compactRestriction u.2
  let f (z : ℂ) : Automorphic.realStandardKFinite n (characterList P (p z)) :=
    ⟨standardSection (p z) ψ, standardSection_mem hψ (p z)⟩
  let J := canonicalJacquetFamily (-a) hψ
  let W (z : ℂ) := J (p z)
  have hMap (z : ℂ) : canonicalJacquetMap (-a) P (p z) (f z) = W z :=
    canonicalJacquetMap_standardSection (-a) hψ (p z)
  have hJ := canonicalJacquetFamily_properties (-a) hψ
  have hReg (z : Fin n → ℂ) (Xs) : RealLocalWhittaker.iteratedRightDerivative (t + 1) Xs (J z) ∈
      regularFunctions (t + 1) a := by
    simpa only [neg_neg] using hJ.1 z Xs
  let S : Set (ℂ × ℂ) := ball 0 3 ×ˢ univ
  let T := p '' closedBall (0 : ℂ) 3
  have hT : IsCompact T := (isCompact_closedBall _ _).image hp.continuous
  obtain ⟨N, hN⟩ := exists_uniform_derivativeGrowth hJ.2.1 hT (subset_univ T)
  have hG : HasUniformGauge S (fun x : ℂ × ℂ => W x.1) :=
    (hasUniformGauge_of_derivativeGrowth T J (fun z _ Xs => hReg z Xs) hN).comp
      (p ∘ Prod.fst) (fun x hx => mem_image_of_mem _ (ball_subset_closedBall hx.1))
  have hVr := realUniformWhittakerRegularity (t + 1) es (-a) V hV
  have hVg := RealWhittakerGauge.exists_gauge_bound hVr.1 hVr.2
  obtain ⟨σ, hConv, hZ⟩ := realLocalEqualFamily a D S (fun x : ℂ × ℂ => W x.1) (fun _ => V) Prod.snd φ
    (isOpen_ball.prod isOpen_univ) differentiable_snd (fun x => (hReg (p x.1) []).1)
    (fun _ => (hVr.1 []).1) (fun x => (hReg (p x.1) []).2.1.continuous)
    (fun _ => (hVr.1 []).2.1.continuous)
    (fun g => ((hJ.2.2.1 [] g).comp (hp.comp differentiable_fst)).differentiableOn)
    (fun g => differentiableOn_const (V g)) hG (hasUniformGauge_const S hVg)
  let Z (x : ℂ × ℂ) := realEqualIntegral D (W x.1) V φ x.2
  let L (z : ℂ) := realPairLFactor (characterList P (p z)) es
  let sh : Fin n → Shape := fun i => .inl (P i)
  let sh' : Fin es.length → Shape := fun i => blockShape es[i]
  let q : Fin es.length → ℂ := fun i => blockExponent es[i]
  have hes : es = blockList sh' q := eq_blockList es
  have hDen : Differentiable ℂ (fun x : ℂ × ℂ => (L x.1).denominator x.2) := by
    simp only [L, characterList_eq_blockList, hes]
    exact differentiable_pairDenominator sh sh' (p ∘ Prod.fst) (fun _ => q)
      (hp.comp differentiable_fst) (differentiable_const q) Prod.snd differentiable_snd
  have hF : DifferentiableOn ℂ (fun x : ℂ × ℂ => (L x.1).denominator x.2 * Z x)
      (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) :=
    hDen.differentiableOn.mul (hZ.mono fun x hx => ⟨⟨hx.1, mem_univ x.2⟩, hx.2⟩)
  obtain ⟨A, R, hR⟩ := ordinaryPolynomialNormalization_at_one σ Z L hF
    (fun z => realPairLFactor_denominator_ne_zero (characterList P (p z)) es) (by
      obtain ⟨δ, hδ, hInit⟩ := hInit
      refine ⟨δ, hδ, fun z hz => ?_⟩
      have hz' := hInit z hz (f z)
      rw [hMap z] at hz'
      exact exists_ordinaryPolynomialNormalization_of_mem hz')
  have hOne : (1 : ℂ) ∈ ball (0 : ℂ) 3 := by simp [Metric.mem_ball, dist_zero_right]
  have hI : ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → Integrable (realEqualIntegrand (W 1) V φ s) D.measure :=
    ⟨σ, fun s hs => hConv (1, s) ⟨⟨hOne, mem_univ s⟩, hs⟩⟩
  have hN := mem_polynomialOrdinaryKernels_of_normalization A R hR hI
  have hf : f 1 = u := Subtype.ext (standardSection_compactRestriction u.2)
  change realEqualIntegrand (W 1) V φ ∈ _ at hN
  rwa [← hMap 1, hf] at hN

/-- Polynomial normalization of the smaller ordinary adjacent tests at the opposite
additive parameter gives polynomial normalization of the next equal-rank Gaussian row tests. -/
def RealOrdinaryEqualPolynomialStepStatement : Prop :=
  ∀ (t : ℕ) (a : ℝˣ), RealAdjacentPolynomialAtRank t (-a) → RealEqualPolynomialAtRank (t + 1) a

set_option maxHeartbeats 1000000 in
theorem realOrdinaryEqualPolynomialStep : RealOrdinaryEqualPolynomialStepStatement := by
  intro r a hAdj cs fs hcs hfs D
  dsimp only
  rintro ⟨W, V, φ⟩
  let ds := cs.map RealBlock.character
  let es := fs.map RealBlock.character
  have hd : realRank ds = r + 2 := (realRank_map_character cs).trans hcs
  have he : realRank es = r + 2 := (realRank_map_character fs).trans hfs
  obtain ⟨P, Z, hds⟩ := RealPrincipalSeries.exists_characterList_of_map_character cs hd
  obtain ⟨p, z, hes⟩ := RealPrincipalSeries.exists_characterList_of_map_character fs he
  have hW : W.val ∈ realUniformWhittakerModel (r + 1) (characterList P Z) (-(-a)) := by
    rw [neg_neg, ← hds, ← realWhittakerModels_eq (r + 1) ds hd]
    exact W.2
  have hV : V.val ∈ realUniformWhittakerModel (r + 1) (characterList p z) (-a) := by
    rw [← hes, ← realWhittakerModels_eq (r + 1) es he]
    exact V.2
  obtain ⟨u, hu⟩ := RealUniformCanonicalRange.uniformWhittakerModel_le_range (r + 1) (-a) P Z hW
  obtain ⟨v, hv⟩ := RealUniformCanonicalRange.uniformWhittakerModel_le_range (r + 1) a p z hV
  have hB : ∃ B : Automorphic.realStandardKFinite (r + 2) (characterList p z) →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 2) ℝ → ℂ),
      IsRealUniformWhittakerIntertwiner (r + 1) (characterList p z) (-a) B ∧ ∃ v, B v = V.val :=
    ⟨canonicalJacquetMap a p z, realGodementCanonicalModel (r + 1) a p z, v, hv⟩
  rw [← hes] at hB
  obtain ⟨B, hB, v', hv'⟩ := hB
  have hBV : B v' ∈ realUniformWhittakerModel (r + 1) es (-a) :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v', rfl⟩)
  have hAll : ∀ Z₀, HasCanonicalEqualPolynomial D a P Z₀ es (B v') φ.val := by
    apply realChamberRemoval
    · exact canonicalEqualPolynomial_parameter D a P es (B v') hBV φ.val
    · exact realEqualPolynomialChamber D a hAdj P fs hfs B hB v' φ.val φ.2
  have hK := hAll Z u
  rw [hu, hv', ← hds] at hK
  exact exists_ordinaryPolynomialNormalization_of_mem hK

/-- Ordinary real integrals for character lists have polynomial normalization at the two
standard additive scales, for adjacent ranks and for equal ranks with standard Gaussian rows. -/
def RealCharacterOrdinaryPolynomialStatement : Prop :=
  RealOrdinaryPolynomialStatement IsRealCharacterList

theorem realCharacterOrdinaryPolynomial : RealCharacterOrdinaryPolynomialStatement := by
  have hEqual (r : ℕ) : ∀ (a : ℝˣ), |(a : ℝ)| = 1 → RealEqualPolynomialAtRank r a := by
    induction r with
    | zero => exact fun a _ => RealRankZero.realRankOnePolynomial a
    | succ r ih =>
      intro a ha
      have hn : |((-a : ℝˣ) : ℝ)| = 1 := by simpa only [Units.val_neg, abs_neg] using ha
      exact realOrdinaryEqualPolynomialStep r a (realOrdinaryAdjacentPolynomial r (-a) hn (ih (-a) hn))
  have hUnit (a : ℝˣ) (ha : a = 1 ∨ a = -1) : |(a : ℝ)| = 1 := by
    rcases ha with rfl | rfl <;> simp
  constructor
  · intro r ds es hd he hr ht a ha D
    obtain ⟨cs, rfl⟩ := hd
    obtain ⟨fs, rfl⟩ := he
    rw [realRank_map_character] at hr ht
    exact realOrdinaryAdjacentPolynomial r a (hUnit a ha) (hEqual r a (hUnit a ha)) cs fs hr ht D
  · intro r ds es hd he hr ht a ha D
    obtain ⟨cs, rfl⟩ := hd
    obtain ⟨fs, rfl⟩ := he
    rw [realRank_map_character] at hr ht
    exact hEqual r a (hUnit a ha) cs fs hr ht D

end Langlands.Global.RankinSelbergGlobal.RealGodement
