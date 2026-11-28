import Langlands.Analysis.Complex.PolynomialFiberContinuation
import Langlands.Global.RankinSelberg.RealAdjacentCanonical
import Langlands.Global.RankinSelberg.RealAdjacentPolynomialChamber
import Langlands.Global.RankinSelberg.RealUniformCanonicalRange

/-! # Polynomial normalization of real adjacent-rank ordinary tests -/

noncomputable section

open MeasureTheory Metric Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Analysis.PolynomialFiberContinuation (polynomialFiberContinuation)
open Langlands.GeneralDirichlet (eqOn_halfPlane)

/-- A jointly holomorphic normalized family on a parameter disk and a right half-plane has a
polynomial normalization at parameter one if its fibers have polynomial normalizations near zero. -/
theorem ordinaryPolynomialNormalization_at_one (σ : ℝ) (Z : ℂ × ℂ → ℂ) (L : ℂ → ReciprocalEntire)
    (hF : DifferentiableOn ℂ (fun u : ℂ × ℂ => (L u.1).denominator u.2 * Z u)
      (ball 0 3 ×ˢ {s : ℂ | σ < s.re}))
    (hL : ∀ z : ℂ, ∃ b : ℝ, ∀ s : ℂ, b < s.re → (L z).denominator s ≠ 0)
    (hInit : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ,
      ∃ (N : OrdinaryIntegralNormalization (fun s => Z (z, s)) (fun s => ((L z).denominator s)⁻¹))
        (P : Polynomial ℂ), N.value = P.eval) :
    ∃ (N : OrdinaryIntegralNormalization (fun s => Z (1, s)) (fun s => ((L 1).denominator s)⁻¹))
      (P : Polynomial ℂ), N.value = P.eval := by
  let U := ball (0 : ℂ) 3
  let F (z s : ℂ) := (L z).denominator s * Z (z, s)
  obtain ⟨δ, hδ, hInit⟩ := hInit
  let T := ball (0 : ℂ) (min δ 3)
  have hTU : T ⊆ U := ball_subset_ball (min_le_right _ _)
  have hParam (s : ℂ) (hs : σ < s.re) : DifferentiableOn ℂ (fun z => F z s) U :=
    hF.comp (differentiable_id.prodMk (differentiable_const s)).differentiableOn
      (fun z hz => ⟨hz, hs⟩)
  have hPoly (z : ℂ) (hz : z ∈ T) :
      ∃ P : Polynomial ℂ, ∀ s : ℂ, σ < s.re → F z s = P.eval s := by
    obtain ⟨N, P, he⟩ := hInit z (ball_subset_ball (min_le_left _ _) hz)
    obtain ⟨τ, hτ⟩ := N.eq_on_right
    obtain ⟨b, hb⟩ := hL z
    have hSpec : DifferentiableOn ℂ (F z) {s : ℂ | σ < s.re} :=
      hF.comp ((differentiable_const z).prodMk differentiable_id).differentiableOn
        (fun s hs => ⟨hTU hz, hs⟩)
    refine ⟨P, fun s hs => eqOn_halfPlane hSpec P.differentiable.differentiableOn
      (σ₁ := max τ b) (fun t ht => ?_) hs⟩
    have hne := hb t ((le_max_right _ _).trans_lt ht)
    have h := hτ t ((le_max_left _ _).trans_lt ht)
    rw [he] at h
    simp only [F, h, mul_left_comm ((L z).denominator t), mul_inv_cancel₀ hne, mul_one]
  obtain ⟨_, hR⟩ := polynomialFiberContinuation U T isOpen_ball (convex_ball _ _).isPreconnected
    isOpen_ball ⟨0, mem_ball_self (lt_min hδ (by norm_num))⟩ hTU σ F hParam hPoly
  have hOne : (1 : ℂ) ∈ U := by simp [U, Metric.mem_ball, dist_zero_right]
  obtain ⟨R, _, hR₁⟩ := hR 1 hOne
  obtain ⟨b, hb⟩ := hL 1
  refine ⟨⟨R.eval, fun s _ => R.differentiable.analyticAt s, ⟨max σ b, fun s hs => ?_⟩⟩, R, rfl⟩
  have hne := hb s ((le_max_right _ _).trans_lt hs)
  rw [← hR₁ s ((le_max_left _ _).trans_lt hs)]
  change Z (1, s) = ((L 1).denominator s * Z (1, s)) * ((L 1).denominator s)⁻¹
  rw [mul_comm ((L 1).denominator s) (Z (1, s)), mul_assoc, mul_inv_cancel₀ hne, mul_one]

namespace RealJacquet

open ArchimedeanLocal Langlands.Archimedean
open Langlands.Archimedean.GramFormula Langlands.Archimedean.PartialJacquet
open RealGodement RealGodementProfiles RealUnequalFamily
open RealBlockParameters (Shape blockList differentiable_pairDenominator)
open FunctionalEquationComparison.CompletedEquationAdapter (realPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationRealGLMeasurable archimedeanEquationRealGLBorel
  archimedeanEquationRealNMeasurable archimedeanEquationRealNBorel
  archimedeanEquationRealQMeasurable archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "m" => (r + 1 : ℕ)
local notation "n" => (r + 2 : ℕ)
local notation "H" => Langlands.GeneralLinear m ℝ
local notation "gap" => Nat.lt_succ_self r

private def HasCanonicalAdjacentPolynomial (D : RealQuotientMeasureData r) (a : ℝˣ)
    (P : Fin n → Fin 2) (Z : Fin n → ℂ) (es : List RealBlock) (V : H → ℂ) : Prop :=
  ∀ u : Automorphic.realStandardKFinite n (characterList P Z),
    realUnequalIntegrand gap (canonicalJacquetMap a P Z u) V ∈ polynomialOrdinaryKernels D.measure
      (fun s => ((realPairLFactor (characterList P Z) es).denominator s)⁻¹)

set_option maxHeartbeats 700000 in
private theorem canonicalAdjacentPolynomial_parameter (D : RealQuotientMeasureData r) (a : ℝˣ)
    (P : Fin n → Fin 2) (es : List RealBlock) (V : H → ℂ)
    (hV : V ∈ realUniformWhittakerModel r es a)
    (p : ℂ → Fin n → ℂ) (hp : Differentiable ℂ p)
    (hInit : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ, HasCanonicalAdjacentPolynomial D a P (p z) es V) :
    HasCanonicalAdjacentPolynomial D a P (p 1) es V := by
  intro u
  let φ := compactRestriction u.val
  have hφ : IsCompactProfile P φ := isCompactProfile_compactRestriction u.2
  let f (z : ℂ) : Automorphic.realStandardKFinite n (characterList P (p z)) :=
    ⟨standardSection (p z) φ, standardSection_mem hφ (p z)⟩
  let W (z : ℂ) := canonicalJacquetMap a P (p z) (f z)
  let Z (u : ℂ × ℂ) := realUnequalIntegral gap D (W u.1) V u.2
  let L (z : ℂ) := realPairLFactor (characterList P (p z)) es
  have hVreg := realUniformWhittakerRegularity r es a V hV
  have hFam := realUnequalCanonicalFamilyBounds gap (-a) a D P φ hφ p hp V
    (by simpa only [neg_neg] using hVreg.1) hVreg.2 3
  simp only [neg_neg] at hFam
  obtain ⟨σ, hConv, hZ, -⟩ := hFam
  let sh : Fin n → Shape := fun i => .inl (P i)
  let sh' : Fin es.length → Shape := fun i => blockShape es[i]
  let q : Fin es.length → ℂ := fun i => blockExponent es[i]
  have hes : es = blockList sh' q := eq_blockList es
  have hDen : Differentiable ℂ (fun u : ℂ × ℂ => (L u.1).denominator u.2) := by
    simp only [L, characterList_eq_blockList, hes]
    exact differentiable_pairDenominator sh sh' (p ∘ Prod.fst) (fun _ => q)
      (hp.comp differentiable_fst) (differentiable_const q) Prod.snd differentiable_snd
  have hF : DifferentiableOn ℂ (fun u : ℂ × ℂ => (L u.1).denominator u.2 * Z u)
      (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) := hDen.differentiableOn.mul hZ
  obtain ⟨N, R, hR⟩ := ordinaryPolynomialNormalization_at_one σ Z L hF
    (fun z => realPairLFactor_denominator_ne_zero (characterList P (p z)) es) (by
      obtain ⟨δ, hδ, hInit⟩ := hInit
      refine ⟨δ, hδ, fun z hz => ?_⟩
      exact exists_ordinaryPolynomialNormalization_of_mem (hInit z hz (f z)))
  have hOne : (1 : ℂ) ∈ ball (0 : ℂ) 3 := by simp [Metric.mem_ball, dist_zero_right]
  have hI : ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → Integrable (realUnequalIntegrand gap (W 1) V s) D.measure :=
    ⟨σ, fun s hs => (hConv 1 hOne s hs).1⟩
  have hN := mem_polynomialOrdinaryKernels_of_normalization N R hR hI
  have hf : f 1 = u := Subtype.ext (standardSection_compactRestriction u.2)
  change realUnequalIntegrand gap (W 1) V ∈ _ at hN
  change realUnequalIntegrand gap (canonicalJacquetMap a P (p 1) (f 1)) V ∈ _ at hN
  rwa [hf] at hN

private theorem canonicalAdjacentPolynomial (D : RealQuotientMeasureData r) (a : ℝˣ)
    (ha : |(a : ℝ)| = 1) (hEqual : RealEqualPolynomialAtRank r (-a))
    (P : Fin n → Fin 2) (fs : List RealCharacterData) (hfs : fs.length = m)
    (B : Automorphic.realStandardKFinite m (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ))
    (hB : IsRealUniformWhittakerIntertwiner r (fs.map RealBlock.character) a B)
    (v : Automorphic.realStandardKFinite m (fs.map RealBlock.character)) :
    ∀ Z, HasCanonicalAdjacentPolynomial D a P Z (fs.map RealBlock.character) (B v) := by
  have hV : B v ∈ realUniformWhittakerModel r (fs.map RealBlock.character) a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)
  apply realChamberRemoval
  · exact canonicalAdjacentPolynomial_parameter D a P _ (B v) hV
  · intro q
    let e (i : Fin m) := (m : ℝ) + normExponent (realPositionExponent (characterList (Fin.tail P) q)) m i -
      ((m : ℝ) + 1) / 2
    obtain ⟨M, hM⟩ := (finite_range e).bddAbove
    refine ⟨M, fun Z hZq hZ hMZ => ?_⟩
    have hc (i : Fin m) : (m : ℝ) + normExponent (realPositionExponent
        (characterList (Fin.tail P) (Fin.tail Z))) m i ≤
        (Langlands.Archimedean.RealJacquetFrobenius.charData (P 0) (Z 0)).exponent.re + ((m : ℝ) + 1) / 2 := by
      have hi := (hM (mem_range_self i)).trans hMZ
      rw [hZq]
      change _ ≤ (Z 0).re + _
      dsimp only [e] at hi
      linarith
    exact realAdjacentPolynomialChamber D a ha hEqual P Z hZ hc fs hfs B hB v

/-- At either unit real additive scale, the equal-rank polynomial conclusion for standard
Gaussian rows implies the ordinary adjacent-rank polynomial conclusion for character lists. -/
def RealOrdinaryAdjacentPolynomialStatement : Prop :=
  ∀ (r : ℕ) (a : ℝˣ), |(a : ℝ)| = 1 → RealEqualPolynomialAtRank r a → RealAdjacentPolynomialAtRank r a

set_option maxHeartbeats 1100000 in
theorem realOrdinaryAdjacentPolynomial : RealOrdinaryAdjacentPolynomialStatement := by
  intro r a ha hEqual cs fs hcs hfs D
  dsimp only
  rintro ⟨W, V⟩
  let ds := cs.map RealBlock.character
  let es := fs.map RealBlock.character
  have hd : realRank ds = r + 2 := (realRank_map_character cs).trans hcs
  have he : realRank es = r + 1 := (realRank_map_character fs).trans hfs
  obtain ⟨P, Z, hds⟩ := RealPrincipalSeries.exists_characterList_of_map_character cs hd
  obtain ⟨p, z, hes⟩ := RealPrincipalSeries.exists_characterList_of_map_character fs he
  have hW : W.val ∈ realUniformWhittakerModel (r + 1) (characterList P Z) (-(-a)) := by
    rw [neg_neg, ← hds, ← realWhittakerModels_eq (r + 1) ds hd]
    exact W.2
  have hV : V.val ∈ realUniformWhittakerModel r (characterList p z) (-a) := by
    rw [← hes, ← realWhittakerModels_eq r es he]
    exact V.2
  obtain ⟨u, hu⟩ := RealUniformCanonicalRange.uniformWhittakerModel_le_range (r + 1) (-a) P Z hW
  obtain ⟨v, hv⟩ := RealUniformCanonicalRange.uniformWhittakerModel_le_range r a p z hV
  have hB : ∃ B : Automorphic.realStandardKFinite (r + 1) (characterList p z) →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ),
      IsRealUniformWhittakerIntertwiner r (characterList p z) (-a) B ∧ ∃ v, B v = V.val :=
    ⟨canonicalJacquetMap a p z, realGodementCanonicalModel r a p z, v, hv⟩
  rw [← hes] at hB
  obtain ⟨B, hB, v', hv'⟩ := hB
  have hK := canonicalAdjacentPolynomial D (-a) (by simpa only [Units.val_neg, abs_neg] using ha)
    (by simpa only [neg_neg] using hEqual) P fs hfs B hB v' Z u
  rw [hu, hv', ← hds] at hK
  exact exists_ordinaryPolynomialNormalization_of_mem hK

end RealJacquet
end Langlands.Global.RankinSelbergGlobal
