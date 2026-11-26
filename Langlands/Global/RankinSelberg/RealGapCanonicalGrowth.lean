import Langlands.Global.RankinSelberg.RealGapMonomialGrowth
import Langlands.Global.RankinSelberg.RealGapGrowthSubmodule
import Langlands.Global.RankinSelberg.RealGapCanonicalSpan
import Langlands.Global.RankinSelberg.RealAdjacentCanonical
import Langlands.Global.RankinSelberg.RealUniformCanonicalRange

/-! # The real normalized larger-gap equation for every inducing parameter -/

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal SchwartzMap Matrix.Norms.Operator
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapCanonicalGrowth

open ArchimedeanLocal
open Langlands.Archimedean
open Langlands.Archimedean.GramFormula Langlands.Archimedean.PartialJacquet
open Langlands.GeneralLinear (blockSum)
open RealGodement (canonicalJacquetMap realSpectralChamber hasRealPairNormalizedGrowth_scale_congr
  realGodementCanonicalModel)
open RealUnequalFamily (HasRealUnequalCanonicalPairGrowth realUnequalCanonicalGrowthReflection)
open RealJacquet (HasRealPairNormalizedGrowth RealLocalUnequalCharacterGrowthAtRanks realChamberRemoval
  determinant_characterList_neg_one characterList_succ)
open RealGapCanonicalSpan (monomialSplitGenerators canonicalJacquetMap_mem_span_monomialSplitGenerators)
open RealGapGrowthSubmodule (unequalGrowthSubmodule translate_mem_model)
open RealGapMonomialGrowth (realGapMonomialGrowth)
open RealGapExactRestriction (rotatedValue)
open RealGapGaussianFactors (gaussianFactors)
open RealGapRankCoordinates (rankLT tailWeyl_mul_self)
open RealGapWeylRestriction (tailWeyl)
open RealGodementGaussianPolynomial (Coordinates gaussianPolynomial)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

local notation "Std" => Langlands.Automorphic.realStandardKFinite

private theorem blockSum_mem_unitary {a b : ℕ} {u : Langlands.GeneralLinear a ℝ}
    {v : Langlands.GeneralLinear b ℝ} (hu : u ∈ unitaryCompact ℝ a) (hv : v ∈ unitaryCompact ℝ b) :
    blockSum (u, v) ∈ unitaryCompact ℝ (a + b) := by
  have hu' := Matrix.mem_unitaryGroup_iff'.mp hu
  have hv' := Matrix.mem_unitaryGroup_iff'.mp hv
  change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u.val 0 0 v.val) ∈
    Matrix.unitaryGroup (Fin (a + b)) ℝ
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
    Matrix.fromBlocks_conjTranspose, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, hu', hv']
  simp

private theorem mem_model {r : ℕ} {ds : List RealBlock} {a : ℝˣ}
    {B : Std (r + 1) ds →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℝ → ℂ)}
    (hB : IsRealUniformWhittakerIntertwiner r ds a B)
    (v : Std (r + 1) ds) : B v ∈ realUniformWhittakerModel r ds a :=
  Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)

variable (t q : ℕ)

/-- The tail reversal is orthogonal. -/
theorem tailWeyl_mem_unitary : tailWeyl (t + 1) (q + 2) ∈ unitaryCompact ℝ (t + 1 + (q + 2)) :=
  blockSum_mem_unitary (unitaryCompact ℝ (t + 1)).one_mem
    (RealUnequalPairConvergence.weylLong_mem_unitary' (q + 2))

/-- The tail-reversed split Godement coefficient of a Gaussian monomial is the rotated value of the
split column factors. -/
theorem translate_godementCoefficient (a : ℝˣ) (D' : RealQuotientMeasureData (t + 1 + q))
    (c : RealCharacterData) (d : Coordinates (t + 1 + q + 1) (t + 1 + q + 1) →₀ ℕ) (c₀ : ℂ)
    (φ : 𝓢(Fin (t + 1 + q + 1) → ℝ, ℂ)) (U : Langlands.GeneralLinear (t + 1 + q + 1) ℝ → ℂ) :
    ArchimedeanLocal.translateFunction (tailWeyl (t + 1) (q + 2))
        (RealJacquet.realAdjacentGodementCoefficient D' a
          (RealJacquet.realColumnProduct (gaussianPolynomial (MvPolynomial.monomial d c₀)) φ) U c) =
      rotatedValue t q a D' c (gaussianPolynomial (MvPolynomial.monomial d c₀))
        (gaussianFactors (t + 1) q d c₀ φ) U := by
  have hφ : (gaussianFactors (t + 1) q d c₀ φ).tail (Fin.last (q + 1)) = φ := by
    simp only [gaussianFactors, Fin.lastCases_last]
  unfold rotatedValue
  rw [hφ]

set_option maxHeartbeats 4000000 in
/-- In the Godement convergence region of a strict chamber, the canonical values of the larger
rank satisfy the normalized larger-gap equation against every value of a smaller uniform map,
given the normalized equation at the smaller gap. -/
theorem realGapChamberGrowth
    (hLower : RealLocalUnequalCharacterGrowthAtRanks (t + 1 + q) t (rankLT t q))
    (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1 + q)) (a : ℝˣ)
    (P : Fin (t + 1 + q + 2) → Fin 2) (Z : Fin (t + 1 + q + 2) → ℂ)
    (hZ : Z ∈ realSpectralChamber (t + 1 + q + 1))
    (hc : ∀ i : Fin (t + 1 + q + 1), ((t + 1 + q + 1 : ℕ) : ℝ) + normExponent (realPositionExponent
        (RealGodementProfiles.characterList (Fin.tail P) (Fin.tail Z))) (t + 1 + q + 1) i ≤
      (RealJacquetFrobenius.charData (P 0) (Z 0)).exponent.re + (((t + 1 + q + 1 : ℕ) : ℝ) + 1) / 2)
    (fs : List RealCharacterData) (hfs : fs.length = t + 1)
    (B : Std (t + 1) (fs.map RealBlock.character) →ₗ[ℂ] (Langlands.GeneralLinear (t + 1) ℝ → ℂ))
    (hB : IsRealUniformWhittakerIntertwiner t (fs.map RealBlock.character) a B)
    (v : Std (t + 1) (fs.map RealBlock.character))
    (F : Std (t + 1 + q + 2) (RealGodementProfiles.characterList P Z)) :
    canonicalJacquetMap a P Z F ∈ unequalGrowthSubmodule (rankLT t (q + 1)) D (-a) (B v)
      (RealGodementProfiles.characterList P Z) (fs.map RealBlock.character)
      ((RealGodementProfiles.characterList P Z).map RealLocalJacquet.dualBlock)
      ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) a
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((RealJacquet.determinant (RealGodementProfiles.characterList P Z) (-1) : ℂ) ^ (t + 1) *
        (RealJacquet.determinant (fs.map RealBlock.character) (-1) : ℂ)) := by
  classical
  let w : Langlands.GeneralLinear (t + 1 + q + 2) ℝ := tailWeyl (t + 1) (q + 2)
  have hw : w ∈ unitaryCompact ℝ (t + 1 + q + 2) := tailWeyl_mem_unitary t q
  let J := canonicalJacquetMap a P Z
  have hJ := realGodementCanonicalModel (t + 1 + q + 1) a P Z
  let T := Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (t + 1 + q + 2) ℝ) w
  let F' : Std (t + 1 + q + 2) (RealGodementProfiles.characterList P Z) :=
    ⟨T F.val, rightTranslation_mem_kFiniteFunctions_realStandardModule _ _ F.2 hw⟩
  have hJF' : J F' = T (J F) := hJ.1.2.2.2.1 ⟨w, hw⟩ F F' rfl
  have hJF : J F = T (J F') := by
    rw [hJF']
    funext g
    change J F g = J F (g * w * w)
    rw [mul_assoc, tailWeyl_mul_self, mul_one]
  let S := unequalGrowthSubmodule (rankLT t (q + 1)) D (-a) (B v)
    (RealGodementProfiles.characterList P Z) (fs.map RealBlock.character)
    ((RealGodementProfiles.characterList P Z).map RealLocalJacquet.dualBlock)
    ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) a
    (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
    ((RealJacquet.determinant (RealGodementProfiles.characterList P Z) (-1) : ℂ) ^ (t + 1) *
      (RealJacquet.determinant (fs.map RealBlock.character) (-1) : ℂ))
  have hgen : monomialSplitGenerators D' a P Z ⊆ S.comap T := by
    rintro _ ⟨hWmodel, f₀, d, c₀, φ, rfl⟩
    let c := RealJacquetFrobenius.charData (P 0) (Z 0)
    let cs : List RealCharacterData :=
      List.ofFn fun i => RealJacquetFrobenius.charData (Fin.tail P i) (Fin.tail Z i)
    have hcs : cs.length = t + 1 + q + 1 := List.length_ofFn
    let A := canonicalJacquetMap a (Fin.tail P) (Fin.tail Z)
    have hA : IsRealUniformWhittakerIntertwiner (t + 1 + q) (cs.map RealBlock.character) (-a) A :=
      realGodementCanonicalModel (t + 1 + q) a (Fin.tail P) (Fin.tail Z)
    have hGrowth := realGapMonomialGrowth t q hLower cs fs hcs hfs a D D' c A hA f₀ d c₀ φ B hB v
    have hrot := translate_godementCoefficient t q a D' c d c₀ φ (A f₀)
    change T (RealJacquet.realAdjacentGodementCoefficient D' a
      (RealJacquet.realColumnProduct (gaussianPolynomial (MvPolynomial.monomial d c₀)) φ) (A f₀) c) ∈ S
    have hrot' : T (RealJacquet.realAdjacentGodementCoefficient D' a
        (RealJacquet.realColumnProduct (gaussianPolynomial (MvPolynomial.monomial d c₀)) φ) (A f₀) c) =
        rotatedValue t q a D' c (gaussianPolynomial (MvPolynomial.monomial d c₀))
          (gaussianFactors (t + 1) q d c₀ φ) (A f₀) := hrot
    have hWm := translate_mem_model hWmodel hw
    rw [hrot']
    have hWm' : rotatedValue t q a D' c (gaussianPolynomial (MvPolynomial.monomial d c₀))
        (gaussianFactors (t + 1) q d c₀ φ) (A f₀) ∈
        realUniformWhittakerModel (t + 1 + q + 1) (RealGodementProfiles.characterList P Z) (-a) := by
      rw [← hrot']
      exact hWm
    have hV : B v ∈ realUniformWhittakerModel t (fs.map RealBlock.character) a := mem_model hB v
    have hWreg := realUniformWhittakerRegularity (t + 1 + q + 1) _ (-a) _ hWm'
    have hVreg := realUniformWhittakerRegularity t _ a (B v) hV
    obtain ⟨σ, h₁, h₂, -, -⟩ := realUnequalPairConvergence (t + 1 + q + 1) t (rankLT t (q + 1)) D (-a)
      _ (B v) hWreg.1 hWreg.2 (by rw [neg_neg]; exact hVreg.1) hVreg.2
    refine ⟨σ, fun s hs => ⟨h₁ s hs, h₂ s hs⟩, ?_⟩
    rw [characterList_succ P Z]
    exact hGrowth
  have hspan := canonicalJacquetMap_mem_span_monomialSplitGenerators D' a P Z hZ hc F'
  change J F ∈ S
  rw [hJF]
  exact (Submodule.span_le.mpr hgen) hspan

/-- For every inducing parameter, every larger canonical value satisfies the normalized
larger-gap equation with strip growth against every value of a smaller uniform map, given the
normalized equation at the smaller gap. -/
theorem realGapCanonicalGrowth
    (hLower : RealLocalUnequalCharacterGrowthAtRanks (t + 1 + q) t (rankLT t q))
    (D : RealQuotientMeasureData t) (a : ℝˣ) (P : Fin (t + 1 + q + 2) → Fin 2)
    (fs : List RealCharacterData) (hfs : fs.length = t + 1)
    (B : Std (t + 1) (fs.map RealBlock.character) →ₗ[ℂ] (Langlands.GeneralLinear (t + 1) ℝ → ℂ))
    (hB : IsRealUniformWhittakerIntertwiner t (fs.map RealBlock.character) (-a) B)
    (v : Std (t + 1) (fs.map RealBlock.character)) (Z : Fin (t + 1 + q + 2) → ℂ) :
    HasRealUnequalCanonicalPairGrowth (rankLT t (q + 1)) a a (-a) D P Z (fs.map RealBlock.character)
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((RealJacquet.determinant (RealGodementProfiles.characterList P 0) (-1) : ℂ) ^ (t + 1) *
        (RealJacquet.determinant (fs.map RealBlock.character) (-1) : ℂ)) (B v) := by
  have hV : B v ∈ realUniformWhittakerModel t (fs.map RealBlock.character) (-a) := mem_model hB v
  have hVreg := realUniformWhittakerRegularity t _ (-a) (B v) hV
  have hsign : ((RealJacquet.determinant (RealGodementProfiles.characterList P 0) (-1) : ℂ) ^ (t + 1) *
      (RealJacquet.determinant (fs.map RealBlock.character) (-1) : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (Units.ne_zero _)
  revert Z
  refine realChamberRemoval (n := t + 1 + q) (fun Z => HasRealUnequalCanonicalPairGrowth (rankLT t (q + 1))
    a a (-a) D P Z (fs.map RealBlock.character) (NNReal.sqrt ‖(a : ℝ)‖₊)
    (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
    ((RealJacquet.determinant (RealGodementProfiles.characterList P 0) (-1) : ℂ) ^ (t + 1) *
      (RealJacquet.determinant (fs.map RealBlock.character) (-1) : ℂ)) (B v)) ?_ ?_
  · exact realUnequalCanonicalGrowthReflection (rankLT t (q + 1)) a a (-a) D P _ _ _ _ hsign (B v)
      hVreg.1 hVreg.2
  · intro q'
    let ex (i : Fin (t + 1 + q + 1)) : ℝ := ((t + 1 + q + 1 : ℕ) : ℝ) + normExponent (realPositionExponent
      (RealGodementProfiles.characterList (Fin.tail P) q')) (t + 1 + q + 1) i -
        (((t + 1 + q + 1 : ℕ) : ℝ) + 1) / 2
    obtain ⟨M, hM⟩ := (Set.finite_range ex).bddAbove
    refine ⟨M, fun Z hZq hZ hMZ => ?_⟩
    intro f
    have hc : ∀ i : Fin (t + 1 + q + 1), ((t + 1 + q + 1 : ℕ) : ℝ) + normExponent (realPositionExponent
        (RealGodementProfiles.characterList (Fin.tail P) (Fin.tail Z))) (t + 1 + q + 1) i ≤
        (RealJacquetFrobenius.charData (P 0) (Z 0)).exponent.re +
          (((t + 1 + q + 1 : ℕ) : ℝ) + 1) / 2 := by
      intro i
      have hi := (hM (Set.mem_range_self i)).trans hMZ
      rw [hZq]
      change _ ≤ (Z 0).re + _
      simp only [ex] at hi
      linarith
    obtain ⟨-, -, h⟩ := realGapChamberGrowth t q hLower D (realQuotientMeasureData (t + 1 + q)) (-a) P Z
      hZ hc fs hfs B hB v f
    rw [neg_neg, determinant_characterList_neg_one P Z 0] at h
    have hscale : NNReal.sqrt ‖((-a : ℝˣ) : ℝ)‖₊ = NNReal.sqrt ‖(a : ℝ)‖₊ := by
      rw [Units.val_neg, nnnorm_neg]
    exact hasRealPairNormalizedGrowth_scale_congr hscale h

/-- The larger-gap step: the normalized unequal-rank equation for character lists at ranks
`t + 1 + q` and `t` gives it at ranks `t + 1 + q + 1` and `t`. -/
def RealGapGrowthStepStatement : Prop :=
  RealLocalUnequalCharacterGrowthAtRanks (t + 1 + q) t (rankLT t q) →
    RealLocalUnequalCharacterGrowthAtRanks (t + 1 + q + 1) t (rankLT t (q + 1))

theorem realGapGrowthStep : RealGapGrowthStepStatement t q := by
  intro hLower ds es hds hes hrd hre a D W W' hW hW'
  obtain ⟨cs, rfl⟩ := hds
  obtain ⟨fs₀, rfl⟩ := hes
  have hcs : cs.length = t + 1 + q + 2 := by rw [← realRank_map_character]; exact hrd
  have hfs₀ : fs₀.length = t + 1 := by rw [← realRank_map_character]; exact hre
  obtain ⟨P, Zs, hPZ⟩ := RealGodement.exists_characterList_eq cs hcs
  obtain ⟨P', Zs', hPZ'⟩ := RealGodement.exists_characterList_eq fs₀ hfs₀
  rw [← hPZ] at hW ⊢
  rw [← hPZ'] at hW' ⊢
  obtain ⟨F, rfl⟩ := RealUniformCanonicalRange.realUniformCanonicalRangePremise (t + 1 + q + 1) (-a) P Zs
    (by rwa [neg_neg])
  obtain ⟨F', rfl⟩ := RealUniformCanonicalRange.realUniformCanonicalRangePremise t a P' Zs' hW'
  let fs : List RealCharacterData := List.ofFn fun i => RealJacquetFrobenius.charData (P' i) (Zs' i)
  have hfs : fs.length = t + 1 := List.length_ofFn
  have hB := realGodementCanonicalModel t a P' Zs'
  have h := realGapCanonicalGrowth t q hLower D a P fs hfs (canonicalJacquetMap a P' Zs') hB F' Zs F
  rw [← determinant_characterList_neg_one P Zs 0] at h
  exact h

end Langlands.Global.RankinSelbergGlobal.RealGapCanonicalGrowth
